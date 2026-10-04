#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Host tests may count logical operations; normal builds emit no hooks. */
#ifndef MY_SOLVER_COUNT
#define MY_SOLVER_COUNT(field) ((void) 0)
#endif

/* Optimal HTM IDA*: R/B/D generators, max(hp,ho), same-face pruning.
 * Persistent tables: 30240 + 4374 + 2520 + 365 = 37499 bytes.
 * Initialization scratch: 5769 distance bytes and a 10080-byte queue.
 * Validation and the full-state BFS oracle live in my_solver_test.c.
 */
enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9,
    MAX_DEPTH = 11,
    NONE = 3,
    FOUND = -1
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/* Search coordinates: p < PERMUTATIONS and o < ORIENTATIONS. */
typedef struct {
    uint16_t p, o;
} ranked_state_t;

/* Only quarter turns are stored; half/inverse turns repeat lookups. */
static uint16_t perm_transition[3][PERMUTATIONS];
static uint16_t ori_transition[3][ORIENTATIONS];
static uint8_t hp_packed[(PERMUTATIONS + 1) / 2];
static uint8_t ho_packed[(ORIENTATIONS + 1) / 2];

static const char *const move_names[MOVES] = {
    "R", "R2", "R'", "B", "B2", "B'", "D", "D2", "D'"
};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < (unsigned) CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

static int valid(const state_t *state)
{
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}

static ranked_state_t rank_coordinates(const state_t *state)
{
    uint32_t rank = rank_state(state);
    ranked_state_t coordinates = {(uint16_t) (rank / ORIENTATIONS),
                                  (uint16_t) (rank % ORIENTATIONS)};
    return coordinates;
}

static void build_transitions(void)
{
    state_t state;
    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        unrank_state((uint32_t) p * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            perm_transition[face][p] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        unrank_state(o, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            ori_transition[face][o] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
}

/* BFS from zero gives exact abstract HTM distances. */
static int build_distances(uint16_t count, uint16_t transition[3][count],
                           uint8_t *distance)
{
    uint16_t queue[PERMUTATIONS];
    uint16_t head = 0, tail = 1;
    memset(distance, UINT8_MAX, count);
    queue[0] = 0;
    distance[0] = 0;
    while (head < tail) {
        uint16_t here = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = transition[face][next];
                if (distance[next] == UINT8_MAX) {
                    distance[next] = (uint8_t) (distance[here] + 1U);
                    queue[tail++] = next;
                }
            }
        }
    }
    return tail == count;
}

/* Even indices use the low nibble; odd indices use the high nibble. */
static uint8_t packed_get(const uint8_t *table, uint16_t index)
{
    unsigned shift = (index & 1U) * 4U;
    return (uint8_t) ((table[index / 2U] >> shift) & 0xFU);
}

static void packed_set(uint8_t *table, uint16_t index, uint8_t value)
{
    unsigned shift = (index & 1U) * 4U;
    uint8_t mask = (uint8_t) (0xFU << shift);
    table[index / 2U] = (uint8_t) ((table[index / 2U] & (uint8_t) ~mask) |
                                  ((unsigned) value << shift));
}

static int pack_distances(const uint8_t *distance, uint8_t *packed,
                          uint16_t count)
{
    memset(packed, 0, (count + 1U) / 2U);
    for (uint16_t i = 0; i < count; ++i) {
        if (distance[i] > 15) {
            fprintf(stderr, "heuristic does not fit in 4 bits: index=%u value=%u\n",
                    (unsigned) i, (unsigned) distance[i]);
            return 0;
        }
        packed_set(packed, i, distance[i]);
    }
    return 1;
}

static int initialize_tables(void)
{
    uint8_t hp[PERMUTATIONS], ho[ORIENTATIONS];
    build_transitions();
    return build_distances(PERMUTATIONS, perm_transition, hp) &&
           build_distances(ORIENTATIONS, ori_transition, ho) &&
           pack_distances(hp, hp_packed, PERMUTATIONS) &&
           pack_distances(ho, ho_packed, ORIENTATIONS);
}

typedef struct {
    uint8_t moves[MAX_DEPTH];
    uint8_t length;
    uint64_t nodes;
} solution_t;

static uint8_t heuristic(ranked_state_t state)
{
    MY_SOLVER_COUNT(heuristic_calls);
    uint8_t p = packed_get(hp_packed, state.p);
    uint8_t o = packed_get(ho_packed, state.o);
    /* Both abstractions charge for the same moves: use max, never sum. */
    return p > o ? p : o;
}

/* Return FOUND, or the minimum f that exceeded the current bound. */
static int search(ranked_state_t state, int depth, int bound, uint8_t previous,
                  solution_t *solution)
{
    int f = depth + heuristic(state);
    if (f > bound)
        return f;
    if (state.p == 0 && state.o == 0) {
        solution->length = (uint8_t) depth;
        return FOUND;
    }
    if (depth == MAX_DEPTH)
        return INT_MAX;
    ++solution->nodes;
    MY_SOLVER_COUNT(expanded_nodes);
    int minimum = INT_MAX;
    for (uint8_t face = 0; face < 3; ++face) {
        MY_SOLVER_COUNT(face_candidates);
        /* Adjacent moves of one face combine into at most one HTM move. */
        if (face == previous) {
            MY_SOLVER_COUNT(same_face_pruned);
            continue;
        }
        const uint16_t *perm_row = perm_transition[face];
        const uint16_t *ori_row = ori_transition[face];
        MY_SOLVER_COUNT(transition_row_pairs);
        ranked_state_t next = state;
        for (uint8_t turn = 0; turn < 3; ++turn) {
            /* Reuse the preceding quarter turn for half/inverse children. */
            next.p = perm_row[next.p];
            MY_SOLVER_COUNT(perm_transition_lookups);
            next.o = ori_row[next.o];
            MY_SOLVER_COUNT(ori_transition_lookups);
            MY_SOLVER_COUNT(generated_children);
            solution->moves[depth] = (uint8_t) ((face << 1) + face + turn);
            int result = search(next, depth + 1, bound, face, solution);
            if (result == FOUND)
                return FOUND;
            if (result < minimum)
                minimum = result;
        }
    }
    return minimum;
}

static int solve(ranked_state_t start, solution_t *solution)
{
    memset(solution, 0, sizeof *solution);
    int bound = heuristic(start);
    while (bound <= MAX_DEPTH) {
        MY_SOLVER_COUNT(iterations);
        int result = search(start, 0, bound, NONE, solution);
        if (result == FOUND)
            return 1;
        if (result == INT_MAX)
            break;
        bound = result;
    }
    return 0;
}

static int parse_state(const char *input, state_t *state)
{
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* Buffered stdout can defer write errors until fflush. */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

int main(int argc, char **argv)
{
    state_t state;
    if (argc != 2 || !parse_state(argv[1], &state)) {
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "my_solver");
        return 2;
    }
    if (!initialize_tables()) {
        fputs("could not build complete abstraction tables\n", stderr);
        return 1;
    }
    solution_t solution;
    if (!solve(rank_coordinates(&state), &solution)) {
        fputs("IDA* search failed\n", stderr);
        return 1;
    }
    for (uint8_t i = 0; i < solution.length; ++i)
        printf("%s%s", i ? " " : "", move_names[solution.moves[i]]);
    putchar('\n');
    return output_failed();
}

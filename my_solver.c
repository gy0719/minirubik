#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Host tests may count logical operations; normal builds emit no hooks. */
#ifndef MY_SOLVER_COUNT
#define MY_SOLVER_COUNT(field) ((void) 0)
#endif
#ifndef MY_SOLVER_SETUP_COUNT
#define MY_SOLVER_SETUP_COUNT(field) ((void) 0)
#endif

/* Optimal HTM IDA*: R/B/D generators, max(hp,ho), same-face pruning.
 * Persistent tables: 30240 + 4374 + 2520 + 365 = 37499 bytes.
 * Initialization scratch: one 5040-byte distance buffer + 10080-byte queue.
 * Concrete replay is checked here; full-state BFS/rank oracles are host-only.
 */
enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
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
static uint8_t hp_packed[(PERMUTATIONS + 1) >> 1];
static uint8_t ho_packed[(ORIENTATIONS + 1) >> 1];

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

/* Each operand is 0..2, so a sum needs at most one subtraction. */
static uint8_t reduce_three(uint8_t value)
{
    MY_SOLVER_SETUP_COUNT(mod3_reductions);
    return value >= 3 ? (uint8_t) (value - 3U) : value;
}

static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = reduce_three((uint8_t) (state.o[from] + twist[face][i]));
    }
    return result;
}

/* Lehmer digits use fixed factorial weights: 720, 120, 24, 6, 2, 1. */
static uint16_t rank_permutation(const uint8_t permutation[CUBIES])
{
    uint32_t digit[6];
    MY_SOLVER_SETUP_COUNT(permutation_rank_calls);
    for (uint8_t i = 0; i < 6; ++i) {
        uint32_t smaller = 0;
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j) {
            MY_SOLVER_SETUP_COUNT(permutation_comparisons);
            if (permutation[j] < permutation[i])
                ++smaller;
        }
        digit[i] = smaller;
    }
    uint32_t rank = (digit[0] << 9) + (digit[0] << 7) +
                    (digit[0] << 6) + (digit[0] << 4);
    rank += (digit[1] << 7) - (digit[1] << 3);
    rank += (digit[2] << 4) + (digit[2] << 3);
    rank += (digit[3] << 2) + (digit[3] << 1);
    rank += (digit[4] << 1) + digit[5];
    return (uint16_t) rank;
}

static uint16_t rank_orientation(const uint8_t orientation[CUBIES])
{
    uint16_t rank = 0;
    MY_SOLVER_SETUP_COUNT(orientation_rank_calls);
    for (uint8_t i = 0; i < 6; ++i) {
        MY_SOLVER_SETUP_COUNT(orientation_rank_digits);
        rank = (uint16_t) ((rank << 1) + rank + orientation[i]);
    }
    return rank;
}

/* Advance to the next lexicographic rank; the caller skips the last rank. */
static void next_permutation(uint8_t permutation[CUBIES])
{
    MY_SOLVER_SETUP_COUNT(permutation_successors);
    uint8_t pivot = CUBIES - 2;
    while (permutation[pivot] > permutation[pivot + 1U])
        --pivot;
    uint8_t last = CUBIES - 1;
    while (permutation[last] < permutation[pivot])
        --last;
    uint8_t saved = permutation[pivot];
    permutation[pivot] = permutation[last];
    permutation[last] = saved;
    uint8_t left = (uint8_t) (pivot + 1U), right = CUBIES - 1;
    while (left < right) {
        saved = permutation[left];
        permutation[left++] = permutation[right];
        permutation[right--] = saved;
    }
}

/* Carry through the six base-3 digits, updating the seventh to preserve
 * total twist 0 mod 3. Even a 2 -> 0 carry changes the sum by +1 mod 3.
 */
static void next_orientation(uint8_t orientation[CUBIES])
{
    for (uint8_t i = 6; i-- > 0;) {
        MY_SOLVER_SETUP_COUNT(orientation_carry_digits);
        orientation[6] = orientation[6] ? (uint8_t) (orientation[6] - 1U) : 2;
        if (++orientation[i] < 3)
            return;
        orientation[i] = 0;
    }
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
        sum = reduce_three((uint8_t) (sum + state->o[i]));
    }
    return sum == 0;
}

static ranked_state_t rank_coordinates(const state_t *state)
{
    ranked_state_t coordinates = {rank_permutation(state->p),
                                  rank_orientation(state->o)};
    return coordinates;
}

static void build_transitions(void)
{
    state_t state = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    uint8_t next[CUBIES];
    uint16_t *perm_rows[3] = {
        perm_transition[0], perm_transition[1], perm_transition[2]
    };
    uint16_t *ori_rows[3] = {
        ori_transition[0], ori_transition[1], ori_transition[2]
    };
    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        for (uint8_t face = 0; face < 3; ++face) {
            for (uint8_t i = 0; i < CUBIES; ++i)
                next[i] = state.p[source[face][i]];
            *perm_rows[face]++ = rank_permutation(next);
            MY_SOLVER_SETUP_COUNT(transition_writes);
        }
        if (p + 1U < PERMUTATIONS)
            next_permutation(state.p);
    }
    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        for (uint8_t face = 0; face < 3; ++face) {
            for (uint8_t i = 0; i < CUBIES; ++i)
                next[i] = reduce_three((uint8_t)
                    (state.o[source[face][i]] + twist[face][i]));
            *ori_rows[face]++ = rank_orientation(next);
            MY_SOLVER_SETUP_COUNT(transition_writes);
        }
        if (o + 1U < ORIENTATIONS)
            next_orientation(state.o);
    }
}

/* BFS uses row pointers and a caller-owned fixed queue; no variable stride. */
static int build_distances(uint16_t count, const uint16_t *const rows[3],
                           uint8_t *distance, uint16_t queue[PERMUTATIONS])
{
    uint16_t head = 0, tail = 1;
    memset(distance, UINT8_MAX, count);
    queue[0] = 0;
    distance[0] = 0;
    while (head < tail) {
        uint16_t here = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            const uint16_t *row = rows[face];
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = row[next];
                MY_SOLVER_SETUP_COUNT(bfs_transition_lookups);
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
    unsigned shift = (index & 1U) << 2;
    return (uint8_t) ((table[index >> 1] >> shift) & 0xFU);
}

static void packed_set(uint8_t *table, uint16_t index, uint8_t value)
{
    unsigned shift = (index & 1U) << 2;
    uint8_t mask = (uint8_t) (0xFU << shift);
    table[index >> 1] = (uint8_t) ((table[index >> 1] & (uint8_t) ~mask) |
                                  ((unsigned) value << shift));
}

static int pack_distances(const uint8_t *distance, uint8_t *packed,
                          uint16_t count)
{
    memset(packed, 0, (count + 1U) >> 1);
    for (uint16_t i = 0; i < count; ++i) {
        if (distance[i] > 15) {
            fprintf(stderr, "heuristic does not fit in 4 bits: index=%u value=%u\n",
                    (unsigned) i, (unsigned) distance[i]);
            return 0;
        }
        packed_set(packed, i, distance[i]);
        MY_SOLVER_SETUP_COUNT(packed_writes);
    }
    return 1;
}

static int initialize_tables(void)
{
    uint16_t queue[PERMUTATIONS];
    uint8_t distance[PERMUTATIONS];
    const uint16_t *perm_rows[3] = {
        perm_transition[0], perm_transition[1], perm_transition[2]
    };
    const uint16_t *ori_rows[3] = {
        ori_transition[0], ori_transition[1], ori_transition[2]
    };
    build_transitions();
    return build_distances(PERMUTATIONS, perm_rows, distance, queue) &&
           pack_distances(distance, hp_packed, PERMUTATIONS) &&
           build_distances(ORIENTATIONS, ori_rows, distance, queue) &&
           pack_distances(distance, ho_packed, ORIENTATIONS);
}

typedef struct {
    uint8_t moves[MAX_DEPTH];
    uint8_t length;
#ifdef MY_SOLVER_HOST_TEST
    uint64_t nodes;
#endif
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
#ifdef MY_SOLVER_HOST_TEST
    ++solution->nodes;
#endif
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
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (input[i] < '1' || input[i] > '7')
            return 0;
        state->p[i] = (uint8_t) (input[i] - '1');
    }
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (input[i + CUBIES] < '1' || input[i + CUBIES] > '3')
            return 0;
        state->o[i] = (uint8_t) (input[i + CUBIES] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* Replay the original concrete input without ranked transition lookups. */
static int replay_solution(const state_t *original, const solution_t *solution)
{
    if (solution->length > MAX_DEPTH)
        return 0;
    state_t state = *original;
    for (uint8_t i = 0; i < solution->length; ++i) {
        uint8_t move = solution->moves[i], face, turns;
        if (move >= MOVES)
            return 0;
        if (move < 3) {
            face = 0;
            turns = (uint8_t) (move + 1U);
        } else if (move < 6) {
            face = 1;
            turns = (uint8_t) (move - 2U);
        } else {
            face = 2;
            turns = (uint8_t) (move - 5U);
        }
        for (uint8_t turn = 0; turn < turns; ++turn)
            state = quarter_turn(state, face);
    }
    for (uint8_t i = 0; i < CUBIES; ++i)
        if (state.p[i] != i || state.o[i] != 0)
            return 0;
    return 1;
}

static const struct {
    char input[15];
    uint8_t length;
} validation_cases[3] = {
    {"12345671111111", 0},
    {"25314672313211", 1},
    {"21345671111111", 11},
};

static int concrete_input_test(void)
{
    for (uint8_t i = 0; i < 3; ++i) {
        state_t state;
        solution_t solution;
        if (!parse_state(validation_cases[i].input, &state) ||
            !solve(rank_coordinates(&state), &solution) ||
            solution.length != validation_cases[i].length ||
            !replay_solution(&state, &solution))
            return 0;
    }
    return 1;
}

/* Buffered stdout can defer write errors until fflush. */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

int main(int argc, char **argv)
{
    state_t state;
    int self_test = argc == 2 && !strcmp(argv[1], "--self-test");
    if (argc != 2 || (!self_test && !parse_state(argv[1], &state))) {
        fprintf(stderr, "usage: %s [PPPPPPPOOOOOOO | --self-test]\n",
                argc > 0 && argv[0] ? argv[0] : "my_solver");
        return 2;
    }
    if (!initialize_tables()) {
        fputs("could not build complete abstraction tables\n", stderr);
        return 1;
    }
    if (self_test) {
        if (!concrete_input_test()) {
            fputs("concrete input self-test failed\n", stderr);
            return 1;
        }
        puts("self-test passed: lengths 0, 1, 11 and concrete replay");
        return output_failed();
    }
    solution_t solution;
    if (!solve(rank_coordinates(&state), &solution) ||
        !replay_solution(&state, &solution)) {
        fputs("IDA* search or concrete replay failed\n", stderr);
        return 1;
    }
    for (uint8_t i = 0; i < solution.length; ++i)
        printf("%s%s", i ? " " : "", move_names[solution.moves[i]]);
    putchar('\n');
    return output_failed();
}

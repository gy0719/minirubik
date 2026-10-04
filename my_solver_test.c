#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdlib.h>
#include <time.h>

/* Compile this file on its own: it includes the actual solver implementation
 * so every test exercises the same private functions as normal solving.
 * Renaming the CLI entry point leaves my_solver.c independently compilable.
 *   cc -O3 -std=c99 -Wall -Wextra -Wpedantic my_solver_test.c -o /tmp/my_solver_test
 */
#define main my_solver_cli_main
#include "my_solver.c"
#undef main

static uint8_t hp[PERMUTATIONS], ho[ORIENTATIONS];
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

static void unrank_coordinates(ranked_state_t coordinates, state_t *state)
{
    unrank_state((uint32_t) coordinates.p * ORIENTATIONS + coordinates.o,
                 state);
}

static int check_distances(const char *name, const uint8_t *distance,
                           uint16_t count, int report)
{
    uint8_t maximum = 0;
    if (distance[0] != 0) {
        fprintf(stderr, "H2 failed: %s[0]=%u\n", name, (unsigned) distance[0]);
        return 0;
    }
    for (uint16_t i = 0; i < count; ++i) {
        if (distance[i] == UINT8_MAX) {
            fprintf(stderr, "H2 failed: %s[%u] is uninitialized\n",
                    name, (unsigned) i);
            return 0;
        }
        if (distance[i] > maximum)
            maximum = distance[i];
    }
    if (report)
        printf("H2: %s[0]=0; populated=%u; maximum=%u\n",
               name, (unsigned) count, (unsigned) maximum);
    return 1;
}

static int h2_test(int report)
{
    return check_distances("hp", hp, PERMUTATIONS, report) &&
           check_distances("ho", ho, ORIENTATIONS, report);
}

static int representation_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    ranked_state_t coordinates = rank_coordinates(&solved);
    if (coordinates.p != 0 || coordinates.o != 0) {
        fputs("solved coordinates are not (0,0)\n", stderr);
        return 0;
    }
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved)) {
            fprintf(stderr, "inverse check failed for %s\n", move_names[move]);
            return 0;
        }
    }
    for (uint8_t face = 0; face < 3; ++face) {
        state = solved;
        for (uint8_t turn = 0; turn < 4; ++turn)
            state = quarter_turn(state, face);
        if (memcmp(&solved, &state, sizeof solved)) {
            fprintf(stderr, "four-turn check failed for %s\n",
                    move_names[face * 3U]);
            return 0;
        }
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        state_t restored;
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank) {
            fprintf(stderr, "rank round-trip failed at %lu\n",
                    (unsigned long) rank);
            return 0;
        }
        coordinates = rank_coordinates(&state);
        if (coordinates.p >= PERMUTATIONS || coordinates.o >= ORIENTATIONS ||
            (uint32_t) coordinates.p * ORIENTATIONS + coordinates.o != rank) {
            fprintf(stderr, "coordinate check failed at %lu\n",
                    (unsigned long) rank);
            return 0;
        }
        unrank_coordinates(coordinates, &restored);
        if (memcmp(&state, &restored, sizeof state)) {
            fprintf(stderr, "coordinate round-trip failed at %lu\n",
                    (unsigned long) rank);
            return 0;
        }
        for (uint8_t move = 0; move < MOVES; ++move) {
            state_t next = apply_move(state, move);
            ranked_state_t expected = rank_coordinates(&next);
            ranked_state_t actual = apply_ranked_move(coordinates, move);
            if (actual.p != expected.p || actual.o != expected.o) {
                fprintf(stderr, "transition check failed: rank=%lu move=%s\n",
                        (unsigned long) rank, move_names[move]);
                return 0;
            }
        }
    }
    return 1;
}

/* Replay concrete cubies independently of the ranked transitions. */
static int verify_solution(uint32_t rank, const solution_t *solution)
{
    state_t state;
    unrank_state(rank, &state);
    if (solution->length > MAX_DEPTH)
        return 0;
    for (uint8_t i = 0; i < solution->length; ++i) {
        uint8_t move = solution->moves[i];
        if (move >= MOVES ||
            (i && move / 3U == solution->moves[i - 1U] / 3U))
            return 0;
        state = apply_move(state, move);
    }
    return rank_state(&state) == 0;
}

static void search_failure(const char *test, uint32_t rank, unsigned expected,
                           const solution_t *solution)
{
    state_t state;
    char input[2 * CUBIES + 1];
    unrank_state(rank, &state);
    for (uint8_t i = 0; i < CUBIES; ++i) {
        input[i] = (char) ('1' + state.p[i]);
        input[i + CUBIES] = (char) ('1' + state.o[i]);
    }
    input[2 * CUBIES] = '\0';
    fprintf(stderr, "%s failed: rank=%" PRIu32 " p=%" PRIu32
                    " o=%" PRIu32 " input=%s expected=%u length=%u\n",
            test, rank, rank / ORIENTATIONS, rank % ORIENTATIONS, input,
            expected, (unsigned) solution->length);
}

static int check_search(const char *test, uint32_t rank, unsigned expected,
                         solution_t *solution)
{
    ranked_state_t state = {(uint16_t) (rank / ORIENTATIONS),
                           (uint16_t) (rank % ORIENTATIONS)};
    if (!solve(state, solution) || solution->length != expected ||
        !verify_solution(rank, solution)) {
        search_failure(test, rank, expected, solution);
        return 0;
    }
    return 1;
}

static int basic_search_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    static const uint8_t sequences[][3] = {
        {0, 3, UINT8_MAX}, {0, 6, UINT8_MAX}, {3, 6, UINT8_MAX},
        {0, 3, 6}, {1, 4, 7}, {2, 5, 8},
    };
    solution_t solution;
    if (!check_search("basic", 0, 0, &solution))
        return 0;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state_t state = apply_move(solved, move);
        if (!check_search("basic", rank_state(&state), 1, &solution))
            return 0;
    }
    for (size_t i = 0; i < sizeof sequences / sizeof sequences[0]; ++i) {
        state_t state = solved;
        unsigned length = 0;
        for (uint8_t j = 0; j < 3 && sequences[i][j] != UINT8_MAX; ++j) {
            state = apply_move(state, sequences[i][j]);
            ++length;
        }
        if (!check_search("basic", rank_state(&state), length, &solution))
            return 0;
    }
    puts("basic search passed: solved, all 9 single moves, six 2/3-move states");
    return 1;
}

/* Reference full-state BFS: never called by normal solving. */
static uint8_t *build_oracle(void)
{
    uint8_t *distance = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    if (!distance || !queue) {
        free(distance);
        free(queue);
        fputs("could not allocate host BFS oracle\n", stderr);
        return NULL;
    }
    memset(distance, UINT8_MAX, STATES);
    distance[0] = 0;
    queue[0] = 0;
    uint32_t head = 0, tail = 1;
    uint8_t diameter = 0;
    while (head < tail) {
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = perm_transition[face][next_p];
                next_o = ori_transition[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (distance[there] == UINT8_MAX) {
                    distance[there] = (uint8_t) (distance[here] + 1U);
                    if (distance[there] > diameter)
                        diameter = distance[there];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES || diameter != MAX_DEPTH) {
        fprintf(stderr, "oracle failed: reached=%" PRIu32 " diameter=%u\n",
                tail, (unsigned) diameter);
        free(distance);
        return NULL;
    }
    return distance;
}

static int h1_test(const uint8_t *exact)
{
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        ranked_state_t state = {(uint16_t) (rank / ORIENTATIONS),
                               (uint16_t) (rank % ORIENTATIONS)};
        uint8_t h = heuristic(state);
        if (h > exact[rank]) {
            fprintf(stderr, "H1 failed: rank=%" PRIu32 " p=%u o=%u "
                            "h=%u exact=%u\n", rank, (unsigned) state.p,
                    (unsigned) state.o, (unsigned) h, (unsigned) exact[rank]);
            return 0;
        }
    }
    puts("H1 passed: heuristic admissible for all 3674160 states");
    return 1;
}

static int random_search_test(const uint8_t *exact)
{
    uint32_t seed = UINT32_C(0x12345678);
    uint64_t nodes = 0;
    for (unsigned i = 0; i < 1000; ++i) {
        seed = seed * UINT32_C(1664525) + UINT32_C(1013904223);
        uint32_t rank = seed % STATES;
        solution_t solution;
        if (!check_search("random", rank, exact[rank], &solution))
            return 0;
        nodes += solution.nodes;
    }
    printf("random search passed: 1000 states; expanded=%" PRIu64 "\n", nodes);
    return 1;
}

static double wall_seconds(void)
{
    struct timespec time;
    if (clock_gettime(CLOCK_MONOTONIC, &time) != 0) {
        perror("clock_gettime");
        return -1.0;
    }
    return (double) time.tv_sec + (double) time.tv_nsec / 1e9;
}

static int h3_test(const uint8_t *exact)
{
    double start = wall_seconds();
    uint64_t nodes = 0, maximum = 0;
    if (start < 0)
        return 0;
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        solution_t solution;
        if (!check_search("H3", rank, exact[rank], &solution))
            return 0;
        nodes += solution.nodes;
        if (solution.nodes > maximum)
            maximum = solution.nodes;
        if ((rank + 1U) % 65536U == 0) {
            double now = wall_seconds();
            if (now < 0)
                return 0;
            fprintf(stderr, "H3: %" PRIu32 "/%u states; expanded=%" PRIu64
                            "; wall=%.2f s\n", rank + 1U, STATES, nodes,
                    now - start);
        }
    }
    double end = wall_seconds();
    if (end < 0)
        return 0;
    printf("H3 passed: states=%u; expanded=%" PRIu64 "; max/state=%" PRIu64
           "; wall=%.2f s (search and replay; excludes oracle build)\n",
           STATES, nodes, maximum, end - start);
    return 1;
}

static int check_packing(const char *name, const uint8_t *unpacked,
                         const uint8_t *packed, uint16_t count)
{
    for (uint16_t i = 0; i < count; ++i) {
        uint8_t value = packed_get(packed, i);
        if (value != unpacked[i]) {
            fprintf(stderr, "H4 failed: %s index=%u packed=%u unpacked=%u\n",
                    name, (unsigned) i, (unsigned) value, (unsigned) unpacked[i]);
            return 0;
        }
    }
    printf("H4: %s all %u even/odd entries match\n", name, (unsigned) count);
    return 1;
}

static int h4_test(void)
{
    /* Exercise setters in both orders and every possible nibble value. */
    for (uint8_t low = 0; low < 16; ++low) {
        for (uint8_t high = 0; high < 16; ++high) {
            uint8_t byte = 0xA5;
            packed_set(&byte, 0, low);
            if (packed_get(&byte, 0) != low || packed_get(&byte, 1) != 10)
                goto setter_failure;
            packed_set(&byte, 1, high);
            if (packed_get(&byte, 0) != low || packed_get(&byte, 1) != high)
                goto setter_failure;
            byte = 0xA5;
            packed_set(&byte, 1, high);
            if (packed_get(&byte, 0) != 5 || packed_get(&byte, 1) != high)
                goto setter_failure;
            packed_set(&byte, 0, low);
            if (packed_get(&byte, 0) != low || packed_get(&byte, 1) != high)
                goto setter_failure;
        }
    }
    if ((ho_packed[sizeof ho_packed - 1U] & 0xF0U) != 0) {
        fputs("H4 failed: unused orientation high nibble is not zero\n", stderr);
        return 0;
    }
    return check_packing("hp", hp, hp_packed, PERMUTATIONS) &&
           check_packing("ho", ho, ho_packed, ORIENTATIONS);
setter_failure:
    fputs("H4 failed: packed setter did not preserve its neighbor\n", stderr);
    return 0;
}

static void report_memory(void)
{
    printf("permutation transitions: %zu bytes\n", sizeof perm_transition);
    printf("orientation transitions: %zu bytes\n", sizeof ori_transition);
    printf("packed hp: %zu bytes; packed ho: %zu bytes\n",
           sizeof hp_packed, sizeof ho_packed);
    printf("persistent target tables: %zu bytes\n",
           sizeof perm_transition + sizeof ori_transition +
           sizeof hp_packed + sizeof ho_packed);
    printf("search context: %zu bytes; path: %u moves; recursion: at most %u levels\n",
           sizeof(solution_t), MAX_DEPTH, MAX_DEPTH + 1);
    printf("target initialization scratch: %zu bytes plus call frames\n",
           (size_t) PERMUTATIONS + ORIENTATIONS +
           PERMUTATIONS * sizeof(uint16_t));
}

static void usage(FILE *output, const char *program)
{
    fprintf(output, "usage: %s [--self-test | --h1 | --h2 | --h3 | --h4 | "
                    "--random-test | --memory | --help]\n", program);
    fputs("No option runs --self-test. --h3 exhaustively solves all 3674160 states.\n",
          output);
}

int main(int argc, char **argv)
{
    const char *program = argc > 0 && argv[0] ? argv[0] : "my_solver_test";
    if (argc != 1 && argc != 2) {
        usage(stderr, program);
        return 2;
    }
    const char *option = argc == 2 ? argv[1] : "--self-test";
    if (!strcmp(option, "--help")) {
        usage(stdout, program);
        return output_failed();
    }
    static const char *const modes[] = {
        "--self-test", "--h1", "--h2", "--h3", "--h4", "--random-test", "--memory"
    };
    int mode = -1;
    for (size_t i = 0; i < sizeof modes / sizeof modes[0]; ++i)
        if (!strcmp(option, modes[i]))
            mode = (int) i;
    if (mode < 0) {
        usage(stderr, program);
        return 2;
    }
    if (!initialize_tables() ||
        !build_distances(PERMUTATIONS, perm_transition, hp) ||
        !build_distances(ORIENTATIONS, ori_transition, ho)) {
        fputs("could not build complete abstraction tables\n", stderr);
        return 1;
    }
    if (mode == 0) {
        if (!representation_test() || !h2_test(1) || !basic_search_test() ||
            !h4_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        puts("self-test passed: all rank/coordinate round-trips and "
             "33067440 concrete/ranked transitions");
        return output_failed();
    }
    if (mode == 2)
        return h2_test(1) ? output_failed() : 1;
    if (mode == 4)
        return h4_test() ? output_failed() : 1;
    if (mode == 6) {
        report_memory();
        return output_failed();
    }
    uint8_t *exact = build_oracle();
    if (!exact)
        return 1;
    int ok = mode == 1 ? h1_test(exact) :
             mode == 3 ? h3_test(exact) : random_search_test(exact);
    free(exact);
    return ok ? output_failed() : 1;
}

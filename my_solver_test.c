#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdlib.h>
#include <time.h>

/* Compile this file on its own: it includes the actual solver implementation
 * so every test exercises the same private functions as normal solving.
 * Renaming the CLI entry point leaves my_solver.c independently compilable.
 *   cc -O3 -std=c99 -Wall -Wextra -Wpedantic my_solver_test.c -o /tmp/my_solver_test
 *
 * Measurements (run one measurement at a time):
 *   /tmp/my_solver_test --memory > /tmp/solver-memory.txt
 *   /tmp/my_solver_test --benchmark-11 > /tmp/solver-d11.txt
 *   /tmp/my_solver_test --benchmark-worst-11 > /tmp/solver-worst-d11.txt
 *   /tmp/my_solver_test --benchmark-all-d11 > /tmp/solver-all-d11.txt
 *   /tmp/my_solver_test --self-test
 * Reproducibility information, recorded outside the solver:
 *   cc --version > /tmp/solver-compiler.txt
 *   uname -a > /tmp/solver-system.txt
 *   lscpu > /tmp/solver-cpu.txt
 *   sha256sum my_solver.c my_solver_test.c
 * Add -DMY_SOLVER_INSTRUMENT for direct operation counts, checked against
 * the exact loop model. Use the normal build for timings (no count hooks).
 *   cc -O3 -std=c99 -Wall -Wextra -Wpedantic -DMY_SOLVER_INSTRUMENT \
 *      my_solver_test.c -o /tmp/my_solver_test_counts
 * --benchmark-worst-11 checks the fixed worst case separately.
 * Timings are host wall times; logical C operations are not retired CPU
 * instructions. Oracle construction and replay are outside solve timers.
 */
typedef struct {
    uint64_t iterations;
    uint64_t expanded_nodes;
    uint64_t heuristic_calls;
    uint64_t face_candidates;
    uint64_t same_face_pruned;
    uint64_t transition_row_pairs;
    uint64_t generated_children;
    uint64_t perm_transition_lookups;
    uint64_t ori_transition_lookups;
} operation_counts_t;

#ifdef MY_SOLVER_INSTRUMENT
static operation_counts_t measured_operations;
#define MY_SOLVER_COUNT(field) (++measured_operations.field)
#endif

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

/* Per-move reference search, kept only on the host.
 * This checks the solution path and per-state expanded-node count.
 */
static ranked_state_t apply_ranked_move(ranked_state_t state, uint8_t move)
{
    uint8_t face = (uint8_t) (move / 3U);
    for (uint8_t turn = 0; turn <= move % 3U; ++turn) {
        state.p = perm_transition[face][state.p];
        state.o = ori_transition[face][state.o];
    }
    return state;
}

static int search_reference(ranked_state_t state, int depth, int bound,
                           uint8_t previous, solution_t *solution)
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
    int minimum = INT_MAX;
    for (uint8_t move = 0; move < MOVES; ++move) {
        uint8_t face = (uint8_t) (move / 3U);
        if (face == previous)
            continue;
        solution->moves[depth] = move;
        int result = search_reference(apply_ranked_move(state, move),
                                      depth + 1, bound, face, solution);
        if (result == FOUND)
            return FOUND;
        if (result < minimum)
            minimum = result;
    }
    return minimum;
}

static int check_reference(ranked_state_t start, const solution_t *actual)
{
    solution_t reference = {0};
    int bound = heuristic(start);
    while (bound <= MAX_DEPTH) {
        int result = search_reference(start, 0, bound, NONE, &reference);
        if (result == FOUND) {
            if (reference.length == actual->length &&
                reference.nodes == actual->nodes &&
                !memcmp(reference.moves, actual->moves, actual->length))
                return 1;
            break;
        }
        if (result == INT_MAX)
            break;
        bound = result;
    }
    fprintf(stderr, "reference search comparison failed: p=%u o=%u; "
                    "length reference/actual=%u/%u; "
                    "expanded reference/actual=%" PRIu64 "/%" PRIu64 "\n",
            (unsigned) start.p, (unsigned) start.o,
            (unsigned) reference.length, (unsigned) actual->length,
            reference.nodes, actual->nodes);
    return 0;
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
        !verify_solution(rank, solution) || !check_reference(state, solution)) {
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

/* Keep the required distance-11 vector visible outside exhaustive H3. */
static int distance_11_test(void)
{
    const char *input = "21345671111111";
    state_t state;
    solution_t solution;
    if (!parse_state(input, &state)) {
        fputs("distance-11 failed: could not parse 21345671111111\n", stderr);
        return 0;
    }
    if (!check_search("distance-11", rank_state(&state), 11, &solution))
        return 0;
    printf("distance-11 passed: input=%s; expected=11; length=%u; replay=solved\n",
           input, (unsigned) solution.length);
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

/* Observe iteration count by calling the unchanged search() with exactly
 * solve()'s bounds, root face and path storage. This untimed second run must
 * reproduce the timed solve's length, path and expanded-node count.
 */
static int observe_iterations(ranked_state_t start, solution_t *solution,
                              uint64_t *iterations)
{
    memset(solution, 0, sizeof *solution);
    *iterations = 0;
    int bound = heuristic(start);
    while (bound <= MAX_DEPTH) {
        ++*iterations;
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

/* Exact source-level accounting for the face loop. Complete roots visit three
 * faces and generate nine children; complete non-roots skip one face and
 * generate six. Successful ancestors stop at the selected face/turn prefix.
 * Each child costs exactly one lookup per transition table. In instrumented
 * builds the same counts must also match hooks in the actual search.
 * Counts exclude initialization, concrete replay and the reference search.
 */
static int count_operations(ranked_state_t start, const solution_t *actual,
                            operation_counts_t *counts)
{
    solution_t observed;
    memset(counts, 0, sizeof *counts);
#ifdef MY_SOLVER_INSTRUMENT
    memset(&measured_operations, 0, sizeof measured_operations);
#endif
    if (!observe_iterations(start, &observed, &counts->iterations) ||
        observed.length != actual->length || observed.nodes != actual->nodes ||
        memcmp(observed.moves, actual->moves, actual->length)) {
        fputs("operation accounting failed: observed search differs from solve\n",
              stderr);
        return 0;
    }
    counts->expanded_nodes = actual->nodes;
    if (actual->length == 0) {
        if (actual->nodes != 0 || counts->iterations != 1)
            return 0;
    } else {
        uint64_t complete_roots = counts->iterations - 1U;
        if (actual->nodes < actual->length + complete_roots) {
            fputs("operation accounting failed: invalid expansion counts\n", stderr);
            return 0;
        }
        uint64_t complete_nodes = actual->nodes - actual->length;
        uint64_t complete_nonroots = complete_nodes - complete_roots;
        counts->face_candidates = 3U * complete_nodes;
        counts->same_face_pruned = complete_nonroots;
        counts->generated_children = 9U * complete_roots + 6U * complete_nonroots;
        uint8_t previous = NONE;
        for (uint8_t depth = 0; depth < actual->length; ++depth) {
            uint8_t selected_face = (uint8_t) (actual->moves[depth] / 3U);
            for (uint8_t face = 0; face <= selected_face; ++face) {
                ++counts->face_candidates;
                if (face == previous) {
                    ++counts->same_face_pruned;
                } else {
                    counts->generated_children +=
                        face < selected_face ? 3U : actual->moves[depth] % 3U + 1U;
                }
            }
            previous = selected_face;
        }
    }
    counts->transition_row_pairs =
        counts->face_candidates - counts->same_face_pruned;
    counts->perm_transition_lookups = counts->generated_children;
    counts->ori_transition_lookups = counts->generated_children;
    counts->heuristic_calls = counts->generated_children + counts->iterations + 1U;
#ifdef MY_SOLVER_INSTRUMENT
    if (memcmp(counts, &measured_operations, sizeof *counts)) {
        fputs("operation accounting failed: actual hooks differ from loop model\n",
              stderr);
        return 0;
    }
#endif
    return 1;
}

static int operation_counts_test(void)
{
    static const struct {
        const char *input;
        unsigned length;
        uint64_t nodes, children;
    } cases[] = {
        {"12345671111111", 0, 0, 0},
        {"25314672313211", 1, 1, 3},
        {"21345671111111", 11, 38998, 233961},
        {"54721631111111", 11, 106635, 639792},
    };
    state_t invalid;
    /* The proposed 25314672213211 vector has orientation sum 5, not 0 mod 3. */
    if (parse_state("25314672213211", &invalid)) {
        fputs("invalid single-R vector was accepted\n", stderr);
        return 0;
    }
    for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
        state_t state;
        solution_t solution;
        operation_counts_t counts;
        if (!parse_state(cases[i].input, &state)) {
            fprintf(stderr, "could not parse count vector: %s\n", cases[i].input);
            return 0;
        }
        if (!check_search("operation counts", rank_state(&state),
                          cases[i].length, &solution) ||
            !count_operations(rank_coordinates(&state), &solution, &counts))
            return 0;
        if (counts.expanded_nodes != cases[i].nodes ||
            counts.generated_children != cases[i].children) {
            fprintf(stderr, "operation counts failed: input=%s\n", cases[i].input);
            return 0;
        }
    }
    puts("operation counts passed: solved, R, required/worst distance-11; "
         "reference paths and expanded nodes match");
    return 1;
}

static void report_operations(const operation_counts_t *counts)
{
    puts("operation_count_scope=source_level_logical_solve_operations");
#ifdef MY_SOLVER_INSTRUMENT
    puts("operation_count_method="
         "direct_hooks_checked_against_face_loop_accounting");
#else
    puts("operation_count_method=exact_face_loop_accounting");
#endif
    puts("machine_instruction_counts=false");
    printf("ida_iterations=%" PRIu64 "\n", counts->iterations);
    printf("expanded_nodes=%" PRIu64 "\n", counts->expanded_nodes);
    printf("heuristic_calls=%" PRIu64 "\n", counts->heuristic_calls);
    printf("same_face_checks=%" PRIu64 "\n", counts->face_candidates);
    printf("same_face_pruned_faces=%" PRIu64 "\n", counts->same_face_pruned);
    printf("generated_children=%" PRIu64 "\n", counts->generated_children);
    printf("transition_row_pointer_pairs=%" PRIu64 "\n", counts->transition_row_pairs);
    printf("perm_transition_table_lookups=%" PRIu64 "\n",
           counts->perm_transition_lookups);
    printf("ori_transition_table_lookups=%" PRIu64 "\n",
           counts->ori_transition_lookups);
    puts("apply_ranked_move_calls=0\nmove_div3_search=0\nmove_div3_apply=0\n"
         "move_div3_total=0\nmove_mod3_apply_loop_condition=0");
}

static int benchmark_11(const char *input, const char *name)
{
    state_t state;
    solution_t solution;
    operation_counts_t counts;
    if (!parse_state(input, &state))
        return 0;
    uint32_t rank = rank_state(&state);
    ranked_state_t start = rank_coordinates(&state);
    double before = wall_seconds();
    if (before < 0)
        return 0;
    int found = solve(start, &solution);
    double after = wall_seconds();
    if (after < 0)
        return 0;
    if (!found || solution.length != 11 || !verify_solution(rank, &solution) ||
        !check_reference(start, &solution)) {
        search_failure("benchmark-11", rank, 11, &solution);
        return 0;
    }
    if (!count_operations(start, &solution, &counts))
        return 0;
    printf("benchmark=%s\n", name);
    puts("solve_time_scope=solve_only\nclock=CLOCK_MONOTONIC");
#ifdef MY_SOLVER_INSTRUMENT
    puts("solve_time_includes_instrumentation=true");
#else
    puts("solve_time_includes_instrumentation=false");
#endif
    printf("input=%s\nrank=%" PRIu32 "\nsolution_length=%u\n",
           input, rank, (unsigned) solution.length);
    printf("solve_wall_seconds=%.9f\n", after - before);
    puts("replay=solved\ncounted_path_matches_original=true\n"
         "reference_path_matches=true\nreference_expanded_nodes_match=true");
    fputs("solution=", stdout);
    for (uint8_t i = 0; i < solution.length; ++i)
        printf("%s%s", i ? " " : "", move_names[solution.moves[i]]);
    putchar('\n');
    report_operations(&counts);
    return 1;
}

static void format_input(uint32_t rank, char input[2 * CUBIES + 1])
{
    state_t state;
    unrank_state(rank, &state);
    for (uint8_t i = 0; i < CUBIES; ++i) {
        input[i] = (char) ('1' + state.p[i]);
        input[i + CUBIES] = (char) ('1' + state.o[i]);
    }
    input[2 * CUBIES] = '\0';
}

static int benchmark_all_d11(const uint8_t *exact)
{
    uint32_t count = 0, tested = 0, worst_rank = 0;
    uint64_t total = 0, minimum = UINT64_MAX, maximum = 0;
    double solve_seconds = 0;
    for (uint32_t rank = 0; rank < STATES; ++rank)
        if (exact[rank] == 11)
            ++count;
    if (count != 2644) {
        fprintf(stderr, "distance-11 count failed: expected=2644 actual=%" PRIu32
                        "\n", count);
        return 0;
    }
    /* Oracle construction and the count scan precede the benchmark timer. */
    double set_start = wall_seconds();
    if (set_start < 0)
        return 0;
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        if (exact[rank] != 11)
            continue;
        ranked_state_t state = {(uint16_t) (rank / ORIENTATIONS),
                               (uint16_t) (rank % ORIENTATIONS)};
        solution_t solution;
        double before = wall_seconds();
        if (before < 0)
            return 0;
        int found = solve(state, &solution);
        double after = wall_seconds();
        if (after < 0)
            return 0;
        if (!found || solution.length != exact[rank] ||
            !verify_solution(rank, &solution) || !check_reference(state, &solution)) {
            search_failure("benchmark-all-d11", rank, exact[rank], &solution);
            return 0;
        }
#ifdef MY_SOLVER_INSTRUMENT
        operation_counts_t counts;
        if (!count_operations(state, &solution, &counts))
            return 0;
#endif
        solve_seconds += after - before;
        ++tested;
        total += solution.nodes;
        if (solution.nodes < minimum)
            minimum = solution.nodes;
        if (solution.nodes > maximum) {
            maximum = solution.nodes;
            worst_rank = rank;
        }
    }
    double set_end = wall_seconds();
    if (set_end < 0)
        return 0;
    char input[2 * CUBIES + 1];
    format_input(worst_rank, input);
    puts("benchmark=all_d11\nclock=CLOCK_MONOTONIC\n"
         "solve_time_scope=sum_of_solve_only_intervals\n"
         "set_time_scope=scan_search_and_host_validation_excludes_bfs");
#ifdef MY_SOLVER_INSTRUMENT
    puts("solve_time_includes_instrumentation=true\n"
         "operation_count_hooks_match_model_all=true");
#else
    puts("solve_time_includes_instrumentation=false");
#endif
    printf("distance_11_states=%" PRIu32 "\nstates_tested=%" PRIu32 "\n",
           count, tested);
    printf("total_expanded_nodes=%" PRIu64 "\n", total);
    printf("min_expanded_nodes=%" PRIu64 "\n", minimum);
    printf("average_expanded_nodes=%.6f\n", (double) total / tested);
    printf("max_expanded_nodes=%" PRIu64 "\n", maximum);
    printf("worst_rank=%" PRIu32 "\nworst_input=%s\n", worst_rank, input);
    printf("solve_wall_seconds=%.9f\nset_wall_seconds=%.9f\n",
           solve_seconds, set_end - set_start);
    puts("solution_length=11\nreplay=solved_all\n"
         "reference_path_matches_all=true\nreference_expanded_nodes_match_all=true");
    return 1;
}

static void report_memory(void)
{
    size_t tables = sizeof perm_transition + sizeof ori_transition +
                    sizeof hp_packed + sizeof ho_packed;
    size_t other_arrays = sizeof move_names + sizeof source + sizeof twist;
    size_t name_strings = 0;
    for (uint8_t move = 0; move < MOVES; ++move)
        name_strings += (strlen(move_names[move]) + 1U) * sizeof(char);
    puts("accounting=object_sizes_not_process_peak");
    printf("persistent_solver_data.perm_transition_bytes=%zu\n",
           sizeof perm_transition);
    printf("persistent_solver_data.ori_transition_bytes=%zu\n",
           sizeof ori_transition);
    printf("persistent_solver_data.hp_packed_bytes=%zu\n", sizeof hp_packed);
    printf("persistent_solver_data.ho_packed_bytes=%zu\n", sizeof ho_packed);
    printf("persistent_solver_data.tables_bytes=%zu\n", tables);
    printf("persistent_solver_data.move_names_pointer_array_bytes=%zu\n",
           sizeof move_names);
    printf("persistent_solver_data.source_bytes=%zu\n", sizeof source);
    printf("persistent_solver_data.twist_bytes=%zu\n", sizeof twist);
    printf("persistent_solver_data.other_named_arrays_bytes=%zu\n", other_arrays);
    printf("persistent_solver_data.total_named_arrays_bytes=%zu\n",
           tables + other_arrays);
    /* Literal character counts are separate from sizeof(pointer array).
     * Diagnostic/format strings, code, linker padding and libc are excluded.
     */
    printf("persistent_solver_data.move_name_string_bytes=%zu\n", name_strings);
    printf("persistent_solver_data.arrays_and_move_strings_bytes=%zu\n",
           tables + other_arrays + name_strings);
    printf("initialization_only_scratch.hp_bytes=%zu\n",
           sizeof(uint8_t[PERMUTATIONS]));
    printf("initialization_only_scratch.ho_bytes=%zu\n",
           sizeof(uint8_t[ORIENTATIONS]));
    printf("initialization_only_scratch.queue_bytes=%zu\n",
           sizeof(uint16_t[PERMUTATIONS]));
    printf("initialization_only_scratch.total_bytes=%zu\n",
           sizeof(uint8_t[PERMUTATIONS]) + sizeof(uint8_t[ORIENTATIONS]) +
           sizeof(uint16_t[PERMUTATIONS]));
    printf("search_path_storage.moves_bytes=%zu\n",
           sizeof(((solution_t *) 0)->moves));
    printf("search_path_storage.length_bytes=%zu\n",
           sizeof(((solution_t *) 0)->length));
    printf("search_path_storage.node_counter_bytes=%zu\n",
           sizeof(((solution_t *) 0)->nodes));
    printf("search_path_storage.context_bytes=%zu\n", sizeof(solution_t));
    printf("search_path_storage.max_recursive_frames=%u\n", MAX_DEPTH + 1);
    puts("search_path_storage.call_frame_bytes=compiler_dependent\n"
         "host_bfs_oracle_in_target_memory=false\n"
         "excluded=diagnostic_strings_code_linker_padding_call_frames_libc");
}

static void usage(FILE *output, const char *program)
{
    fprintf(output, "usage: %s [--self-test | --h1 | --h2 | --h3 | --h4 | "
                    "--random-test | --distance-11 | --memory | "
                    "--benchmark-11 | --benchmark-all-d11 | "
                    "--benchmark-worst-11 | --help]\n",
            program);
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
        "--self-test", "--h1", "--h2", "--h3", "--h4", "--random-test", "--memory",
        "--distance-11", "--benchmark-11", "--benchmark-all-d11", "--benchmark-worst-11"
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
            !distance_11_test() || !h4_test() || !operation_counts_test()) {
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
    if (mode == 7)
        return distance_11_test() ? output_failed() : 1;
    if (mode == 8)
        return benchmark_11("21345671111111", "required_d11") ? output_failed() : 1;
    if (mode == 10)
        return benchmark_11("54721631111111", "worst_d11") ?
               output_failed() : 1;
    if (mode == 6) {
        report_memory();
        return output_failed();
    }
    uint8_t *exact = build_oracle();
    if (!exact)
        return 1;
    int ok = mode == 1 ? h1_test(exact) :
             mode == 3 ? h3_test(exact) :
             mode == 9 ? benchmark_all_d11(exact) : random_search_test(exact);
    free(exact);
    return ok ? output_failed() : 1;
}

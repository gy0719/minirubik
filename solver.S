.equ RENDER, 0
.option norvc
.option norelax


/* ============================================================
 * Read-only data
 * ============================================================ */
.section .rodata,"a",@progbits
.balign 1

.globl cube_input
.type cube_input, @object
cube_input:
    .ascii "54721631111111"
cube_input_end:
    .byte 0
.size cube_input, . - cube_input

.if (cube_input_end - cube_input) != 14
.error "cube_input must contain exactly 14 characters"
.endif


/* ============================================================
 * Writable storage
 * ============================================================ */
.section .bss,"aw",@nobits
.balign 4

/* Preserve the original input coordinates across solve and replay. */
.globl perm_rank
.type perm_rank, @object
perm_rank:
    .space 4
.size perm_rank, . - perm_rank

.globl ori_rank
.type ori_rank, @object
ori_rank:
    .space 4
.size ori_rank, . - ori_rank


.globl solution_length
.type solution_length, @object
solution_length:
    .space 4
.size solution_length, . - solution_length

.globl solution_path
.type solution_path, @object
solution_path:
    .space 12
.size solution_path, . - solution_path


.globl validation_result
.type validation_result, @object
validation_result:
    .space 4
.size validation_result, . - validation_result


/* 12 frames × 8 words × 4 bytes = 384 bytes. */
.balign 4
.globl search_frames
.type search_frames, @object
search_frames:
    .space 384
.size search_frames, . - search_frames


/* ============================================================
 * Code
 * ============================================================ */
.section .text,"ax",@progbits
.balign 4


/* ------------------------------------------------------------
 * rank_permutation
 *
 * Input:
 *   a0 = address of 7 permutation characters
 *
 * Output:
 *   a0 = permutation coordinate [0, 5039]
 *
 * Uses the lexicographic / Lehmer rank used by the C solver.
 * No MUL instruction is used.
 * ------------------------------------------------------------ */
.type rank_permutation, @function
rank_permutation:
    mv      t0, a0          /* base pointer */
    li      t1, 0           /* rank */
    li      t2, 0           /* i */

.Lperm_outer:
    li      t3, 6
    bgeu    t2, t3, .Lperm_done

    /* current = input[i] */
    add     t4, t0, t2
    lbu     t5, 0(t4)

    /* Count elements to the right smaller than current. */
    addi    t6, t2, 1       /* j = i + 1 */
    li      a1, 0           /* smaller = 0 */

.Lperm_inner:
    li      a2, 7
    bgeu    t6, a2, .Lperm_digit_done

    add     a3, t0, t6
    lbu     a4, 0(a3)

    bltu    a4, t5, .Lperm_smaller

.Lperm_next_j:
    addi    t6, t6, 1
    j       .Lperm_inner

.Lperm_smaller:
    addi    a1, a1, 1
    j       .Lperm_next_j


.Lperm_digit_done:
    /*
     * Lexicographic rank recurrence:
     *
     * rank = rank * (7 - i) + smaller
     *
     * Use shift/add multiplication because RV32I has no MUL.
     */

    li      a2, 7
    sub     a2, a2, t2      /* multiplier = 7 - i */

    li      a3, 0           /* product */
    mv      a4, t1          /* shifted multiplicand */

.Lperm_mul:
    andi    a5, a2, 1
    beqz    a5, .Lperm_mul_skip

    add     a3, a3, a4

.Lperm_mul_skip:
    slli    a4, a4, 1
    srli    a2, a2, 1
    bnez    a2, .Lperm_mul

    add     t1, a3, a1      /* rank = product + smaller */

    addi    t2, t2, 1
    j       .Lperm_outer


.Lperm_done:
    mv      a0, t1
    ret

.size rank_permutation, . - rank_permutation


/* ------------------------------------------------------------
 * rank_orientation
 *
 * Input:
 *   a0 = address of first orientation character
 *
 * Output:
 *   a0 = orientation coordinate [0, 728]
 *
 * Only the first six orientations are independent.
 *
 * rank = rank * 3 + digit
 *
 * ASCII:
 *   '1' -> 0
 *   '2' -> 1
 *   '3' -> 2
 * ------------------------------------------------------------ */
.type rank_orientation, @function
rank_orientation:
    mv      t0, a0          /* base pointer */
    li      t1, 0           /* rank */
    li      t2, 0           /* i */

.Lori_loop:
    li      t3, 6
    bgeu    t2, t3, .Lori_done

    add     t4, t0, t2
    lbu     t5, 0(t4)

    /* Convert ASCII '1'/'2'/'3' to 0/1/2. */
    addi    t5, t5, -49

    /* rank *= 3 -> rank = (rank << 1) + rank */
    slli    t6, t1, 1
    add     t1, t6, t1

    /* rank += digit */
    add     t1, t1, t5

    addi    t2, t2, 1
    j       .Lori_loop


.Lori_done:
    mv      a0, t1
    ret

.size rank_orientation, . - rank_orientation


/* ============================================================
 * Solver core
 *
 * Internal calling convention (no platform stack is needed):
 *   a4/a5 hold solve's root coordinates; a6 holds solve's return PC.
 *   t6 holds search's return PC; a3 holds heuristic's return PC.
 *   Helpers preserve a4/a5/a6/t6 and all s registers.
 *   search uses s0..s11 for its active node and cached transition rows.
 * These routines are internal to this bare-metal program, not C ABI entry
 * points. The only search stack is the existing 384-byte search_frames.
 * ============================================================ */

/* a0 = packed table, a1 = coordinate; return a0 = four-bit distance.
 * Clobbers t0/t1. Even coordinates select the low nibble.
 */
.type packed_get, @function
packed_get:
    srli    t0, a1, 1
    add     t0, a0, t0
    lbu     a0, 0(t0)
    andi    t1, a1, 1
    slli    t1, t1, 2
    srl     a0, a0, t1
    andi    a0, a0, 15
    ret
.size packed_get, . - packed_get

/* a0 = p, a1 = o; return a0 = max(hp[p], ho[o]). */
.type heuristic, @function
heuristic:
    mv      a3, ra
    mv      a2, a1
    mv      a1, a0
    la      a0, hp_table
    jal     ra, packed_get
    mv      t2, a0
    mv      a1, a2
    la      a0, ho_table
    jal     ra, packed_get
    bgeu    a0, t2, .Lheuristic_return
    mv      a0, t2
.Lheuristic_return:
    jalr    zero, 0(a3)
.size heuristic, . - heuristic

/* a0 = face (R=0, B=1, D=2); return a0/a1 = p/o row pointers.
 * Face-major row strides: 5040 halfwords = 10080 bytes and
 * 729 halfwords = 1458 bytes. No multiplication is required.
 */
.type transition_rows, @function
transition_rows:
    la      t0, perm_move_table
    la      a1, ori_move_table
    beqz    a0, .Lrows_return
    li      t1, 10080
    add     t0, t0, t1
    addi    a1, a1, 1458
    li      t2, 1
    beq     a0, t2, .Lrows_return
    add     t0, t0, t1
    addi    a1, a1, 1458
.Lrows_return:
    mv      a0, t0
    ret
.size transition_rows, . - transition_rows

/* a0/a1 = quarter-turn coordinates, s10/s11 = selected p/o rows.
 * Return the next quarter-turn coordinates in a0/a1.
 */
.type quarter_transition, @function
quarter_transition:
    slli    t0, a0, 1
    add     t0, s10, t0
    lhu     a0, 0(t0)
    slli    t0, a1, 1
    add     t0, s11, t0
    lhu     a1, 0(t0)
    ret
.size quarter_transition, . - quarter_transition

/* a0 = root p, a1 = root o, a2 = bound.
 * Return a0 = -1 (FOUND), or the minimum exceeded f / INT_MAX.
 * Active node:
 *   s0 depth; s1 p; s2 o; s3 quarter_p; s4 quarter_o;
 *   s5 face; s6 turn; s7 previous; s8 minimum; s9 bound;
 *   s10 permutation row; s11 orientation row.
 */
.type search, @function
search:
    mv      t6, ra
    mv      s1, a0
    mv      s2, a1
    mv      s9, a2
    jal     ra, heuristic
    bltu    s9, a0, .Lsearch_return
    or      t0, s1, s2
    beqz    t0, .Lsearch_root_goal

    li      s0, 0
    mv      s3, s1
    mv      s4, s2
    li      s5, 0
    li      s6, 0
    li      s7, 3
    li      s8, 0x7fffffff
    li      s10, 0
    li      s11, 0

.Lsearch_loop:
    li      t0, 3
    bne     s6, t0, .Lsearch_face
    addi    s5, s5, 1
    li      s6, 0
.Lsearch_face:
    li      t0, 3
    bne     s5, t0, .Lsearch_next_face
    beqz    s0, .Lsearch_exhausted

    /* Return an exhausted child's minimum to its suspended parent. */
    mv      t0, s8
    addi    s0, s0, -1
    slli    t1, s0, 5
    la      t2, search_frames
    add     t1, t1, t2
    lw      s1, 0(t1)
    lw      s2, 4(t1)
    lw      s3, 8(t1)
    lw      s4, 12(t1)
    lw      s5, 16(t1)
    lw      s6, 20(t1)
    lw      s7, 24(t1)
    lw      s8, 28(t1)
    bgeu    t0, s8, .Lsearch_restored
    mv      s8, t0
.Lsearch_restored:
    li      t0, 3
    bgeu    s6, t0, .Lsearch_loop
    /* A completed face does not need its row pointers restored. */
    mv      a0, s5
    jal     ra, transition_rows
    mv      s10, a0
    mv      s11, a1
    j       .Lsearch_loop

.Lsearch_next_face:
    bnez    s6, .Lsearch_generate
    bne     s5, s7, .Lsearch_select_rows
    /* Same-face pruning skips all three turns at once. */
    addi    s5, s5, 1
    j       .Lsearch_loop
.Lsearch_select_rows:
    mv      a0, s5
    jal     ra, transition_rows
    mv      s10, a0
    mv      s11, a1
    mv      s3, s1
    mv      s4, s2

.Lsearch_generate:
    /* Reuse the preceding quarter turn for half/inverse children. */
    mv      a0, s3
    mv      a1, s4
    jal     ra, quarter_transition
    mv      s3, a0
    mv      s4, a1
    slli    t0, s5, 1
    add     t0, t0, s5
    add     t0, t0, s6
    la      t1, solution_path
    add     t1, t1, s0
    sb      t0, 0(t1)
    addi    s6, s6, 1

    jal     ra, heuristic
    addi    t0, s0, 1
    add     t0, t0, a0
    bltu    s9, t0, .Lsearch_cutoff
    or      t0, s3, s4
    beqz    t0, .Lsearch_child_goal
    addi    t0, s0, 1
    li      t1, 11
    beq     t0, t1, .Lsearch_loop

    /* Only an expanded child suspends its parent. Frame layout:
     * +0 p, +4 o, +8 quarter_p, +12 quarter_o, +16 face,
     * +20 turn, +24 previous, +28 minimum; stride = 32 bytes.
     */
    slli    t0, s0, 5
    la      t1, search_frames
    add     t0, t0, t1
    sw      s1, 0(t0)
    sw      s2, 4(t0)
    sw      s3, 8(t0)
    sw      s4, 12(t0)
    sw      s5, 16(t0)
    sw      s6, 20(t0)
    sw      s7, 24(t0)
    sw      s8, 28(t0)
    addi    s0, s0, 1
    mv      s1, s3
    mv      s2, s4
    mv      s7, s5
    li      s5, 0
    li      s6, 0
    li      s8, 0x7fffffff
    j       .Lsearch_loop

.Lsearch_cutoff:
    bgeu    t0, s8, .Lsearch_loop
    mv      s8, t0
    j       .Lsearch_loop
.Lsearch_child_goal:
    la      t0, solution_length
    addi    t1, s0, 1
    sw      t1, 0(t0)
    li      a0, -1
    j       .Lsearch_return
.Lsearch_root_goal:
    la      t0, solution_length
    sw      zero, 0(t0)
    li      a0, -1
    j       .Lsearch_return
.Lsearch_exhausted:
    mv      a0, s8
.Lsearch_return:
    jalr    zero, 0(t6)
.size search, . - search

/* a0 = p, a1 = o; return a0 = success (1) or failure (0).
 * The next bound is the preceding search's minimum exceeded f.
 */
.type solve, @function
solve:
    mv      a4, a0
    mv      a5, a1
    mv      a6, ra
    la      t0, solution_length
    sw      zero, 0(t0)
    la      t0, solution_path
    sw      zero, 0(t0)
    sw      zero, 4(t0)
    sw      zero, 8(t0)
    jal     ra, heuristic
    mv      s9, a0
.Lsolve_iteration:
    li      t0, 11
    bltu    t0, s9, .Lsolve_failed
    mv      a0, a4
    mv      a1, a5
    mv      a2, s9
    jal     ra, search
    li      t0, -1
    beq     a0, t0, .Lsolve_found
    li      t0, 0x7fffffff
    beq     a0, t0, .Lsolve_failed
    mv      s9, a0
    j       .Lsolve_iteration
.Lsolve_found:
    li      a0, 1
    jalr    zero, 0(a6)
.Lsolve_failed:
    li      a0, 0
    jalr    zero, 0(a6)
.size solve, . - solve


/* a0/a1 = preserved root coordinates; return a0 = replay success (1/0).
 * Replay reads the solution without changing it. Like search, this internal
 * routine uses s registers for active state and t6 for its return PC.
 */
.type replay_solution, @function
replay_solution:
    mv      t6, ra
    mv      s0, a0
    mv      s1, a1
    la      s2, solution_path
    la      t0, solution_length
    lw      s3, 0(t0)
    li      t0, 11
    bltu    t0, s3, .Lreplay_failed

.Lreplay_move:
    beqz    s3, .Lreplay_finished
    lbu     s4, 0(s2)
    li      t0, 9
    bgeu    s4, t0, .Lreplay_failed

    /* Subtract each preceding face's three encodings. The remainder is
     * 0/1/2, so adding one gives the base quarter-turn count 1/2/3.
     */
    li      a0, 0
    li      t0, 3
    bltu    s4, t0, .Lreplay_decoded
    addi    s4, s4, -3
    li      a0, 1
    bltu    s4, t0, .Lreplay_decoded
    addi    s4, s4, -3
    li      a0, 2
.Lreplay_decoded:
    addi    s4, s4, 1
    jal     ra, transition_rows
    mv      s10, a0
    mv      s11, a1

.Lreplay_quarter:
    mv      a0, s0
    mv      a1, s1
    jal     ra, quarter_transition
    mv      s0, a0
    mv      s1, a1
    addi    s4, s4, -1
    bnez    s4, .Lreplay_quarter
    addi    s2, s2, 1
    addi    s3, s3, -1
    j       .Lreplay_move

.Lreplay_finished:
    /* An empty solution succeeds exactly when the root is solved. */
    or      t0, s0, s1
    sltiu   a0, t0, 1
    j       .Lreplay_store
.Lreplay_failed:
    li      a0, 0
.Lreplay_store:
    la      t0, validation_result
    sw      a0, 0(t0)
    jalr    zero, 0(t6)
.size replay_solution, . - replay_solution


/* ============================================================
 * Program entry
 * ============================================================ */
.globl _start
.type _start, @function

_start:
    /* Clear solution length. */
    la      t0, solution_length
    sw      zero, 0(t0)
    la      t0, validation_result
    sw      zero, 0(t0)


    /* --------------------------------------------------------
     * Compute permutation rank from cube_input[0..6].
     * -------------------------------------------------------- */
    la      a0, cube_input
    jal     ra, rank_permutation

    la      t0, perm_rank
    sw      a0, 0(t0)


    /* --------------------------------------------------------
     * Compute orientation rank from cube_input[7..13].
     * -------------------------------------------------------- */
    la      a0, cube_input
    addi    a0, a0, 7
    jal     ra, rank_orientation

    la      t0, ori_rank
    sw      a0, 0(t0)


    /* Run IDA* using the already tested input coordinates. */
    la      t0, perm_rank
    lw      a0, 0(t0)
    la      t0, ori_rank
    lw      a1, 0(t0)
    jal     ra, solve

    /* Failed searches leave validation_result zero. Successful searches
     * replay from the original ranks, never from the search's final state.
     */
    beqz    a0, .Lprogram_exit
    la      t0, perm_rank
    lw      a0, 0(t0)
    la      t0, ori_rank
    lw      a1, 0(t0)
    jal     ra, replay_solution

/* Stop Ripes after solving so CLI instruction measurement terminates. */
.Lprogram_exit:
    li      a7, 10
    ecall

.size _start, . - _start

/* GNU builds default to the frozen CLI program. GUI builds use
 * -DSOLVER_RENDER=1 and link LED_MATRIX_0_BASE/WIDTH/HEIGHT from the
 * actual Ripes I/O symbol panel (--defsym); no MMIO address is baked in.
 * Load that ELF in Ripes: its native assembler does not support the GNU
 * macros/directives already used by this source. */
#ifdef SOLVER_RENDER
.equ RENDER, SOLVER_RENDER
#else
.equ RENDER, 0
#endif
.option norvc
.option norelax

#ifndef SOLVER_CUBE_INPUT
#define SOLVER_CUBE_INPUT "21345671111111"
#endif

/* ============================================================
 * Read-only data
 * ============================================================ */
.section .rodata,"a",@progbits
.balign 1

.globl cube_input
.type cube_input, @object
cube_input:
    .ascii SOLVER_CUBE_INPUT
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

.if RENDER
/* Same zero-based p[7], o[7] as my_solver.c; corner 0 is implicit/fixed. */
.type render_cube, @object
render_cube:
    .space 14
.size render_cube, . - render_cube
.type render_next, @object
render_next:
    .space 14
.size render_next, . - render_next
.balign 4
.globl render_moves
.type render_moves, @object
render_moves:
    .space 4
.size render_moves, . - render_moves
.globl render_validation_result
.type render_validation_result, @object
render_validation_result:
    .space 4
.size render_validation_result, . - render_validation_result
.endif


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
 *   search caches hp_table/ho_table in t3/t4, preserved by its helpers.
 *   After its cold root heuristic, search caches transition bases in a2/a3.
 *   t5 is the explicit-frame cursor: search_frames + 32 * active depth.
 *   a7 points to solution_path + active depth, updated only on push/pop.
 *   After the cold root call, ra holds 3; the return PC remains in t6.
 *   a1 holds the maximum depth 11 until search returns.
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

/* Inline row selection at both search sites. The fixed face-major layout
 * stays unchanged; a2/a3 contain the cached permutation/orientation bases.
 * Macro expansion adds no calls, stack traffic, or new lookup tables.
 */
.macro search_transition_rows
    mv      s10, a2
    mv      s11, a3
    beqz    s5, .Lsearch_rows_done\@
    li      t1, 10080
    add     s10, s10, t1
    addi    s11, s11, 1458
    li      t2, 1
    beq     s5, t2, .Lsearch_rows_done\@
    add     s10, s10, t1
    addi    s11, s11, 1458
.Lsearch_rows_done\@:
.endm

/* a0 = root p, a1 = root o, a2 = bound.
 * Return a0 = -1 (FOUND), or the minimum exceeded f / INT_MAX.
 * Active node:
 *   s0 depth; s1 p; s2 o; s3 quarter_p; s4 quarter_o;
 *   s5 face; s6 turn; s7 previous; s8 minimum; s9 bound;
 *   s10 permutation row; s11 orientation row; t3 hp base; t4 ho base.
 *   a2 permutation table base; a3 orientation table base.
 *   t5 points to the current depth's frame slot, updated only on push/pop.
 *   a7 points to the current depth's solution_path byte.
 *   ra is the constant 3; there are no calls in the inner search loop.
 *   a1 is the constant maximum depth 11.
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

    /* Cache packed table bases once per expanded search root. */
    la      t3, hp_table
    la      t4, ho_table
    la      a2, perm_move_table
    la      a3, ori_move_table
    la      t5, search_frames
    la      a7, solution_path
    li      ra, 3
    li      a1, 11

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
    bne     s6, ra, .Lsearch_face
.Lsearch_advance_face:
    addi    s5, s5, 1
    li      s6, 0
.Lsearch_face:
    bne     s5, ra, .Lsearch_next_face
    beqz    s0, .Lsearch_exhausted

    /* Return an exhausted child's minimum to its suspended parent. */
    mv      t0, s8
    addi    s0, s0, -1
    addi    t5, t5, -32
    addi    a7, a7, -1
    lw      s1, 0(t5)
    lw      s2, 4(t5)
    lw      s3, 8(t5)
    lw      s4, 12(t5)
    lw      s5, 16(t5)
    lw      s6, 20(t5)
    lw      s7, 24(t5)
    lw      s8, 28(t5)
    bgeu    t0, s8, .Lsearch_restored
    mv      s8, t0
.Lsearch_restored:
    /* A saved turn is 1..3: resume directly without root-loop checks. */
    bgeu    s6, ra, .Lsearch_advance_face
    /* A completed face does not need its row pointers restored. */
    search_transition_rows
    j       .Lsearch_generate

.Lsearch_next_face:
    bnez    s6, .Lsearch_generate
    bne     s5, s7, .Lsearch_select_rows
    /* Same-face pruning skips all three turns at once. */
    addi    s5, s5, 1
    j       .Lsearch_loop
.Lsearch_select_rows:
    search_transition_rows
    mv      s3, s1
    mv      s4, s2

.Lsearch_generate:
    /* Reuse the preceding quarter turn for half/inverse children. */
    slli    t0, s3, 1
    add     t0, s10, t0
    lhu     s3, 0(t0)
    slli    t0, s4, 1
    add     t0, s11, t0
    lhu     s4, 0(t0)
    slli    t0, s5, 1
    add     t0, t0, s5
    add     t0, t0, s6
    sb      t0, 0(a7)
    addi    s6, s6, 1

    /* Inline the child heuristic; cold root/solve calls keep the helper.
     * Preserve its nibble convention and max comparison exactly.
     */
    srli    t0, s3, 1
    add     t0, t3, t0
    lbu     t2, 0(t0)
    andi    t1, s3, 1
    slli    t1, t1, 2
    srl     t2, t2, t1
    andi    t2, t2, 15
    srli    t0, s4, 1
    add     t0, t4, t0
    lbu     a0, 0(t0)
    andi    t1, s4, 1
    slli    t1, t1, 2
    srl     a0, a0, t1
    andi    a0, a0, 15
    bgeu    a0, t2, .Lsearch_child_heuristic_done
    mv      a0, t2
.Lsearch_child_heuristic_done:
    /* Keep child depth in t0; a0 holds f until cutoff handling finishes. */
    addi    t0, s0, 1
    add     a0, t0, a0
    bltu    s9, a0, .Lsearch_cutoff
    or      t1, s3, s4
    beqz    t1, .Lsearch_child_goal
    beq     t0, a1, .Lsearch_loop

    /* Only an expanded child suspends its parent. Frame layout:
     * +0 p, +4 o, +8 quarter_p, +12 quarter_o, +16 face,
     * +20 turn, +24 previous, +28 minimum; stride = 32 bytes.
     */
    sw      s1, 0(t5)
    sw      s2, 4(t5)
    sw      s3, 8(t5)
    sw      s4, 12(t5)
    sw      s5, 16(t5)
    sw      s6, 20(t5)
    sw      s7, 24(t5)
    sw      s8, 28(t5)
    addi    t5, t5, 32
    addi    s0, s0, 1
    addi    a7, a7, 1
    mv      s1, s3
    mv      s2, s4
    mv      s7, s5
    li      s5, 0
    li      s6, 0
    li      s8, 0x7fffffff
    j       .Lsearch_loop

.Lsearch_cutoff:
    bgeu    a0, s8, .Lsearch_loop
    mv      s8, a0
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

.if RENDER
    /* Search and ranked replay are complete before any LED writes. */
    beqz    a0, .Lprogram_exit
    jal     ra, render_solution
.endif

/* Stop Ripes after solving so CLI instruction measurement terminates. */
.Lprogram_exit:
    li      a7, 10
    ecall

.size _start, . - _start


.if RENDER
/* ============================================================
 * Renderer only. No code/data/symbol references below survive RENDER=0.
 * Build using the LED_MATRIX_0_* symbols exported by the GUI's actual
 * 35x25 device. Each LED is RGB in bits 23:0 of a row-major word.
 *
 * Net face origins: U(9,2), L(0,9), F(9,9), R(18,9), B(27,9), D(9,16).
 * Each face is 8x6; each sticker is 4x3. Separators: x=8,17,26,
 * y=8,15. Two padding rows above and three below the 20-row net.
 *
 * Corner labels follow README.md and the C model:
 * 0 UFL, 1 URF, 2 DFR, 3 DLF, 4 UBR, 5 DRB, 6 DBL, 7 ULB.
 * Ordered sticker triples have consistent handedness. For destination
 * slot k and C twist o, color = cubie_colors[cubie][(k+o) mod 3].
 * These are geometry/palette tables, never a sequence of saved pictures.
 * ============================================================ */
#ifndef SOLVER_RENDER_DELAY
#define SOLVER_RENDER_DELAY 5000000
#endif
.equ RENDER_DELAY, SOLVER_RENDER_DELAY

.section .rodata,"a",@progbits
.balign 4
render_palette:
    /* U white, D yellow, F green, B blue, L orange, R red. */
    .word 0xffffff, 0xffff00, 0x00cc44, 0x2266ff, 0xff8800, 0xff2222
render_cubie_colors:
    .byte 0,2,4, 0,5,2, 1,2,5, 1,4,2
    .byte 0,3,5, 1,5,3, 1,3,4, 0,4,3
/* Verbatim C source[3][7] and twist[3][7]: destination takes source. */
render_sources:
    .byte 1,4,2,0,3,5,6
    .byte 0,1,2,4,5,6,3
    .byte 0,2,5,3,1,4,6
render_twists:
    .byte 1,2,0,2,1,0,0
    .byte 0,0,0,1,2,1,2
    .byte 0,0,0,0,0,0,0
/* (corner, corner sticker slot, pixel x, pixel y); TL/TR/BL/BR. */
render_facelets:
    .byte 7,0,9,2,  4,0,13,2,  0,0,9,5,   1,0,13,5    /* U */
    .byte 7,1,0,9,  0,2,4,9,   6,2,0,12,  3,1,4,12    /* L */
    .byte 0,1,9,9,  1,2,13,9,  3,2,9,12,  2,1,13,12   /* F */
    .byte 1,1,18,9, 4,2,22,9,  2,2,18,12, 5,1,22,12   /* R */
    .byte 4,1,27,9, 7,2,31,9,  5,2,27,12, 6,1,31,12   /* B */
    .byte 3,0,9,16, 2,0,13,16, 6,0,9,19,  5,0,13,19   /* D */

.section .text,"ax",@progbits
.balign 4

/* a0=x, a1=y, a2=RGB. Clobbers t0..t2 only. Use the WIDTH symbol;
 * 35*y = (y<<5)+(y<<1)+y. Refuse a different GUI matrix size. */
.if LED_MATRIX_0_WIDTH != 35
.error "Renderer requires LED Matrix Width=35"
.endif
.if LED_MATRIX_0_HEIGHT != 25
.error "Renderer requires LED Matrix Height=25"
.endif
.type set_pixel, @function
set_pixel:
    slli    t0, a1, 5
    slli    t1, a1, 1
    add     t0, t0, t1
    add     t0, t0, a1
    add     t0, t0, a0
    slli    t0, t0, 2
    li      t2, LED_MATRIX_0_BASE
    add     t0, t2, t0
    sw      a2, 0(t0)
    ret
.size set_pixel, . - set_pixel

.type clear_matrix, @function
clear_matrix:
    li      t0, LED_MATRIX_0_BASE
    li      t1, LED_MATRIX_0_HEIGHT
.Lclear_row:
    li      t2, LED_MATRIX_0_WIDTH
.Lclear_pixel:
    sw      zero, 0(t0)
    addi    t0, t0, 4
    addi    t2, t2, -1
    bnez    t2, .Lclear_pixel
    addi    t1, t1, -1
    bnez    t1, .Lclear_row
    ret
.size clear_matrix, . - clear_matrix

/* Reconstruct the ORIGINAL cube_input, not search/replay's final ranks. */
.type construct_concrete_cube, @function
construct_concrete_cube:
    la      t0, cube_input
    la      t1, render_cube
    li      t2, 14
.Lconstruct_byte:
    lbu     t3, 0(t0)
    addi    t3, t3, -49
    sb      t3, 0(t1)
    addi    t0, t0, 1
    addi    t1, t1, 1
    addi    t2, t2, -1
    bnez    t2, .Lconstruct_byte
    ret
.size construct_concrete_cube, . - construct_concrete_cube

/* a0=actual move byte 0..8. Repeated C quarter turns, with a 14-byte
 * scratch state to avoid overwriting a source cubie prematurely.
 * Leaf routine: all s registers and ra survive; a and t registers are scratch. */
.type apply_concrete_move, @function
apply_concrete_move:
    li      a1, 0
    li      t0, 3
    bltu    a0, t0, .Lconcrete_decoded
    addi    a0, a0, -3
    li      a1, 1
    bltu    a0, t0, .Lconcrete_decoded
    addi    a0, a0, -3
    li      a1, 2
.Lconcrete_decoded:
    addi    t6, a0, 1
    slli    t0, a1, 3
    sub     t0, t0, a1     /* face * 7 */
    la      a4, render_sources
    add     a4, a4, t0
    la      a5, render_twists
    add     a5, a5, t0
    la      a2, render_cube
    la      a3, render_next
.Lconcrete_quarter:
    li      a7, 0
.Lconcrete_cubie:
    add     t0, a4, a7
    lbu     t1, 0(t0)
    add     t2, a2, t1
    lbu     t3, 0(t2)
    add     t4, a3, a7
    sb      t3, 0(t4)
    lbu     t3, 7(t2)
    add     t0, a5, a7
    lbu     t1, 0(t0)
    add     t3, t3, t1
    li      t0, 3
    bltu    t3, t0, .Lconcrete_reduced
    addi    t3, t3, -3
.Lconcrete_reduced:
    sb      t3, 7(t4)
    addi    a7, a7, 1
    li      t0, 7
    bltu    a7, t0, .Lconcrete_cubie
    li      a7, 0
.Lconcrete_copy:
    add     t0, a3, a7
    lbu     t1, 0(t0)
    add     t2, a2, a7
    sb      t1, 0(t2)
    addi    a7, a7, 1
    li      t0, 14
    bltu    a7, t0, .Lconcrete_copy
    addi    t6, t6, -1
    bnez    t6, .Lconcrete_quarter
    ret
.size apply_concrete_move, . - apply_concrete_move

/* Clobbers s4..s8 and a/t registers; preserves render_solution's s0..s3.
 * Every sticker derives its color from the live concrete corner state. */
.type draw_cube, @function
draw_cube:
    mv      s8, ra
    la      s4, render_facelets
    li      s5, 24
    la      s6, render_cube
    la      s7, render_palette
.Ldraw_sticker:
    lbu     t0, 0(s4)      /* corner position 0..7 */
    lbu     t1, 1(s4)      /* sticker slot 0..2 */
    beqz    t0, .Ldraw_fixed_corner
    add     t2, s6, t0
    lbu     t0, -1(t2)     /* zero-based physical cubie */
    addi    t0, t0, 1
    lbu     t3, 6(t2)      /* twist at the same position */
    add     t1, t1, t3
    li      t3, 3
    bltu    t1, t3, .Ldraw_fixed_corner
    addi    t1, t1, -3
.Ldraw_fixed_corner:
    slli    t2, t0, 1
    add     t2, t2, t0
    add     t2, t2, t1
    la      t3, render_cubie_colors
    add     t2, t2, t3
    lbu     t0, 0(t2)
    slli    t0, t0, 2
    add     t0, s7, t0
    lw      a2, 0(t0)
    lbu     a5, 2(s4)      /* rectangle origin x */
    lbu     a6, 3(s4)      /* rectangle origin y */
    li      a3, 0
.Ldraw_sticker_row:
    li      a4, 0
.Ldraw_sticker_pixel:
    add     a0, a5, a4
    add     a1, a6, a3
    jal     ra, set_pixel
    addi    a4, a4, 1
    li      t0, 4
    bltu    a4, t0, .Ldraw_sticker_pixel
    addi    a3, a3, 1
    li      t0, 3
    bltu    a3, t0, .Ldraw_sticker_row
    addi    s4, s4, 4
    addi    s5, s5, -1
    bnez    s5, .Ldraw_sticker
    jalr    zero, 0(s8)
.size draw_cube, . - draw_cube

.type render_delay, @function
render_delay:
    li      t0, RENDER_DELAY
    beqz    t0, .Ldelay_done
.Ldelay_loop:
    addi    t0, t0, -1
    bnez    t0, .Ldelay_loop
.Ldelay_done:
    ret
.size render_delay, . - render_delay

/* This internal routine runs after ranked replay and owns s0..s8.
 * Initial frame, then exactly one redraw per solution_path byte.
 * Independent concrete solved check is exposed for GUI inspection. */
.type render_solution, @function
render_solution:
    mv      s3, ra
    la      s0, solution_path
    la      t0, solution_length
    lw      s1, 0(t0)
    li      s2, 0
    la      t0, render_moves
    sw      zero, 0(t0)
    la      t0, render_validation_result
    sw      zero, 0(t0)
    jal     ra, construct_concrete_cube
    jal     ra, clear_matrix
    jal     ra, draw_cube
    jal     ra, render_delay
.Lrender_move:
    beqz    s1, .Lrender_finished
    lbu     a0, 0(s0)
    jal     ra, apply_concrete_move
    jal     ra, draw_cube
    addi    s0, s0, 1
    addi    s1, s1, -1
    addi    s2, s2, 1
    la      t0, render_moves
    sw      s2, 0(t0)
    jal     ra, render_delay
    j       .Lrender_move
.Lrender_finished:
    la      t0, render_cube
    li      t1, 0
    li      a0, 0
.Lrender_check_cubie:
    lbu     t2, 0(t0)
    bne     t2, t1, .Lrender_checked
    lbu     t2, 7(t0)
    bnez    t2, .Lrender_checked
    addi    t0, t0, 1
    addi    t1, t1, 1
    li      t2, 7
    bltu    t1, t2, .Lrender_check_cubie
    li      a0, 1
.Lrender_checked:
    la      t0, render_validation_result
    sw      a0, 0(t0)
    jalr    zero, 0(s3)
.size render_solution, . - render_solution
.endif

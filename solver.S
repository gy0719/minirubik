.equ RENDER, 0
.option norvc
.option norelax

.section .rodata,"a",@progbits
.balign 1
.globl cube_input
.type cube_input, @object
cube_input:
    .ascii "12345671111111"
cube_input_end:
    .byte 0
.size cube_input, . - cube_input

.if (cube_input_end - cube_input) != 14
.error "cube_input must contain exactly 14 characters"
.endif

.section .bss,"aw",@nobits
.balign 4
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

.balign 4
.globl search_frames
.type search_frames, @object
search_frames:
    .space 384
.size search_frames, . - search_frames

.section .text,"ax",@progbits
.balign 4
.globl _start
.type _start, @function
_start:
    la t0, solution_length
    sw zero, 0(t0)
1:
    j 1b
.size _start, . - _start

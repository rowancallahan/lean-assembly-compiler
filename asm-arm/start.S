// Unverified bare-metal harness (QEMU virt, EL1, MMU off): n (8 bytes LE) at INPUT-8, bytes at INPUT.
    .section .text.start
    .globl _start
_start:
    ldr  x0, =0x40300000
    ldur x1, [x0, #-8]
    ldr  x2, =0x44000000
    ldr  x3, =0x48000000
    bl   sort
halt:
    b    halt
    .ltorg

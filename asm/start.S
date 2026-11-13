# Unverified bare-metal harness: n (8 bytes LE) at INPUT-8, bytes at INPUT.
    .section .text.start
    .globl _start
_start:
    li   a0, 0x80100000
    ld   a1, -8(a0)
    li   a2, 0x84000000
    li   a3, 0x88000000
    call sort
    lla  t0, tohost          # Sail/HTIF: write 1 = exit(0); plain RAM under QEMU virt
    li   t1, 1
    sd   t1, 0(t0)
halt:
    j    halt
    .section .tohost,"aw"
    .globl tohost
    .globl fromhost
    .align 6
tohost:   .dword 0
fromhost: .dword 0

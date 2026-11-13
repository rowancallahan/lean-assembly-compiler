.section .text.start
.globl _start
_start:
  lla t6, args
  ld a0, 0(t6)
  ld a1, 8(t6)
  ld a2, 16(t6)
  ld a3, 24(t6)
  jal ra, func
  lla t6, result
  sd a0, 0(t6)
  lla t0, tohost
  li t1, 1
  sd t1, 0(t0)
halt: j halt
.text
func:
  .word 0x00a002b3
  .word 0x00b00333
  .word 0x406282b3
  .word 0x00c00333
  .word 0x00000393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00737333
  .word 0x0062c2b3
  .word 0x00d00333
  .word 0x00000393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00139393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00139393
  .word 0x00139393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00139393
  .word 0x00138393
  .word 0x00139393
  .word 0x00139393
  .word 0x00736333
  .word 0x406282b3
  .word 0x00500533
  .word 0x00008067

.section .tohost,"aw"
.globl tohost
.globl fromhost
.align 6
tohost: .dword 0
fromhost: .dword 0
.data
args: .dword 0xc4647159c324c985, 0xe6c3f3391a2b8f1f, 0x0, 0xafbd67f9619699cf
result: .dword 0x5555555555555555

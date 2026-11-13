# sort(a0=in, a1=n, a2=scratch, a3=out): stable bottom-up merge sort of n bytes (unsigned <=).
# RV64I only, leaf, no stack, clobbers only t0-t6,a4-a7.
    .text
    .globl sort
sort:
    li   t0, 0
copy_in:                      # out[0..n) := in[0..n)
    bgeu t0, a1, copy_in_done
    add  t1, a0, t0
    lbu  t2, 0(t1)
    add  t1, a3, t0
    sb   t2, 0(t1)
    addi t0, t0, 1
    j    copy_in
copy_in_done:
    mv   t3, a3               # src
    mv   t4, a2               # dst
    li   t5, 1                # width
outer:
    bgeu t5, a1, done
    li   t6, 0                # lo
pass:
    bgeu t6, a1, pass_done
    add  a4, t6, t5           # mid = min(lo+width, n)
    bgeu a1, a4, 1f
    mv   a4, a1
1:  add  a5, a4, t5           # hi = min(mid+width, n)
    bgeu a1, a5, 1f
    mv   a5, a1
1:  mv   t0, t6               # i
    mv   t1, a4               # j
    mv   t2, t6               # k
merge:
    bgeu t2, a5, merge_done
    bgeu t0, a4, take_r
    bgeu t1, a5, take_l
    add  a6, t3, t0
    lbu  a6, 0(a6)
    add  a7, t3, t1
    lbu  a7, 0(a7)
    bltu a7, a6, take_r       # right only if strictly smaller (stable)
take_l:
    add  a6, t3, t0
    lbu  a6, 0(a6)
    addi t0, t0, 1
    j    store
take_r:
    add  a6, t3, t1
    lbu  a6, 0(a6)
    addi t1, t1, 1
store:
    add  a7, t4, t2
    sb   a6, 0(a7)
    addi t2, t2, 1
    j    merge
merge_done:
    mv   t6, a5
    j    pass
pass_done:
    mv   a6, t3
    mv   t3, t4
    mv   t4, a6
    slli t5, t5, 1
    j    outer
done:
    beq  t3, a3, finish
    li   t0, 0
copy_out:
    bgeu t0, a1, finish
    add  t1, t3, t0
    lbu  t2, 0(t1)
    add  t1, a3, t0
    sb   t2, 0(t1)
    addi t0, t0, 1
    j    copy_out
finish:
    ret

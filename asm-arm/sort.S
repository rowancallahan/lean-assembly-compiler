// sort(x0=in, x1=n, x2=scratch, x3=out): stable bottom-up merge sort of n bytes (unsigned <=).
// AArch64, leaf, no stack, clobbers only x4-x15 and flags.
    .text
    .globl sort
sort:
    mov  x4, #0
copy_in:                      // out[0..n) := in[0..n)
    cmp  x4, x1
    b.hs copy_in_done
    ldrb w5, [x0, x4]
    strb w5, [x3, x4]
    add  x4, x4, #1
    b    copy_in
copy_in_done:
    mov  x6, x3               // src
    mov  x7, x2               // dst
    mov  x8, #1               // width
outer:
    cmp  x8, x1
    b.hs done
    mov  x9, #0               // lo
pass:
    cmp  x9, x1
    b.hs pass_done
    add  x10, x9, x8          // mid = min(lo+width, n)
    cmp  x1, x10
    b.hs 1f
    mov  x10, x1
1:  add  x11, x10, x8         // hi = min(mid+width, n)
    cmp  x1, x11
    b.hs 1f
    mov  x11, x1
1:  mov  x12, x9              // i
    mov  x13, x10             // j
    mov  x14, x9              // k
merge:
    cmp  x14, x11
    b.hs merge_done
    cmp  x12, x10
    b.hs take_r
    cmp  x13, x11
    b.hs take_l
    ldrb w4, [x6, x12]
    ldrb w5, [x6, x13]
    cmp  w5, w4
    b.lo take_r               // right only if strictly smaller (stable)
take_l:
    ldrb w4, [x6, x12]
    add  x12, x12, #1
    b    store
take_r:
    ldrb w4, [x6, x13]
    add  x13, x13, #1
store:
    strb w4, [x7, x14]
    add  x14, x14, #1
    b    merge
merge_done:
    mov  x9, x11
    b    pass
pass_done:
    mov  x4, x6
    mov  x6, x7
    mov  x7, x4
    lsl  x8, x8, #1
    b    outer
done:
    cmp  x6, x3
    b.eq finish
    mov  x4, #0
copy_out:
    cmp  x4, x1
    b.hs finish
    ldrb w5, [x6, x4]
    strb w5, [x3, x4]
    add  x4, x4, #1
    b    copy_out
finish:
    ret

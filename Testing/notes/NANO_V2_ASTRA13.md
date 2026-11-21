# Astra round 13 — growable buffers (ADVICE; owner may override)

Relayed advice, not owner decisions. Lean interface: `NANO_V2_ASTRA13_Grow.lean` (type-checks on Lean 4.29 as given).

Policy: geometric growth on the existing bump heap. `bnew` = header only (len 0, cap 0, 16 bytes). Full `bpush`:
cap 0→1, then double; copy live words to a fresh block at t5, append, return the NEW address. Old block leaked
(never reused). One-word buffer ABI unchanged; no free list. Later options: per-buffer capacity hint for the one
huge buffer (≈ halves its use); stage reset only with a proof that survivors lie outside. Keep "max logical length
κ → −2" separate from "heap exhausted"; if −2 at κ must stay, check len == κ first and clamp the last growth.

Ownership invariant: each live buffer has exactly one owning location holding its block address; distinct owners
have disjoint capacity-sized footprints (incl. headers); all live blocks end ≤ t5; borrows expire before consuming
ops; the fresh block is private until commit. CONSEQUENCE: every bpush call site must use the RETURNED pointer,
including CONTINUE staging. Test: a push that relocates inside a loop, then read the appended element next iteration.

Heap/stack: use a fixed heap/stack partition with ceiling H, check stack growth against the same boundary.

bnew (after space check H - t5 ≥ 16): a0 := t5; sd 0 → len, cap; t5 += 16.
bpush:
```asm
    ld    t0, 0(a0)           # len
    ld    t1, 8(a0)           # cap
    bltu  t0, t1, append
    sub   t2, H, t5
    srli  t2, t2, 3
    li    t3, 2
    bltu  t2, t3, fail
    addi  t2, t2, -2
    beqz  t1, first
    srli  t3, t2, 1
    bltu  t3, t1, fail
    slli  t1, t1, 1
    j     reserve
first:
    beqz  t2, fail
    li    t1, 1
reserve:
    mv    t2, t5
    sd    t1, 8(t2)
    addi  t3, a0, 16
    addi  t4, t2, 16
    mv    a2, t0
copy:
    beqz  a2, copied
    ld    a3, 0(t3)
    sd    a3, 0(t4)
    addi  t3, t3, 8
    addi  t4, t4, 8
    addi  a2, a2, -1
    j     copy
copied:
    slli  t3, t1, 3
    add   t5, t2, t3
    addi  t5, t5, 16
    mv    a0, t2
append:
    slli  t3, t0, 3
    add   t3, a0, t3
    sd    a1, 16(t3)
    addi  t0, t0, 1
    sd    t0, 0(a0)
```
All checks precede the first store; on failure t5 and memory unchanged. NOTE (ours): this template uses a2/a3 as
scratch — in C's convention a2 = work base and a3 = output, so pick other scratch registers.
Copy-loop invariant: after j iterations fresh prefix = first j source words, source unchanged, cursors = bases + 8j.

Heap bound per buffer LIFETIME (one per executed bnew): L = 0 → 2 words; L ≥ 1, k = ⌈log₂ L⌉ →
2^(k+1) + 2k + 3 words. L = 2^20 → 2,097,195 words (≈ 16 MiB); L = 10 → 43 words. Sum over lifetimes × 8 bytes.

Proof: GrowCorrect (fresh block at old top, BufferRep (xs ++ [v]) at nextCap c, memory outside the new footprint
unchanged) ⇒ every other live buffer frames; replace only the consumed owner's (xs, ptr, cap) in LiveRep.

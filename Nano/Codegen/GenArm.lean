/- Nano/Codegen: NATIVE AArch64 CODE GENERATOR (PROTOTYPE, UNPROVEN, not part of the proven compiler).
Same structure as `Gen` (one fuel loop over an explicit work stack, the same work items, label fixups by `bset`, the
same width pre-pass `g53`, the same frame layout, stubs at words 1–5 / 6–10 and start word 0), but every template
is emitted as AArch64 words directly (no RISC-V words, no rv2arm blocks).  Register map = rv2arm's (`armMapping`):
RV t0 t1 t2 s0 a4 a5 = x5 x6 x7 x8 x14 x15, t3/t4 (input base/length) = x12/x13, t5 (heap top) = x10,
t6 (expression stack) = x11, ra = x30, a0..a3 = x0..x3, sp (work top) = x4.  Scratch: x16, x17.  No emitted word
has a register field 31 (no xzr, no sp); x9, x18..x29 are never touched.  Notes and tests: `Testing/nano/v2self/native_arm/README.md`. -/
import Nano.Codegen.Gen
namespace C

/-! ## A64 encoders (64-bit forms).  Bases: add imm 2432696320, sub imm 3506438144, add reg 2332033024,
sub reg 3405774848, subs reg 3942645760, and 2315255808, orr 2852126720, eor 3388997632, lslv 2596282368,
lsrv 2596283392, madd 2600468480, movz 3531603968, movk 4068474880, movn 2457862144, ldr 4181721088,
str 4177526784, ldur 4164943872, stur 4160749568, ldp 2839543808, b 335544320, bl 2483027968, b.cond 1409286144,
cbnz 3036676096, cbz 3019898880, br 3592355840 (br x30 = 3592356800 is the return) -/
/-! (`|||`/`&&&` take no bare numerals: the bases are named, as in Gen) -/
def a_1 : UInt64 := 2432696320
def a_2 : UInt64 := 3506438144
def a_3 : UInt64 := 2332033024
def a_4 : UInt64 := 3405774848
def a_5 : UInt64 := 3942645760
def a_6 : UInt64 := 2315255808
def a_7 : UInt64 := 2852126720
def a_8 : UInt64 := 3388997632
def a_9 : UInt64 := 2596282368
def a_10 : UInt64 := 2596283392
def a_11 : UInt64 := 2600468480
def a_12 : UInt64 := 3531603968
def a_13 : UInt64 := 4068474880
def a_14 : UInt64 := 2457862144
def a_15 : UInt64 := 4181721088
def a_16 : UInt64 := 4177526784
def a_17 : UInt64 := 4164943872
def a_18 : UInt64 := 4160749568
def a_19 : UInt64 := 2839543808
def a_20 : UInt64 := 335544320
def a_21 : UInt64 := 2483027968
def a_22 : UInt64 := 1409286144
def a_23 : UInt64 := 3036676096
def a_24 : UInt64 := 3019898880
def a_26 : UInt64 := 3592355840
def a_28 : UInt64 := 945842176
def a_29 : UInt64 := 956301312
def a_30 : UInt64 := 65535
def a_31 : UInt64 := 511
def a_32 : UInt64 := 7
def a_33 : UInt64 := 524287
def a_34 : UInt64 := 67108863

/-- add d, n, #v (v < 4096) -/
def a1 (d n v : UInt64) : UInt64 := a_1 ||| (v <<< 10) ||| (n <<< 5) ||| d
/-- sub d, n, #v (v < 4096) -/
def a2 (d n v : UInt64) : UInt64 := a_2 ||| (v <<< 10) ||| (n <<< 5) ||| d
/-- a three-register form with base `c` -/
def a3 (c d n m : UInt64) : UInt64 := c ||| (m <<< 16) ||| (n <<< 5) ||| d
/-- movz / movk / movn (base `c`) d, #v, lsl 16j -/
def a4 (c d v j : UInt64) : UInt64 := c ||| (j <<< 21) ||| (v <<< 5) ||| d
/-- c ||| v << 10 ||| n << 5 ||| t (uimm loads/stores, madd addend, shifted add) -/
def a35 (c t n v : UInt64) : UInt64 := c ||| (v <<< 10) ||| (n <<< 5) ||| t
/-- the unscaled (ldur/stur) form, v a signed 9-bit offset -/
def a36 (c t n v : UInt64) : UInt64 := c ||| ((v &&& a_31) <<< 12) ||| (n <<< 5) ||| t
/-- ldp t, u, [n] -/
def a32 (t u n : UInt64) : UInt64 := a_19 ||| (u <<< 10) ||| (n <<< 5) ||| t
/-- subs x16, n, m (the compare; NZCV and x16 written) -/
def a33 (n m : UInt64) : UInt64 := a3 3942645760 16 n m
/-- add d, n, m, lsl #3 -/
def a34 (d n m : UInt64) : UInt64 := a35 (a3 a_3 0 0 m) d n 3

/-- the number of 16-bit chunks of `v` equal to `e` -/
def a8 (v e : UInt64) : UInt64 :=
  (if (v &&& a_30) == e then 1 else 0) + (if ((v >>> 16) &&& a_30) == e then 1 else 0)
  + (if ((v >>> 32) &&& a_30) == e then 1 else 0) + (if ((v >>> 48) &&& a_30) == e then 1 else 0)
/-- chunks j.. of `v` (v shifted right 16j) that differ from `e` (0: movz path, 65535: movn path); `f` = 1 once the first word is out -/
def a7 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, o, d, v, j, e, f => o
  | n + 1, o, d, v, j, e, f =>
    let c := v &&& a_30;
    if c == e then a7 n o d (v >>> 16) (j + 1) e f else
    if f == 1 then a7 n (bpush o (a4 4068474880 d c j)) d (v >>> 16) (j + 1) e 1 else
    if e == 0 then a7 n (bpush o (a4 3531603968 d c j)) d (v >>> 16) (j + 1) e 1 else
    a7 n (bpush o (a4 2457862144 d (65535 - c) j)) d (v >>> 16) (j + 1) e 1
/-- li d, v: one movz/movn plus a movk per remaining chunk -/
def a6 (o : Buf) (d v : UInt64) : Buf :=
  if v < 65536 then bpush o (a4 3531603968 d v 0) else
  if (g_901 - v) < 65536 then bpush o (a4 2457862144 d (g_901 - v) 0) else
  if a8 v 0 < a8 v 65535 then a7 4 o d v 0 65535 0 else a7 4 o d v 0 0 0
/-- add d, n, #v for a signed `v` (n ≠ x16) -/
def a5 (o : Buf) (d n v : UInt64) : Buf :=
  if v < 4096 then bpush o (a1 d n v) else
  if g_0 - v < 4096 then bpush o (a2 d n (g_0 - v)) else
  bpush (a6 o 16 v) (a3 2332033024 d n 16)
/-- an 8-byte load (s = 0) or store (s = 1) of t at [n + f], f signed (n ≠ x16) -/
def a9 (o : Buf) (s t n f : UInt64) : Buf :=
  if f < 32768 then (if (f &&& a_32) == 0 then
    bpush o (a35 (if s == 0 then a_15 else a_16) t n (f >>> 3)) else
    bpush (a5 o 16 n f) (a35 (if s == 0 then a_15 else a_16) t 16 0)) else
  if f + 256 < 512 then bpush o (a36 (if s == 0 then a_17 else a_18) t n f)
  else bpush (a5 o 16 n f) (a35 (if s == 0 then a_15 else a_16) t 16 0)

/-- b.cond-form word with base `c` (b.cond or cbnz/cbz) at word `h` to word `b` -/
def a16 (c h b : UInt64) : UInt64 := c ||| (((b - h) &&& a_33) <<< 5)
/-- push register d: sub x11, x11, #8; subs x16, x11, x10; b.lo OOM; str d, [x11] -/
def a10 (o : Buf) (d : UInt64) : Buf :=
  let h := bsize o;
  bpush (bpush (bpush (bpush o (a2 11 11 8)) (a33 11 10)) (a16 1409286147 (h + 2) 1)) (a35 a_16 d 11 0)
/-- pop two: x6 := top, x5 := below; x11 += k -/
def a11 (o : Buf) (k : UInt64) : Buf := bpush (bpush o (a32 6 5 11)) (a1 11 11 k)
/-- the binary op `p` (add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7 xor 8) on x5, x6 → x5, stored over the top -/
def a12 (o : Buf) (p : UInt64) : Buf :=
  let o1 := a11 o 8;
  let o2 := (if p == 3 then bpush (bpush o1 (a4 3531603968 17 0 0)) (a35 (a3 a_11 0 0 6) 5 5 17) else
    bpush o1 (if p == 1 then a3 2332033024 5 5 6 else if p == 2 then a3 3405774848 5 5 6
      else if p == 4 then a3 2315255808 5 5 6 else if p == 5 then a3 2852126720 5 5 6
      else if p == 6 then a3 2596282368 5 5 6 else if p == 7 then a3 2596283392 5 5 6 else a3 3388997632 5 5 6));
  bpush o2 (a35 4177526784 5 11 0)
/-- the prims (ISIZE 1, RD 2, LEN 3, PUT 4, BNEW 5, BSIZE 6, BGET 7, BSET 8, BPUSH 9) -/
def a13 (o : Buf) (p u : UInt64) : Buf :=
  if p == 1 then a10 o 13 else if p == 3 then a10 o 13
  else if p == 2 then
    let h := bsize o;
    bpush (bpush (bpush (bpush (bpush (bpush o (a35 4181721088 6 11 0)) (a4 3531603968 5 0 0)) (a33 6 13))
      (a16 1409286146 (h + 3) (h + 5))) (a3 945842176 5 12 6)) (a35 4177526784 5 11 0)
  else if p == 5 then
    let o1 := bpush (a6 (bpush o (a1 5 10 0)) 6 ((u + 2) <<< 3)) (a3 2332033024 6 6 10);
    let h1 := bsize o1;
    let o2 := bpush (bpush o1 (a33 11 6)) (a16 1409286147 (h1 + 1) 1);
    let o3 := bpush (bpush (a6 o2 7 u) (a4 3531603968 17 0 0)) (a35 4177526784 17 5 0);
    a10 (bpush (bpush o3 (a35 4177526784 7 5 1)) (a1 10 6 0)) 5
  else if p == 6 then
    bpush (bpush (bpush o (a35 4181721088 5 11 0)) (a35 4181721088 5 5 0)) (a35 4177526784 5 11 0)
  else if p == 7 then
    let o1 := bpush (bpush (a11 o 8) (a35 4181721088 7 5 0)) (a4 3531603968 14 0 0);
    let h := bsize o1;
    bpush (bpush (bpush (bpush (bpush o1 (a33 6 7)) (a16 1409286146 (h + 1) (h + 4))) (a34 16 5 6))
      (a35 4181721088 14 16 2)) (a35 4177526784 14 11 0)
  else if p == 8 then
    let o1 := bpush (bpush (bpush (bpush o (a32 14 6 11)) (a35 4181721088 5 11 2)) (a1 11 11 16))
      (a35 4181721088 7 5 0);
    let h := bsize o1;
    bpush (bpush (bpush (bpush o1 (a33 6 7)) (a16 1409286146 (h + 1) (h + 4))) (a34 16 5 6))
      (a35 4177526784 14 16 2)
  else
    let o1 := bpush (bpush (a11 o 8) (a32 7 14 5)) (a33 7 14);
    let h := bsize o1;
    bpush (bpush (bpush (bpush (bpush o1 (a16 1409286146 h 6)) (a34 15 5 7)) (a35 4177526784 6 15 2))
      (a1 7 7 1)) (a35 4177526784 7 5 0)

/-- the code before the defs: word 0 = b start (patched), the out-of-memory (1–5) and capacity (6–10) stubs -/
def a14 (o : Buf) : Buf :=
  let o1 := bpush (bpush (bpush (bpush (bpush (bpush o 335544320) (a4 2457862144 0 0 0)) (a4 3531603968 1 0 0))
    (a35 4181721088 30 2 0)) (a35 4181721088 8 2 1)) 3592356800;
  bpush (bpush (bpush (bpush (bpush o1 (a4 2457862144 0 1 0)) (a4 3531603968 1 0 0))
    (a35 4181721088 30 2 0)) (a35 4181721088 8 2 1)) 3592356800
/-- emit b (d = 0) or bl (d = 1) from here to word `b` (error flag if beyond ±1 MiB, as Gen) -/
def a17 (r o : Buf) (d b : UInt64) : Buf × Buf :=
  let h := bsize o;
  let w := (if d == 1 then a_21 else a_20) ||| ((b - h) &&& a_34);
  if g14 h b == 1 then (r, bpush o w) else (g16 r, bpush o w)
/-- patch the placeholder at word `p` (b, b.cond or cbnz with offset 0) to jump here -/
def a18 (r o : Buf) (p : UInt64) : Buf × Buf :=
  let h := bsize o;
  let v := bget o p;
  let w := (if (v >>> 26) == 5 then v ||| ((h - p) &&& a_34) else a16 v p h);
  if g14 p h == 1 then (r, bset o p w) else (g16 r, bset o p w)

/-- the start code (as `g35`): work under 16 bytes ⇒ x0 = −1 at once; save x30/x8, input to x12/x13, call main
(at word `w`), copy the output buffer's low bytes to [x3] -/
def a19 (r o : Buf) (w : UInt64) : Buf × Buf :=
  let o1 := bpush (bpush (bpush (bpush o (a1 10 2 16)) (a4 3531603968 16 3 0)) (a3 a_10 11 4 16)) (a3 a_9 11 11 16);
  let h1 := bsize o1;
  let o2 := bpush (bpush (bpush (bpush (bpush o1 (a33 11 10)) (a16 1409286146 (h1 + 1) (h1 + 5))) (a4 2457862144 0 0 0))
    (a4 3531603968 1 0 0)) 3592356800;
  let o9 := bpush (bpush (bpush (bpush o2 (a35 4177526784 30 2 0)) (a35 4177526784 8 2 1))
    (a1 12 0 0)) (a1 13 1 0);
  let (r1, o3) := a17 r o9 1 w;
  let o4 := bpush (bpush o3 (a35 4181721088 5 11 0)) (a35 4181721088 7 5 0);
  let h4 := bsize o4;
  let o5 := bpush (bpush (bpush (bpush o4 (a16 (a3 a_23 7 0 0) h4 (h4 + 4))) (a4 3531603968 0 1 0)) (a4 3531603968 1 0 0))
    (a3 a_20 12 0 0);
  let o6 := bpush (bpush (bpush o5 (a1 1 7 0)) (a1 6 5 16)) (a1 14 3 0);
  let h6 := bsize o6;
  let o7 := bpush (bpush (bpush (bpush (bpush (bpush o6 (a16 (a3 a_24 7 0 0) h6 (h6 + 7))) (a35 4181721088 15 6 0))
    (a35 956301312 15 14 0)) (a1 6 6 8)) (a1 14 14 1)) (a2 7 7 1);
  let o8 := bpush (bpush o7 (a_20 ||| ((h6 - bsize o7) &&& a_34))) (a4 3531603968 0 0 0);
  (r1, bpush (bpush (bpush o8 (a35 4181721088 30 2 0)) (a35 4181721088 8 2 1)) 3592356800)

/-- LOCAL s w: push the w words -/
def a20 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, s, w, o => o
  | n + 1, p, s, w, o =>
    if w == 0 then o else
    a20 n p (s + 1) (w - 1) (a10 (a9 o 0 5 8 (g24 p s)) 5)
/-- pop the top w words into slots s+w-1 … s -/
def a21 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, s, w, o => o
  | n + 1, p, s, w, o =>
    if w == 0 then o else
    a21 n p s (w - 1) (a9 (bpush (bpush o (a35 4181721088 5 11 0)) (a1 11 11 8)) 1 5 8 (g24 p (s + w - 1)))
/-- patch the def's exit jumps (fixup buffer `f`, `c` entries) to here -/
def a22 : Nat → UInt64 → Buf × (Buf × Buf) → Buf × (Buf × Buf)
  | 0, c, y6 => y6
  | n + 1, c, y6 =>
    if c == 0 then y6 else
    let (f, y7) := y6;
    let (r, o) := y7;
    let v := bget f (c - 1);
    a22 n (c - 1) (f, a18 r o v)
/-- the def epilogue: result (nres words on top) copied over the args, x11 set, x8 restored, br x14 -/
def a23 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, q, j, o => o
  | n + 1, p, q, j, o =>
    if j < q then a23 n p q (j + 1) (a9 (a9 o 0 5 11 ((q - 1 - j) <<< 3)) 1 5 8 ((p <<< 3) + g_16 - ((j + 1) <<< 3)))
    else bpush (bpush (a5 o 11 8 ((p <<< 3) + g_16 - (q <<< 3))) (a1 8 15 0)) (a3 a_26 0 14 0)

/-- visit the node at the cursor in mode `m` (as `g36`; only CONST, LOCAL and the LOOP head emit code) -/
def a24 (x r o k : Buf) (y : UInt64) : Buf × (Buf × Buf) :=
  let i := bget r 0;
  let n := bget r 6;
  let c0 := bget x i;
  let c := (if c0 < 7 then c0 else if c0 == 7 then 999 else if c0 < 12 then c0 - 1 else 999);
  let z := (if c == 4 then g_1 else if c == 5 then g_1 else if c == 10 then g_1 else g_0);
  let b := bget x (i + 1);
  let a := (if c == 3 then (if b - 1 < 8 then g_1 else g_0) else if c == 4 then (if b - 1 < 2 then g_1 else g_0)
    else if c == 8 then (if b - 1 < 9 then g_1 else g_0) else g_1);
  if a == 0 then (g16 r, (o, k)) else
  if y == 1 then
    if z == 0 then (g15 r 6 (n + 2), (o, g18 (g18 k n 9 0 0) (n + 1) 1 0 0)) else
    if c == 10 then (g15 (g15 r 0 (i + 1)) 6 (n + 2), (o, g18 (g18 k n 10 0 0) (n + 1) 1 0 0)) else
    if c == 4 then (g15 (g15 r 0 (i + 2)) 6 (n + 7),
      (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k n 5 0 0) (n + 1) 1 1 0) (n + 2) 4 0 0) (n + 3) 1 1 0) (n + 4) 3 (bget x (i + 1)) 0)
        (n + 5) 1 0 0) (n + 6) 1 0 0))
    else
    let e := g43 r (bget x (i + 1)) (bget x (i + 2));
    if e == 1 then (g16 r, (o, k)) else
    (g15 (g15 r 0 (i + 3)) 6 (n + 3),
      (o, g18 (g18 (g18 k n 1 1 0) (n + 1) 6 (bget x (i + 1)) (bget x (i + 2))) (n + 2) 1 0 0))
  else
  if c == 1 then (g15 r 0 (i + 2), (a10 (a6 o 5 (bget x (i + 1))) 5, k)) else
  if c == 2 then
    let e := g43 r (bget x (i + 1)) (bget x (i + 2));
    if e == 1 then (g16 r, (o, k)) else
    let v := a20 256 (bget r 1) (bget x (i + 1)) (bget x (i + 2)) o;
    (g15 r 0 (i + 3), (v, k)) else
  if c == 3 then (g15 (g15 r 0 (i + 2)) 6 (n + 3), (o, g18 (g18 (g18 k n 2 (bget x (i + 1)) 0) (n + 1) 1 0 0) (n + 2) 1 0 0)) else
  if c == 4 then (g15 (g15 r 0 (i + 2)) 6 (n + 7),
      (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k n 5 0 0) (n + 1) 1 0 0) (n + 2) 4 0 0) (n + 3) 1 0 0) (n + 4) 3 (bget x (i + 1)) 0)
        (n + 5) 1 0 0) (n + 6) 1 0 0)) else
  if c == 5 then
    let e := g43 r (bget x (i + 1)) (bget x (i + 2));
    if e == 1 then (g16 r, (o, k)) else
    (g15 (g15 r 0 (i + 3)) 6 (n + 3),
      (o, g18 (g18 (g18 k n 1 0 0) (n + 1) 6 (bget x (i + 1)) (bget x (i + 2))) (n + 2) 1 0 0)) else
  if c == 6 then
    let q := bget x (i + 1);
    if q < 251 then
    (g15 (g15 r 0 (i + 2)) 6 (n + q), (o, g27 256 k n q)) else (g16 r, (o, k)) else
  if c == 7 then
    let q := bget x (i + 2);
    if q < 251 then
    (g15 (g15 r 0 (i + 3)) 6 (n + 1 + q), (o, g27 256 (g18 k n 7 (bget x (i + 1)) 0) (n + 1) q)) else (g16 r, (o, k)) else
  if c == 8 then
    let p := bget x (i + 1);
    let q := g33 p;
    (g15 (g15 r 0 (i + 2)) 6 (n + 1 + q), (o, g27 256 (g18 k n 8 p 0) (n + 1) q)) else
  if c == 9 then
    if n == 1 then
    let h := bsize o;
    let o0 := a9 o 0 5 8 (g24 (bget r 1) 0);
    let h1 := bsize o0;
    let o1 := bpush o0 (a3 a_23 5 0 0);
    (g15 (g15 (g15 r 0 (i + 1)) 3 h) 6 (n + 3), (o1, g18 (g18 (g18 k n 1 1 0) (n + 1) 11 h1 0) (n + 2) 1 1 0))
    else (g16 r, (o, k))
  else (g16 r, (o, k))

/-- one work item (as `g37`) -/
def a25 (x r o k t f : Buf) : Buf × (Buf × (Buf × Buf)) :=
  let n := bget r 6 - 1;
  let c := bget k (n * 3);
  let z := bget k (n * 3 + 1);
  let y := bget k (n * 3 + 2);
  let r1 := g15 r 6 n;
  if c == 1 then
    let (r2, y1) := a24 x r1 o k z;
    let (o2, k2) := y1;
    (r2, (o2, (k2, f))) else
  if c == 2 then (r1, (a12 o z, (k, f))) else
  if c == 3 then
    let o0 := bpush (a11 o 16) (a33 5 6);
    let h := bsize o0;
    let o1 := bpush o0 (if z == 1 then 1409286145 else 1409286146);
    (r1, (o1, (bset k ((n - 2) * 3 + 1) h, f))) else
  if c == 4 then
    let h := bsize o;
    let (r2, o2) := a18 r1 (bpush o 335544320) z;
    (r2, (o2, (bset k ((n - 2) * 3 + 1) h, f))) else
  if c == 5 then
    let (r2, o2) := a18 r1 o z;
    (r2, (o2, (k, f))) else
  if c == 6 then
    let v := a21 256 (bget r1 1) z y o;
    (r1, (v, (k, f))) else
  if c == 7 then
    let (r2, o2) := (if z < bsize t then a17 r1 o 1 (bget t z) else (g16 r1, o));
    (r2, (o2, (k, f))) else
  if c == 8 then
    let u := bget r1 9;
    (r1, (a13 o z u, (k, f))) else
  if c == 9 then
    let q := bget r1 8;
    let h := bsize o;
    if 65535 < q then (g16 r1, (o, (k, f))) else
    (g15 r1 8 (q + 1), (bpush o 335544320, (k, g17 f q h))) else
  if c == 10 then
    let p := bget r1 1;
    let h := bget r1 3;
    let o1 := a21 256 p 1 (p - 1) o;
    let (r2, o2) := a17 r1 o1 0 h;
    (r2, (o2, (k, f))) else
  if c == 11 then
    let w := g24 (bget r1 1) 0;
    let (r2, o2) := a18 r1 o z;
    (r2, (a9 (bpush o2 (a2 5 5 1)) 1 5 8 w, (k, f))) else
  let i := bget r1 0;
  let r2 := (if bget x i == 21 then g15 r1 0 (i + 1) else g16 r1);
  let p := bget r2 1;
  let q := bget r2 2;
  let c2 := bget r2 8;
  let (f1, y8) := a22 65536 c2 (f, (r2, o));
  let (r3, o3) := y8;
  let o4 := a23 512 p q 0 (bpush o3 (a32 15 14 8));
  (g15 r3 8 0, (o4, (k, f1)))

/-- a def header at the cursor (as `g38`): push x30, x8; x8 := x11; reserve the locals; OOM check -/
def a26 (x r o k t : Buf) : Buf × (Buf × (Buf × Buf)) :=
  let i := bget r 0;
  let d := bget x (i + 1);
  let p := bget x (i + 2);
  let s := bget x (i + 3);
  let q := bget x (i + 5);
  let v := (if bget x i == 20 then g_1 else g_0);
  let z0 := (if s < 251 then g_1 else g_0);
  let z1 := (if p < s + 1 then z0 else g_0);
  let z2 := (if q < 251 then z1 else g_0);
  let z3 := (if d == bsize t then z2 else g_0);
  let z4 := (if v == 1 then z3 else g_0);
  if z4 == 0 then (g16 r, (o, (k, t))) else
  let r1 := g15 (g15 (g15 (g15 (g15 r 0 (i + 6)) 1 p) 7 s) 2 q) 6 2;
  let h := bsize o;
  let o1 := a10 (a10 o 30) 8;
  let o2 := bpush (bpush (a5 (bpush o1 (a1 8 11 0)) 11 11 (g_0 - ((s - p) <<< 3))) (a33 11 10)) 0;
  let h2 := bsize o2 - 1;
  (r1, (bset o2 h2 (a16 1409286147 h2 1), (g18 (g18 k 0 12 0 0) 1 1 0 0, bpush t h)))

/-- one step of the main loop: a def header (no pending items) or one work item -/
def a27 (x r o k t f : Buf) : Buf × (Buf × (Buf × (Buf × Buf))) :=
  if bget r 6 == 0 then
    let (r1, y2) := a26 x r o k t;
    let (o1, y3) := y2;
    let (k1, t1) := y3;
    (r1, (o1, (k1, (t1, f))))
  else
    let (r1, y4) := a25 x r o k t f;
    let (o1, y5) := y4;
    let (k1, f1) := y5;
    (r1, (o1, (k1, (t, f1))))

/-- the result when the main loop stops (as `g56`) -/
def a28 (r o t : Buf) : Buf × Buf :=
  if bget r 5 == 1 then (r, o) else
  if bget r 4 == 1 then (r, o) else
  if 16777215 < bsize o then (g16 r, o) else
  let w := bsize t;
  if w == 0 then (g16 r, o) else
  let m := (if bget r 1 == 0 then (if bget r 2 == 1 then g_1 else g_0) else g_0);
  if m == 0 then (g16 r, o) else
  let (r1, o1) := a18 r o 0;
  let (r2, o2) := a19 r1 o1 (bget t (w - 1));
  (g15 r2 5 1, o2)

/-- the main loop -/
def a29 : Nat → Buf → Buf → Buf → Buf → Buf → Buf → Buf × Buf
  | 0, x, r, o, k, t, f => (g16 r, o)
  | n + 1, x, r, o, k, t, f =>
    if g55 x r o == 1 then a28 r o t else
    let (r1, y) := a27 x r o k t f;
    let (o1, y1) := y;
    let (k1, y2) := y1;
    let (t1, f1) := y2;
    a29 n x r1 o1 k1 t1 f1

/-- **the native AArch64 code generator**: AST (`IRV = 2` first) → A64 machine-code bytes, or empty -/
def a30 (c : List UInt8) (x : Buf) (u : UInt64) : List UInt8 :=
  if 2147483647 < bsize x then [] else
  if bget x 0 == 2 then
    let (x2, w) := g53 x;
    if w == 0 then [] else
    let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u;
    let (r1, o) := a29 16777216 x2 r (a14 bnew) bnew bnew bnew;
    if bget r1 4 == 1 then [] else if 16777215 < bsize o then [] else if 262143 < bsize o then [] else
    g40 16777216 c o 0 []
  else []

/-- with the default buffer capacity κ = 2^19 words -/
def a31 (c : List UInt8) (x : Buf) : List UInt8 := a30 c x g_999

end C

/- Nano/V2Self/C: the FUSED CODE GENERATOR (expand + assemble, Astra round 8): the flat pre-order AST of
Testing/notes/NANO_V2_IR.md (version 2) → RV64 machine code bytes.  One fuel loop over an explicit work stack (no
recursion in S), label fixups by `bset`.  Machine (as Nano.V2B, plus frames): t6 = expression-stack pointer (8-byte
slots, downward, every push checked against t5 = heap top), s0 = frame pointer, t3/t4 = input base/length, a2 = work
base (read-only: [a2] = caller ra, [a2+8] = caller s0, heap from a2+16).  A def: args (npw words) pushed by the caller,
then `jal ra`; the callee pushes ra, s0, sets s0, reserves the locals; slot k < npw at s0+16+8(npw-1-k), slot k ≥ npw at
s0-8(k-npw+1); the result (nres words) is copied down over the args, t6 just below it.  Fuel loops: fuel = slot 0,
`CONTINUE` = compute the whole new state, then commit, then jump to the head.  Word 0 jumps to the start code; words
1–5 = out of memory (a0 = −1), 6–10 = capacity (a0 = −2).  Any unsupported form, frame over 250 words or jump beyond
±1 MiB ⇒ the EMPTY output. -/
import Nano.V2Self.C.Base
namespace C

def g_0 : UInt64 := 0
def g_1 : UInt64 := 1
def g_3 : UInt64 := 3
def g_19 : UInt64 := 19
def g_16 : UInt64 := 16
def g_31 : UInt64 := 31
def g_35 : UInt64 := 35
def g_51 : UInt64 := 51
def g_63 : UInt64 := 63
def g_99 : UInt64 := 99
def g_103 : UInt64 := 103
def g_111 : UInt64 := 111
def g_127 : UInt64 := 127
def g_15 : UInt64 := 15
def g_255 : UInt64 := 255
def g_1023 : UInt64 := 1023
def g_4095 : UInt64 := 4095
def g_901 : UInt64 := g_0 - 1
def g_902 : UInt64 := g_0 - 2
def g_908 : UInt64 := g_0 - 8
def g_999 : UInt64 := 524288

/-! ## encoders (RV64I/M) -/
def g1 (f7 f3 d a b : UInt64) : UInt64 :=
  (f7 <<< 25) ||| (b <<< 20) ||| (a <<< 15) ||| (f3 <<< 12) ||| (d <<< 7) ||| g_51
def g2 (p f3 d a v : UInt64) : UInt64 := ((v &&& g_4095) <<< 20) ||| (a <<< 15) ||| (f3 <<< 12) ||| (d <<< 7) ||| p
def g3 (f3 b a v : UInt64) : UInt64 :=
  (((v >>> 5) &&& g_127) <<< 25) ||| (b <<< 20) ||| (a <<< 15) ||| (f3 <<< 12) ||| ((v &&& g_31) <<< 7) ||| g_35
def g4 (f3 a b v : UInt64) : UInt64 :=
  (((v >>> 12) &&& g_1) <<< 31) ||| (((v >>> 5) &&& g_63) <<< 25) ||| (b <<< 20) ||| (a <<< 15) ||| (f3 <<< 12) ||| (((v >>> 1) &&& g_15) <<< 8) ||| (((v >>> 11) &&& g_1) <<< 7) ||| g_99
def g5 (d v : UInt64) : UInt64 :=
  (((v >>> 20) &&& g_1) <<< 31) ||| (((v >>> 1) &&& g_1023) <<< 21) ||| (((v >>> 11) &&& g_1) <<< 20) ||| (((v >>> 12) &&& g_255) <<< 12) ||| (d <<< 7) ||| g_111
/-- addi / ld / sd / jalr / jal x0 to word `b` from word `a` -/
def g10 (d a v : UInt64) : UInt64 := g2 g_19 0 d a v
def g11 (d a v : UInt64) : UInt64 := g2 g_3 3 d a v
def g12 (b a v : UInt64) : UInt64 := g3 3 b a v
def g13 (d a b : UInt64) : UInt64 := g5 d ((b - a) <<< 2)
/-- a jump offset is in range (±1 MiB) -/
def g14 (a b : UInt64) : UInt64 :=
  let v := (b - a) <<< 2;
  if v + 1048576 < 2097152 then g_1 else g_0

/-! ## the state registers `r`: 0 cursor, 1 npw, 2 nres, 3 loop head, 4 error, 5 done, 6 work items, 7 nslots,
8 fixups -/
def g15 (r : Buf) (j v : UInt64) : Buf := bset r j v
def g16 (r : Buf) : Buf := bset r 4 g_1
/-- one word written at index `j` of a growing buffer -/
def g17 (k : Buf) (j v : UInt64) : Buf := if j < bsize k then bset k j v else bpush k v
/-- push a work item (tag, a, b) at item index `n` -/
def g18 (k : Buf) (n c a b : UInt64) : Buf := g17 (g17 (g17 k (n * 3) c) (n * 3 + 1) a) (n * 3 + 2) b
/-- emit a jal x0 from here to word `b` (error flag if out of range) -/
def g19 (r o : Buf) (d b : UInt64) : Buf × Buf :=
  let h := bsize o;
  if g14 h b == 1 then (r, bpush o (g13 d h b)) else (g16 r, bpush o (g13 d h b))
/-- patch word `p` (a jal x0 placeholder) to jump here -/
def g20 (r o : Buf) (p : UInt64) : Buf × Buf :=
  let h := bsize o;
  if g14 p h == 1 then (r, bset o p (g13 0 p h)) else (g16 r, bset o p (g13 0 p h))

/-- push t0 on the expression stack -/
def g21 (o : Buf) : Buf :=
  let h := bsize o;
  bpush (bpush (bpush (bpush o (g10 31 31 g_908)) (g4 7 31 30 8)) (g13 0 (h + 2) 1)) (g12 5 31 0)
/-- push register `d` -/
def g22 (o : Buf) (d : UInt64) : Buf :=
  let h := bsize o;
  bpush (bpush (bpush (bpush o (g10 31 31 g_908)) (g4 7 31 30 8)) (g13 0 (h + 2) 1)) (g12 d 31 0)
/-- li d, v -/
def g23 (o : Buf) (d v : UInt64) : Buf :=
  if v < 2048 then bpush o (g10 d 0 v) else
  let o1 := bpush o (g10 d 0 0);
  let o2 := bpush (bpush o1 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 56) &&& g_255));
  let o3 := bpush (bpush o2 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 48) &&& g_255));
  let o4 := bpush (bpush o3 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 40) &&& g_255));
  let o5 := bpush (bpush o4 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 32) &&& g_255));
  let o6 := bpush (bpush o5 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 24) &&& g_255));
  let o7 := bpush (bpush o6 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 16) &&& g_255));
  let o8 := bpush (bpush o7 (g2 g_19 1 d d 8)) (g10 d d ((v >>> 8) &&& g_255));
  bpush (bpush o8 (g2 g_19 1 d d 8)) (g10 d d (v &&& g_255))
/-- the s0 offset of slot `s` -/
def g24 (p s : UInt64) : UInt64 :=
  if s < p then ((p - 1 - s) <<< 3) + g_16 else g_0 - ((s - p + 1) <<< 3)

/-- LOCAL s w: push the w words -/
def g25 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, s, w, o => o
  | n + 1, p, s, w, o =>
    if w == 0 then o else
    let v := g11 5 8 (g24 p s);
    g25 n p (s + 1) (w - 1) (g21 (bpush o v))
/-- pop the top w words into slots s+w-1 … s -/
def g26 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, s, w, o => o
  | n + 1, p, s, w, o =>
    if w == 0 then o else
    let v := g12 5 8 (g24 p (s + w - 1));
    g26 n p s (w - 1) (bpush (bpush (bpush o (g11 5 31 0)) (g10 31 31 8)) v)
/-- push `c` items (tag 1 = visit, mode 0) -/
def g27 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, k, n, c => k
  | z + 1, k, n, c => if c == 0 then k else g27 z (g18 k n 1 0 0) (n + 1) (c - 1)
/-- patch the def's exit jumps (fixup buffer `f`, `c` entries) to here -/
def g28 : Nat → UInt64 → Buf × (Buf × Buf) → Buf × (Buf × Buf)
  | 0, c, y6 => y6
  | n + 1, c, y6 =>
    if c == 0 then y6 else
    let (f, y7) := y6;
    let (r, o) := y7;
    let v := bget f (c - 1);
    g28 n (c - 1) (f, g20 r o v)
/-- the def epilogue: result (nres words on top) copied over the args, return -/
def g29 : Nat → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, q, j, o => o
  | n + 1, p, q, j, o =>
    if j < q then g29 n p q (j + 1) (bpush (bpush o (g11 5 31 ((q - 1 - j) <<< 3))) (g12 5 8 ((p <<< 3) + g_16 - ((j + 1) <<< 3))))
    else bpush (bpush (bpush o (g10 31 8 ((p <<< 3) + g_16 - (q <<< 3)))) (g10 8 15 0)) (g2 g_103 0 0 14 0)

/-- pop two: t1 := top, t0 := below -/
def g30 (o : Buf) (k : UInt64) : Buf := bpush (bpush (bpush o (g11 6 31 0)) (g11 5 31 8)) (g10 31 31 k)
/-- the binary op `p` (add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7 xor 8) on t0, t1 → t0, stored over the top -/
def g31 (o : Buf) (p : UInt64) : Buf :=
  let w := (if p == 1 then g1 0 0 5 5 6 else if p == 2 then g1 32 0 5 5 6 else if p == 3 then g1 1 0 5 5 6
    else if p == 4 then g1 0 7 5 5 6 else if p == 5 then g1 0 6 5 5 6 else if p == 6 then g1 0 1 5 5 6
    else if p == 7 then g1 0 5 5 5 6 else g1 0 4 5 5 6);
  bpush (bpush (g30 o 8) w) (g12 5 31 0)
/-- the prims (ISIZE 1, RD 2, LEN 3, PUT 4, BNEW 5, BSIZE 6, BGET 7, BSET 8, BPUSH 9) -/
def g32 (o : Buf) (p u : UInt64) : Buf :=
  if p == 1 then g22 o 29 else if p == 3 then g22 o 29
  else if p == 2 then
    bpush (bpush (bpush (bpush (bpush (bpush o (g11 6 31 0)) (g10 5 0 0)) (g4 7 6 29 12)) (g1 0 0 5 28 6))
      (g2 g_3 4 5 5 0)) (g12 5 31 0)
  else if p == 5 then
    let h := bsize o;
    let o1 := g23 (bpush o (g10 5 30 0)) 6 ((u + 2) <<< 3);
    let h1 := bsize o1;
    let o2 := bpush (bpush (bpush o1 (g1 0 0 6 6 30)) (g4 7 31 6 8)) (g13 0 (h1 + 2) 1);
    g21 (bpush (bpush (bpush (g23 o2 7 u) (g12 0 5 0)) (g12 7 5 8)) (g10 30 6 0))
  else if p == 6 then bpush (bpush (bpush o (g11 5 31 0)) (g11 5 5 0)) (g12 5 31 0)
  else if p == 7 then
    let o1 := bpush (bpush (g30 o 8) (g11 7 5 0)) (g10 14 0 0);
    bpush (bpush (bpush (bpush (bpush o1 (g4 7 6 7 16)) (g2 g_19 1 6 6 3)) (g1 0 0 5 5 6)) (g11 14 5 16)) (g12 14 31 0)
  else if p == 8 then
    let o1 := bpush (bpush (bpush (bpush (bpush o (g11 14 31 0)) (g11 6 31 8)) (g11 5 31 16)) (g10 31 31 16)) (g11 7 5 0);
    bpush (bpush (bpush (bpush o1 (g4 7 6 7 16)) (g2 g_19 1 6 6 3)) (g1 0 0 6 5 6)) (g12 14 6 16)
  else
    let o1 := bpush (bpush (bpush (g30 o 8) (g11 7 5 0)) (g11 14 5 8)) (g4 6 7 14 8);
    let h := bsize o1;
    bpush (bpush (bpush (bpush (bpush (bpush o1 (g13 0 h 6)) (g2 g_19 1 15 7 3)) (g1 0 0 15 15 5)) (g12 6 15 16))
      (g10 7 7 1)) (g12 7 5 0)
/-- the number of operands of prim `p` -/
def g33 (p : UInt64) : UInt64 :=
  if p == 1 then 0 else if p == 5 then 0 else if p == 3 then 0 else if p == 2 then 1 else if p == 6 then 1
  else if p == 8 then 3 else 2

/-- the code before the defs: jump to start, the out-of-memory and capacity stubs -/
def g34 (o : Buf) : Buf :=
  let o1 := bpush (bpush (bpush (bpush (bpush (bpush o 0) (g10 10 0 g_901)) (g10 11 0 0)) (g11 1 12 0)) (g11 8 12 8))
    (g2 g_103 0 0 1 0);
  bpush (bpush (bpush (bpush (bpush o1 (g10 10 0 g_902)) (g10 11 0 0)) (g11 1 12 0)) (g11 8 12 8)) (g2 g_103 0 0 1 0)

/-- the start code: work under 16 bytes ⇒ a0 = −1 at once; save ra/s0, registers, call main (def `d` at word `w`), copy the output buffer's low bytes -/
def g35 (r o : Buf) (w : UInt64) : Buf × Buf :=
  let o1 := bpush (bpush (bpush o (g10 30 12 16)) (g2 g_19 5 31 2 3)) (g2 g_19 1 31 31 3);
  let o2 := bpush (bpush (bpush (bpush o1 (g4 7 31 30 16)) (g10 10 0 g_901)) (g10 11 0 0)) (g2 g_103 0 0 1 0);
  let o9 := bpush (bpush (bpush (bpush o2 (g12 1 12 0)) (g12 8 12 8)) (g10 28 10 0)) (g10 29 11 0);
  let (r1, o3) := g19 r o9 1 w;
  let o4 := bpush (bpush (bpush o3 (g11 5 31 0)) (g11 7 5 0)) (g4 1 7 0 16);
  let h4 := bsize o4;
  let o5 := bpush (bpush (bpush o4 (g10 10 0 1)) (g10 11 0 0)) (g13 0 (h4 + 2) (h4 + 14));
  let o6 := bpush (bpush (bpush o5 (g10 11 7 0)) (g10 6 5 16)) (g10 14 13 0);
  let o7 := bpush (bpush (bpush (bpush (bpush (bpush o6 (g4 0 7 0 28)) (g11 15 6 0)) (g3 0 15 14 0)) (g10 6 6 8))
    (g10 14 14 1)) (g10 7 7 g_901);
  let h7 := bsize o7;
  let o8 := bpush (bpush o7 (g13 0 h7 (h7 - 6))) (g10 10 0 0);
  (r1, bpush (bpush (bpush o8 (g11 1 12 0)) (g11 8 12 8)) (g2 g_103 0 0 1 0))

/-- 1 iff a slot range (slot `s`, width `w`) is empty or leaves the frame (`nslots` = r[7]) -/
def g43 (r : Buf) (s w : UInt64) : UInt64 :=
  if w == 0 then g_1 else if s < 251 then (if w < 251 then (if bget r 7 < s + w then g_1 else g_0) else g_1) else g_1

/-- visit the node at the cursor in mode `m` (0 value, 1 loop/def tail); a LOOP only as the def body (item 1 of the def); BIN op 1–8, IF compare 1–2, PRIM 1–9 -/
def g36 (x r o k : Buf) (y : UInt64) : Buf × (Buf × Buf) :=
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
  if c == 1 then (g15 r 0 (i + 2), (g21 (g23 o 5 (bget x (i + 1))), k)) else
  if c == 2 then
    let e := g43 r (bget x (i + 1)) (bget x (i + 2));
    if e == 1 then (g16 r, (o, k)) else
    let v := g25 256 (bget r 1) (bget x (i + 1)) (bget x (i + 2)) o;
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
    let o1 := bpush (bpush (bpush o (g11 5 8 (g24 (bget r 1) 0))) (g4 0 5 0 8)) 0;
    (g15 (g15 (g15 r 0 (i + 1)) 3 h) 6 (n + 3), (o1, g18 (g18 (g18 k n 1 1 0) (n + 1) 11 (h + 2) 0) (n + 2) 1 1 0))
    else (g16 r, (o, k))
  else (g16 r, (o, k))

/-- one work item -/
def g37 (x r o k t f : Buf) : Buf × (Buf × (Buf × Buf)) :=
  let n := bget r 6 - 1;
  let c := bget k (n * 3);
  let z := bget k (n * 3 + 1);
  let y := bget k (n * 3 + 2);
  let r1 := g15 r 6 n;
  if c == 1 then
    let (r2, y1) := g36 x r1 o k z;
    let (o2, k2) := y1;
    (r2, (o2, (k2, f))) else
  if c == 2 then (r1, (g31 o z, (k, f))) else
  if c == 3 then
    let h := bsize o;
    let o1 := bpush (bpush (g30 o 16) (if z == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0;
    (r1, (o1, (bset k ((n - 2) * 3 + 1) (h + 4), f))) else
  if c == 4 then
    let h := bsize o;
    let (r2, o2) := g20 r1 (bpush o 0) z;
    (r2, (o2, (bset k ((n - 2) * 3 + 1) h, f))) else
  if c == 5 then
    let (r2, o2) := g20 r1 o z;
    (r2, (o2, (k, f))) else
  if c == 6 then
    let v := g26 256 (bget r1 1) z y o;
    (r1, (v, (k, f))) else
  if c == 7 then
    let (r2, o2) := (if z < bsize t then g19 r1 o 1 (bget t z) else (g16 r1, o));
    (r2, (o2, (k, f))) else
  if c == 8 then
    let u := bget r1 9;
    (r1, (g32 o z u, (k, f))) else
  if c == 9 then
    let q := bget r1 8;
    let h := bsize o;
    if 65535 < q then (g16 r1, (o, (k, f))) else
    (g15 r1 8 (q + 1), (bpush o 0, (k, g17 f q h))) else
  if c == 10 then
    let p := bget r1 1;
    let h := bget r1 3;
    let o1 := g26 256 p 1 (p - 1) o;
    let (r2, o2) := g19 r1 o1 0 h;
    (r2, (o2, (k, f))) else
  if c == 11 then
    let w := g12 5 8 (g24 (bget r1 1) 0);
    let (r2, o2) := g20 r1 o z;
    (r2, (bpush (bpush o2 (g10 5 5 g_901)) w, (k, f))) else
  let i := bget r1 0;
  let r2 := (if bget x i == 21 then g15 r1 0 (i + 1) else g16 r1);
  let p := bget r2 1;
  let q := bget r2 2;
  let c2 := bget r2 8;
  let (f1, y8) := g28 65536 c2 (f, (r2, o));
  let (r3, o3) := y8;
  let o4 := g29 512 p q 0 (bpush (bpush o3 (g11 14 8 8)) (g11 15 8 0));
  (g15 r3 8 0, (o4, (k, f1)))

/-- a def header at the cursor: `DEF id npw nslots kind nres`, then the prologue -/
def g38 (x r o k t : Buf) : Buf × (Buf × (Buf × Buf)) :=
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
  let o1 := g22 (g22 o 1) 8;
  let h1 := bsize o1;
  let o2 := bpush (bpush (bpush (bpush o1 (g10 8 31 0)) (g10 31 31 (g_0 - ((s - p) <<< 3)))) (g4 7 31 30 8))
    (g13 0 (h1 + 3) 1);
  (r1, (o2, (g18 (g18 k 0 12 0 0) 1 1 0 0, bpush t h)))

/-- one step of the main loop: a def header (no pending items) or one work item -/
def g54 (x r o k t f : Buf) : Buf × (Buf × (Buf × (Buf × Buf))) :=
  if bget r 6 == 0 then
    let (r1, y2) := g38 x r o k t;
    let (o1, y3) := y2;
    let (k1, t1) := y3;
    (r1, (o1, (k1, (t1, f))))
  else
    let (r1, y4) := g37 x r o k t f;
    let (o1, y5) := y4;
    let (k1, f1) := y5;
    (r1, (o1, (k1, (t, f1))))

/-- 1 iff the main loop stops: done, error, code over 2^24 − 1 words, or all defs read -/
def g55 (x r o : Buf) : UInt64 :=
  if bget r 5 == 1 then g_1 else if bget r 4 == 1 then g_1 else if 16777215 < bsize o then g_1
  else if bget r 6 == 0 then (if bget r 0 < bsize x then g_0 else g_1) else g_0

/-- the result when the main loop stops; after the last def: patch word 0, the start code (main = last def) -/
def g56 (r o t : Buf) : Buf × Buf :=
  if bget r 5 == 1 then (r, o) else
  if bget r 4 == 1 then (r, o) else
  if 16777215 < bsize o then (g16 r, o) else
  let w := bsize t;
  if w == 0 then (g16 r, o) else
  let m := (if bget r 1 == 0 then (if bget r 2 == 1 then g_1 else g_0) else g_0);
  if m == 0 then (g16 r, o) else
  let (r1, o1) := g20 r o 0;
  let (r2, o2) := g35 r1 o1 (bget t (w - 1));
  (g15 r2 5 1, o2)

/-- the main loop -/
def g39 : Nat → Buf → Buf → Buf → Buf → Buf → Buf → Buf × Buf
  | 0, x, r, o, k, t, f => (g16 r, o)
  | n + 1, x, r, o, k, t, f =>
    if g55 x r o == 1 then g56 r o t else
    let (r1, y) := g54 x r o k t f;
    let (o1, y1) := y;
    let (k1, y2) := y1;
    let (t1, f1) := y2;
    g39 n x r1 o1 k1 t1 f1

/-- the code words as little-endian bytes -/
def g40 : Nat → List UInt8 → Buf → UInt64 → List UInt8 → List UInt8
  | 0, c, w, i, o => o
  | n + 1, c, w, i, o =>
    if i < bsize w then
      let v := bget w i;
      g40 n c w (i + 1) (put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24))
    else o

/-! Width pre-pass (fail loudly, the IR carries no types): CONST 1, LOCAL w, BIN 1 (operands 1), IF (a, b 1; t = e),
LET (v = w), PAIR Σ, CALL (Σ args = callee npw; callee nres), PRIM 1 (operands 1), LOOP (zero, step = nres),
CONTINUE (e = npw − 1; counts as nres), def body = nres; a LOOP only as the def body (its exits jump to
the epilogue, its head is r[3]).  State `s`: [0] cursor, [1] error, [2] npw, [3] nres,
[4] frames, [5] done; frames of 4 words (tag, children left, width so far, aux) from word 8.  `d`: npw, nres per def. -/
/-- field j of the top frame -/
def g44 (s : Buf) (j : UInt64) : UInt64 := bget s (8 + 4 * (bget s 4 - 1) + j)
/-- set field j of the top frame -/
def g46 (s : Buf) (j v : UInt64) : Buf := bset s (8 + 4 * (bget s 4 - 1) + j) v
/-- push a frame -/
def g47 (s : Buf) (a b c e : UInt64) : Buf :=
  let n := bget s 4;
  let y := 8 + 4 * n;
  bset (g17 (g17 (g17 (g17 s y a) (y + 1) b) (y + 2) c) (y + 3) e) 4 (n + 1)
/-- the error flag -/
def g48 (s : Buf) : Buf := bset s 1 1
/-- deliver a child of width `c` to the top frame -/
def g49 (s : Buf) (c : UInt64) : Buf :=
  let t := g44 s 0;
  let r := g44 s 1;
  let a := g44 s 2;
  let e := g44 s 3;
  let q := bget s 3;
  let s1 := g46 s 1 (r - 1);
  let z := (if t == 3 then (if c == 1 then g_0 else g_1)
    else if t == 4 then (if 2 < r then (if c == 1 then g_0 else g_1) else if r == 2 then g_0 else if c == a then g_0 else g_1)
    else if t == 5 then (if r == 2 then (if c == e then g_0 else g_1) else g_0)
    else if t == 9 then (if c == 1 then g_0 else g_1)
    else if t == 10 then (if c == q then g_0 else g_1)
    else if t < 12 then g_0 else if t == 100 then g_0 else g_1);
  let v := (if t == 6 then a + c else if t == 8 then a + c else c);
  if z == 1 then g48 s1 else g46 s1 2 v
/-- pop the completed top frame and deliver its width (`u`, `v` = npw, nres of a CALL's callee); the ROOT frame checks nres and the ENDDEF -/
def g50 (x s : Buf) (u v : UInt64) : Buf :=
  let t := g44 s 0;
  let a := g44 s 2;
  let e := g44 s 3;
  let p := bget s 2;
  let q := bget s 3;
  let s1 := bset s 4 (bget s 4 - 1);
  let i := bget s1 0;
  if t == 100 then (if a == q then (if bget x i == 21 then bset s1 0 (i + 1) else g48 s1) else g48 s1) else
  let w := (if t == 3 then g_1 else if t == 8 then v else if t == 9 then g_1 else if t == 10 then q else if t == 11 then q else a);
  let z := (if t == 8 then (if a == u then g_0 else g_1) else if t == 11 then (if a + 1 == p then g_0 else g_1) else g_0);
  if z == 1 then g48 s1 else g49 s1 w
/-- one step of the width pre-pass -/
def g51 (x d s : Buf) : Buf × Buf :=
  let i := bget s 0;
  let c := bget x i;
  let e := bget x (i + 1);
  let h := bsize d >>> 1;
  let p := bget x (i + 2);
  let q := bget x (i + 5);
  let f := (if bget s 4 == 0 then g_0 else g44 s 3);
  let u := bget d (2 * f);
  let v := bget d (2 * f + 1);
  if bget s 4 == 0 then
    if i < bsize x then
      if c == 20 then (bpush (bpush d p) q, g47 (bset (bset (bset s 0 (i + 6)) 2 p) 3 q) 100 1 0 0) else (d, g48 s)
    else (d, bset s 5 1)
  else if g44 s 1 == 0 then (d, g50 x s u v)
  else if c == 1 then (d, g49 (bset s 0 (i + 2)) 1)
  else if c == 2 then (d, g49 (bset s 0 (i + 3)) p)
  else if c == 3 then (d, g47 (bset s 0 (i + 2)) 3 2 0 0)
  else if c == 4 then (d, g47 (bset s 0 (i + 2)) 4 4 0 0)
  else if c == 5 then (d, g47 (bset s 0 (i + 3)) 5 2 0 p)
  else if c == 6 then (d, g47 (bset s 0 (i + 2)) 6 e 0 0)
  else if c == 8 then
    if e < h then (d, g47 (bset s 0 (i + 3)) 8 p 0 e) else (d, g48 s)
  else if c == 9 then (d, g47 (bset s 0 (i + 2)) 9 (g33 e) 0 0)
  else if c == 10 then (if bget s 4 == 1 then (d, g47 (bset s 0 (i + 1)) 10 2 0 0) else (d, g48 s))
  else if c == 11 then (d, g47 (bset s 0 (i + 1)) 11 1 0 0)
  else (d, g48 s)
/-- the width pre-pass loop (`x` threaded through: a loop's Buf parameters move into its state) -/
def g52 : Nat → Buf × (Buf × Buf) → Buf × (Buf × Buf)
  | 0, y => let (x, z) := y; let (d, s) := z; (x, (d, g48 s))
  | n + 1, y =>
    let (x, z) := y;
    let (d, s) := z;
    if bget s 1 == 1 then (x, (d, s)) else
    if bget s 5 == 1 then (x, (d, s)) else
    let (d1, s1) := g51 x d s;
    g52 n (x, (d1, s1))
/-- the AST back and 1 iff every node's width is consistent (see above) -/
def g53 (x : Buf) : Buf × UInt64 :=
  let s := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0;
  let (x1, z) := g52 16777216 (x, (bnew, s));
  let (d, s1) := z;
  (x1, (if bget s1 1 == 1 then g_0 else g_1))

/-- **the code generator**: AST (`IRV = 2` first) → machine-code bytes, or empty -/
def g42 (c : List UInt8) (x : Buf) (u : UInt64) : List UInt8 :=
  if 2147483647 < bsize x then [] else
  if bget x 0 == 2 then
    let (x2, w) := g53 x;
    if w == 0 then [] else
    let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u;
    let (r1, o) := g39 16777216 x2 r (g34 bnew) bnew bnew bnew;
    if bget r1 4 == 1 then [] else if 16777215 < bsize o then [] else if 262143 < bsize o then [] else
    g40 16777216 c o 0 []
  else []

/-- the code generator with the default buffer capacity κ = 2^19 words -/
def g41 (c : List UInt8) (x : Buf) : List UInt8 := g42 c x g_999

end C

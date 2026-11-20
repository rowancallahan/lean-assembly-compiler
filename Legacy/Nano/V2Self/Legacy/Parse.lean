/- Nano/V2Self: parser stage 2b (Nano/V2S/Parse.lean) in the nano subset.  Differences from `p2bV`, all semantic no-ops:
15-component state `(c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)` = `(c, f, x, y, p, d, na, cg, cf, o, S, D, F, |S|, |F|)`; the scope and frame stacks have no `bpop`: `i0`/`m0` are their top indices (push = `bset` below the buffer size else `bpush`, pop = lower the index; slots above the top are dead, never read); buffers are
moved, so the lookups `r5`/`r6` return the buffer back; they step over buffer POSITIONS (`bsize S` instead of `bsize S / 2`,
`findV` returns `3·number` instead of `number`), the number of a new def is read off the last table entry; `rdW` uses
two multiplications by 65536; the token fuel `n` is `16 * len' x + 16`; constants `w0..w13` type the tuple components.  Output-carrying
helpers take the output last. -/
import Legacy.Nano.V2Self.Legacy.Inl

def w0 : UInt64 := 0
def w1 : UInt64 := 1
def w2 : UInt64 := 2
def w3 : UInt64 := 3
def w4 : UInt64 := 4
def w5 : UInt64 := 5
def w6 : UInt64 := 6
def w7 : UInt64 := 7
def w8 : UInt64 := 8
def w9 : UInt64 := 9
def w10 : UInt64 := 10
def w11 : UInt64 := 11
def w12 : UInt64 := 12
def w13 : UInt64 := 13

def r0 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, q => 0
  | n + 1, x, q =>
    if q < len x then
      if rd x q == 0 then q + 1 else if rd x q == 1 && q + 1 < len x then r0 n x (q + 2) else 0
    else 0

def r1 (x : List UInt8) (p : UInt64) : UInt64 :=
  if rd x p == 5 then p + 9 else if rd x p == 14 then r0 (16 * len' x + 16) x (p + 1) else p + 1

def r2 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, p => 0
  | n + 1, x, p =>
    if p < len x then
      let q := rd x p;
      if (1 ≤ q && q ≤ 4) || (6 ≤ q && q ≤ 13) then r2 n x (p + 1)
      else if q == 5 then if p + 9 ≤ len x then r2 n x (p + 9) else 0
      else if q == 14 then if r0 (16 * len' x + 16) x (p + 1) == 0 then 0 else r2 n x (r0 (16 * len' x + 16) x (p + 1))
      else 0
    else 1

def r3 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, p, c => c
  | n + 1, x, p, c => if p < len x then r3 n x (r1 x p) (c + 1) else c

def r4 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, a, b => 0
  | n + 1, x, a, b =>
    if rd x a == 1 && rd x b == 1 then if rd x (a + 1) == rd x (b + 1) then r4 n x (a + 2) (b + 2) else 0
    else if rd x a == 0 && rd x b == 0 then 1 else 0

def r5 : Nat → List UInt8 → Buf → UInt64 → UInt64 → UInt64
  | 0, x, s, i, g => 0
  | n + 1, x, s, i, g =>
    if i == 0 then 0
    else if r4 (16 * len' x + 16) x (bget s (i - 2) + 1) (g + 1) == 1 then bget s (i - 1) + 1
    else r5 n x s (i - 2) g

def r6 : Nat → List UInt8 → Buf → UInt64 → UInt64 → UInt64
  | 0, x, t, i, g => 0
  | n + 1, x, t, i, g =>
    if i == 0 then 0
    else if r4 (16 * len' x + 16) x (bget t (i - 3) + 1) (g + 1) == 1 then i
    else r6 n x t (i - 3) g

def r7 (x : List UInt8) (p : UInt64) : UInt64 :=
  let v := rd x p + 256 * (rd x (p + 1) + 256 * (rd x (p + 2) + 256 * rd x (p + 3)));
  let w := rd x (p + 4) + 256 * (rd x (p + 5) + 256 * (rd x (p + 6) + 256 * rd x (p + 7)));
  v + w * 65536 * 65536

def r8 (a b : UInt64) : UInt64 := if b ≤ a then a - b else 0

def r9 (v : UInt64) (o : List UInt8) : List UInt8 :=
  j0 6 v (j0 6 (v >>> 8) (j0 6 (v >>> 16) (j0 6 (v >>> 24) (j0 6 (v >>> 32) (j0 6 (v >>> 40) (j0 6 (v >>> 48) (j0 6 (v >>> 56) (j0 5 0 o))))))))

def r10 (j k : UInt64) (o : List UInt8) : List UInt8 := j0 9 k (j0 15 j (j0 14 (j >>> 8) o))

def r19 (u : Buf) (m v : UInt64) : Buf := if m < bsize u then bset u m v else bpush u v

def r11 (u : Buf) (m t a b : UInt64) : Buf := r19 (r19 (r19 u m t) (m + 1) a) (m + 2) b

def r12 (x : List UInt8) (f1 a1 : UInt64) (s : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 :=
  let (c, y1) := s;
  let (f, y2) := y1;
  let (a, y3) := y2;
  let (b, y4) := y3;
  let (p, y5) := y4;
  let (d, y6) := y5;
  let (g, y7) := y6;
  let (h, y8) := y7;
  let (k, y9) := y8;
  let (o, y10) := y9;
  let (s0, y11) := y10;
  let (t0, y12) := y11;
  let (u0, y13) := y12;
  let (i0, m0) := y13;
  let z := r5 (16 * len' x + 16) x s0 i0 p;
  if z ≠ 0 then (w12, f, a, b, r1 x p, d + 1, g, h, k, j0 3 0 (j0 7 (r8 (r8 d 1) (z - 1)) o), s0, t0, u0, i0, m0)
  else
    let j := bsize t0;
    let e := r6 (16 * len' x + 16) x t0 j p;
    if e == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else
      let z2 := bget t0 (e - 2);
      let z3 := bget t0 (e - 1);
      if a1 == 1 then
        if z2 == 0 then (w12, f, a, b, r1 x p, d + 1, g, h, k, r10 z3 0 o, s0, t0, u0, i0, m0)
        else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
      else (w10, f1, z2, b, r1 x p, d, g, h, k, o, s0, t0, r11 u0 m0 7 z3 z2, i0, m0 + 3)

def r13 (x : List UInt8) (s : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 :=
  let (c, y1) := s;
  let (f, y2) := y1;
  let (a, y3) := y2;
  let (b, y4) := y3;
  let (p, y5) := y4;
  let (d, y6) := y5;
  let (g, y7) := y6;
  let (h, y8) := y7;
  let (k, y9) := y8;
  let (o, y10) := y9;
  let (s0, y11) := y10;
  let (t0, y12) := y11;
  let (u0, y13) := y12;
  let (i0, m0) := y13;
  let m1 := m0 - 3;
  let t := bget u0 m1;
  let a1 := bget u0 (m1 + 1);
  let b1 := bget u0 (m1 + 2);
  if t == 1 then
    if rd x p == 13 then (w5, a1, a, b, p + 1, d, g, h, k, o, r19 (r19 s0 i0 b1) (i0 + 1) (r8 d 1), t0, r11 u0 m1 2 0 0, i0 + 2, m1 + 3)
    else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m1)
  else if t == 2 then (w12, f, a, b, p, r8 d 1, g, h, k, j0 9 1 o, s0, t0, u0, i0 - 2, m1)
  else if t == 3 then (w6, a1, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m1)
  else if t == 4 then (w6, a1, a, b, p, r8 d 1, g, h, k, j0 8 b1 o, s0, t0, u0, i0, m1)
  else if t == 5 then (w8, a1, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m1)
  else if t == 6 then (w8, a1, a, b, p, r8 d 1, g, h, k, j0 8 40 o, s0, t0, u0, i0, m1)
  else if t == 7 then (w12, f, a, b, p, r8 (d + 1) b1, g, h, k, r10 a1 b1 o, s0, t0, u0, i0, m1)
  else if t == 8 then (w10, a1, b1, b, p, d, g, h, k, o, s0, t0, u0, i0, m1)
  else if rd x p == 7 then (w12, f, a, b, p + 1, d, g, h, k, o, s0, t0, u0, i0, m1)
  else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m1)

def r17 (x : List UInt8) (s : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 :=
  let (c, y1) := s;
  let (f, y2) := y1;
  let (a, y3) := y2;
  let (b, y4) := y3;
  let (p, y5) := y4;
  let (d, y6) := y5;
  let (g, y7) := y6;
  let (h, y8) := y7;
  let (k, y9) := y8;
  let (o, y10) := y9;
  let (s0, y11) := y10;
  let (t0, y12) := y11;
  let (u0, y13) := y12;
  let (i0, m0) := y13;
  let j := bsize t0;
  let e := r6 (16 * len' x + 16) x t0 j h;
  if e == 0 then (w5, k, a, b, p + 3, g, g, h, k, o, s0, t0, u0, i0, w0)
  else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)

def r18 (x : List UInt8) (s : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 :=
  let (c, y1) := s;
  let (f, y2) := y1;
  let (a, y3) := y2;
  let (b, y4) := y3;
  let (p, y5) := y4;
  let (d, y6) := y5;
  let (g, y7) := y6;
  let (h, y8) := y7;
  let (k, y9) := y8;
  let (o, y10) := y9;
  let (s0, y11) := y10;
  let (t0, y12) := y11;
  let (u0, y13) := y12;
  let (i0, m0) := y13;
  let z := bsize t0;
  let z4 := if z == 0 then w0 else bget t0 (z - 1) + 1;
  if m0 == 0 then
    if p < len x then (w1, k, a, b, p, d, g, h, k, j0 13 g o, s0, bpush (bpush (bpush t0 h) g) z4, u0, i0, m0)
    else (w0, f, a, b, p, d, g, h, k, j0 13 g o, s0, t0, u0, i0, m0)
  else r13 x (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)

def r14 (x : List UInt8) (s : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 :=
  let (c, y1) := s;
  let (f, y2) := y1;
  let (a, y3) := y2;
  let (b, y4) := y3;
  let (p, y5) := y4;
  let (d, y6) := y5;
  let (g, y7) := y6;
  let (h, y8) := y7;
  let (k, y9) := y8;
  let (o, y10) := y9;
  let (s0, y11) := y10;
  let (t0, y12) := y11;
  let (u0, y13) := y12;
  let (i0, m0) := y13;
  let q := rd x p;
  if c == 1 then
    if f ≠ 0 && q == 1 && rd x (p + 1) == 14 then (w2, f - 1, w0, b, r1 x (p + 1), d, g, p + 1, f - 1, o, s0, t0, u0, w0, m0)
    else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 2 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 6 then (w3, f - 1, f - 1, a, p + 1, d, g, h, k, o, s0, t0, u0, i0, m0)
    else (w4, f, a, b, p, d, a, h, k, o, s0, t0, u0, i0, m0)
  else if c == 3 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 14 then (w3, f - 1, a, b + 1, r1 x p, d, g, h, k, o, r19 (r19 s0 i0 p) (i0 + 1) b, t0, u0, i0 + 2, m0)
    else if q == 8 && (rd x (p + 1) == 3 || rd x (p + 1) == 4) && rd x (p + 2) == 7 then (w2, a, b, b, p + 3, d, g, h, k, o, s0, t0, u0, i0, m0)
    else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 4 then
    if q == 8 && (rd x (p + 1) == 3 || rd x (p + 1) == 4) && rd x (p + 2) == 9 then r17 x (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 12 then r18 x (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 5 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 2 && rd x (p + 1) == 14 && rd x (r1 x (p + 1)) == 9 then (w5, f - 1, a, b, r1 x (p + 1) + 1, d, g, h, k, o, s0, t0, r11 u0 m0 1 (f - 1) (p + 1), i0, m0 + 3)
    else (w7, f - 1, a, b, p, d, g, h, k, o, s0, t0, r11 u0 m0 3 (f - 1) 0, i0, m0 + 3)
  else if c == 6 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 10 then (w7, f - 1, a, b, p + 1, d, g, h, k, o, s0, t0, r11 u0 m0 4 (f - 1) 24, i0, m0 + 3)
    else if q == 11 then (w7, f - 1, a, b, p + 1, d, g, h, k, o, s0, t0, r11 u0 m0 4 (f - 1) 32, i0, m0 + 3)
    else (w12, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 7 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else (w9, f - 1, a, b, p, d, g, h, k, o, s0, t0, r11 u0 m0 5 (f - 1) 0, i0, m0 + 3)
  else if c == 8 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 12 then (w9, f - 1, a, b, p + 1, d, g, h, k, o, s0, t0, r11 u0 m0 6 (f - 1) 0, i0, m0 + 3)
    else (w12, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 9 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 14 then r12 x (f - 1) 0 (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 11 && rd x (p + 1) == 5 then (w12, f, a, b, p + 10, d + 1, g, h, k, j0 3 0 (r9 (0 - r7 x (p + 2)) o), s0, t0, u0, i0, m0)
    else (w11, f - 1, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else if c == 10 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if a == 0 then (w12, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else (w11, f - 1, a, b, p, d, g, h, k, o, s0, t0, r11 u0 m0 8 (f - 1) (a - 1), i0, m0 + 3)
  else if c == 11 then
    if f == 0 then (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 5 then (w12, f, a, b, p + 9, d + 1, g, h, k, j0 3 0 (r9 (r7 x (p + 1)) o), s0, t0, u0, i0, m0)
    else if q == 14 then r12 x f 1 (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
    else if q == 6 then (w5, f - 1, a, b, p + 1, d, g, h, k, o, s0, t0, r11 u0 m0 9 0 0, i0, m0 + 3)
    else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)
  else (w13, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)

def r15 : Nat → List UInt8 → UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 × Buf × Buf × Buf × UInt64 × UInt64 → List UInt8
  | 0, x, s => []
  | n + 1, x, s =>
    let (c, y1) := r14 x s;
    let (f, y2) := y1;
    let (a, y3) := y2;
    let (b, y4) := y3;
    let (p, y5) := y4;
    let (d, y6) := y5;
    let (g, y7) := y6;
    let (h, y8) := y7;
    let (k, y9) := y8;
    let (o, y10) := y9;
    let (s0, y11) := y10;
    let (t0, y12) := y11;
    let (u0, y13) := y12;
    let (i0, m0) := y13;
    if c == 0 then o else if c == 13 then [] else r15 n x (c, f, a, b, p, d, g, h, k, o, s0, t0, u0, i0, m0)

def r16 (x : List UInt8) : List UInt8 :=
  if (rd x 0 == 1 || rd x 0 == 2) && r2 (16 * len' x + 16) x 1 == 1 then
    r15 (13 * len' x + 6) x (w1, r3 (16 * len' x + 16) x 1 0 + 1, w0, w0, w1, w0, w0, w0, w0, [], bnew, bnew, bnew, w0, w0)
  else []

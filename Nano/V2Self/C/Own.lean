/- Nano/V2Self/C: the OWNERSHIP STAGE `o41` between the parser (Par1, `y16`) and the code generator (Gen, `g41`):
AST (IR v2.1, Testing/notes/NANO_V2_IR.md) → the same AST if the program follows the ownership discipline
`OwnSpec.Linear` (Nano/V2Self/Proof/OwnSpec.lean: buffers are affine, borrowed only by bsize/bget/read-only params),
else the EMPTY Buf (reject).  Needed because Gen's BPUSH/BSET/PUT update buffers in place.  Notes:
Testing/notes/NANO_V2_OWN.md.  Per def: the slot kinds K (0 word, 1 owned buffer, 2 read-only param) are INFERRED by
rounds of the walk in mode 1 (unverified heuristic: params start "unused" (3), uses raise them 3 → 0 word → 2 borrowed →
1 owned, a let slot used as a buffer makes its LOCAL source one; an unused param ends read-only),
then the walk runs in mode 0 (VERIFY = `OwnSpec.chk`); the param / result kinds go to the def table.
The walk is a stack machine over the pre-order AST.  Buffers:
`s`: registers 0 cursor, 1 error, 2 npw, 3 nres, 4 frames, 5 done, 6 nslots, 7 value top, 8 mode, 9 changed,
     10 snapshots, 11 phase (0 start a node, 1 a child completed, 2 the top frame decides), 12 body start, 13 defs done;
     frames of 8 words from 16: tag, children, done, destination source, value base, current child's base, aux a, aux b;
`f`: K at [0, ns), dead flags at [ns, 2ns), IF snapshots of the flags at 2ns + ns·j;
`v`: value entries (OwnSpec: plain kind 0/1, or `k + 4 (s + 1)` for a LOCAL word of slot s of kind k);
`t`: def table: t[d] = offset of [npw, nres, unused flags (inference only), param kinds, result kinds] (data from 4096). -/
import Nano.V2Self.C.Base
namespace C

/-- set word j (j ≤ size) -/
def o0 (b : Buf) (j v : UInt64) : Buf := if j < bsize b then bset b j v else bpush b v

/-- field j of the top frame / set it -/
def o1 (s : Buf) (j : UInt64) : UInt64 := bget s (16 + 8 * (bget s 4 - 1) + j)
def o2 (s : Buf) (j v : UInt64) : Buf := bset s (16 + 8 * (bget s 4 - 1) + j) v

/-- push a frame (tag, children, 0, destination source, value base = current = top, a, b) -/
def o3 (s : Buf) (g n d a b : UInt64) : Buf :=
  let q := bget s 4;
  let y := 16 + 8 * q;
  let u := bget s 7;
  if q < 1073741824 then
    bset (o0 (o0 (o0 (o0 (o0 (o0 (o0 (o0 s y g) (y + 1) n) (y + 2) 0) (y + 3) d) (y + 4) u) (y + 5) u) (y + 6) a) (y + 7) b) 4 (q + 1)
  else bset (bset s 1 1) 5 1

/-- hard error: stop the walk -/
def o5 (s : Buf) : Buf := bset (bset s 1 1) 5 1

/-- push a value entry (at most 2^24: the entry loops have fuel 2^24) -/
def o6 (s v : Buf) (e : UInt64) : Buf × Buf :=
  let u := bget s 7;
  if u < 16777216 then (bset s 7 (u + 1), o0 v u e) else (o5 s, v)

/-- slot q is dead (or no slot) -/
def o7 (s f : Buf) (q : UInt64) : UInt64 :=
  let n := bget s 6;
  if q < n then bget f (n + q) else 1

/-- prim argument destinations `OwnSpec.dsP` (4 = none) -/
def o10 (p o : UInt64) : UInt64 :=
  if p == 2 then (if o == 0 then 0 else 4)
  else if p == 4 then (if o == 0 then 1 else if o == 1 then 0 else 4)
  else if p == 6 then (if o == 0 then 2 else 4)
  else if p == 7 then (if o == 0 then 2 else if o == 1 then 0 else 4)
  else if p == 8 then (if o == 0 then 1 else if o < 3 then 0 else 4)
  else if p == 9 then (if o == 0 then 1 else if o == 1 then 0 else 4)
  else 4

/-- number of prim arguments -/
def o11 (p : UInt64) : UInt64 :=
  if p == 2 then 1 else if p == 4 then 2 else if p == 6 then 1 else if p == 7 then 2
  else if p == 8 then 3 else if p == 9 then 2 else 0

/-- destination of argument word o of the top frame (`OwnSpec.dest`): source 0 transfer, 1 two words, 2 prim, 3 call, 4 CONTINUE -/
def o9 (s f t : Buf) (o : UInt64) : UInt64 :=
  let c := o1 s 3;
  if c == 0 then 1
  else if c == 1 then (if o < 2 then 0 else 4)
  else if c == 2 then o10 (o1 s 6) o
  else if c == 3 then
    (let a := bget t (o1 s 6);
     let p := bget t a;
     if o < p then bget t (a + 2 + p + o) else 4)
  else if o + 1 < bget s 2 then (let k := bget f (o + 1); if k == 2 then 3 else k) else 4

/-- `OwnSpec.ok1`: entry e may reach destination d (1 = yes) -/
def o12 (s f : Buf) (e d : UInt64) : UInt64 :=
  if e < 4 then
    (if e == 0 then (if d < 4 then 1 else 0) else if e == 1 then (if d == 1 then 1 else if d == 2 then 1 else 0) else 0)
  else
    let k := e &&& 3;
    let q := (e >>> 2) - 1;
    if k == 0 then (if d < 4 then 1 else 0)
    else if k == 1 then (if d == 1 then (if o7 s f q == 0 then 1 else 0) else if d == 2 then (if o7 s f q == 0 then 1 else 0) else 0)
    else if k == 2 then (if d == 2 then 1 else if d == 3 then 1 else 0)
    else 0

/-- INFERENCE (mode 1): entry e at destination d, offset o, source c.  Strong evidence `g` (a prim's buffer argument, an
owned callee parameter / CONTINUE state) makes a parameter borrowed (2) or owned (1) and a let slot owned; a word
destination or a pair field makes an unused (3) parameter a word; a read-only parameter transferred becomes owned;
a CONTINUE state receiving a buffer becomes one -/
def o13 (s f t : Buf) (e d o c : UInt64) : Buf × Buf :=
  let p := bget s 2;
  let a := bget t (o1 s 6);
  if e < 4 then
    (if c == 4 then
      (if d < 4 then
        (if e == 1 then (if bget f (o + 1) == 1 then (s, f) else (bset s 9 1, bset f (o + 1) 1)) else (s, f))
       else (s, f))
     else (s, f))
  else
    let k := e &&& 3;
    let x := (e >>> 2) - 1;
    let g := (if c == 2 then (if d == 1 then 1 else if d == 2 then 2 else 0)
      else if c == 3 then (if d == 1 then 1 else if d == 2 then (if bget t (a + 2 + o) == 1 then 0 else 2) else 0)
      else if c == 4 then (if d == 1 then 1 else 0) else 0);
    let u := (if x < p then
      (if k == 2 then (if d == 1 then 1 else 2)
       else if k == 1 then 1
       else if d == 0 then 0
       else if c == 0 then 0
       else if g == 0 then k else g)
      else if k == 0 then (if g == 0 then 0 else 1) else k);
    let s1 := (if u == k then s else bset s 9 1);
    let f1 := (if u == k then f else bset f x u);
    if c == 4 then
      (if d < 4 then
        (let q := bget f1 (o + 1);
         let r := (if u == 1 then 1 else if u == 2 then (if q == 0 then 2 else if q == 3 then 2 else q) else q);
         if r == q then (s1, f1) else (bset s1 9 1, bset f1 (o + 1) r))
       else (s1, f1))
    else (s1, f1)

/-- an argument completed: check (mode 0) / infer (mode 1) its entries [q, b) against the top frame's destinations -/
def o14 : Nat → Buf → Buf → Buf → Buf → UInt64 → UInt64 → Buf × Buf
  | 0, s, f, v, t, q, b => (o5 s, f)
  | n + 1, s, f, v, t, q, b =>
    if q < b then
      let e := bget v q;
      let o := q - o1 s 4;
      let d := o9 s f t o;
      if bget s 8 == 0 then
        (if o12 s f e d == 1 then o14 n s f v t (q + 1) b else (bset s 1 1, f))
      else
        let c := o1 s 3;
        let (s1, f1) := o13 s f t e d o c;
        o14 n s1 f1 v t (q + 1) b
    else (s, f)

/-- `OwnSpec.tr` on the entries [q, b) in place: owned LOCAL words are consumed, entries become plain -/
def o15 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → Buf × (Buf × Buf)
  | 0, s, f, v, q, b => (o5 s, (f, v))
  | n + 1, s, f, v, q, b =>
    if q < b then
      let e := bget v q;
      let k := e &&& 3;
      let x := (e >>> 2) - 1;
      let m := bget s 8;
      let y := bget s 6 + x;
      if e < 4 then
        (if e < 2 then o15 n s f v (q + 1) b else if m == 0 then (bset s 1 1, (f, v)) else o15 n s f v (q + 1) b)
      else if k == 0 then o15 n s f (bset v q 0) (q + 1) b
      else if k == 1 then
        (if o7 s f x == 0 then o15 n s (bset f y 1) (bset v q 1) (q + 1) b
         else if m == 0 then (bset s 1 1, (f, v)) else o15 n s f (bset v q 1) (q + 1) b)
      else if m == 0 then (bset s 1 1, (f, v))
      else if k == 2 then
        (if x < bget s 2 then o15 n (bset s 9 1) (bset f x 1) (bset v q 1) (q + 1) b else o15 n s f (bset v q 1) (q + 1) b)
      else if x < bget s 2 then o15 n (bset s 9 1) (bset f x 0) (bset v q 0) (q + 1) b
      else o15 n s f (bset v q 1) (q + 1) b
    else (s, (f, v))

/-- end of an argument list, pass 1 (`OwnSpec.finC`): owned pins at transfer destinations are consumed -/
def o17 : Nat → Buf → Buf → Buf → Buf → UInt64 → UInt64 → Buf × Buf
  | 0, s, f, v, t, q, b => (o5 s, f)
  | n + 1, s, f, v, t, q, b =>
    if q < b then
      let e := bget v q;
      let d := o9 s f t (q - o1 s 4);
      let x := (e >>> 2) - 1;
      let y := bget s 6 + x;
      if e < 4 then o17 n s f v t (q + 1) b
      else if (e &&& 3) == 1 then
        (if d == 1 then (if o7 s f x == 0 then o17 n s (bset f y 1) v t (q + 1) b else (bset s 1 1, f))
         else o17 n s f v t (q + 1) b)
      else o17 n s f v t (q + 1) b
    else (s, f)

/-- pass 2 (`OwnSpec.finB`): owned pins at borrow destinations are still live -/
def o18 : Nat → Buf → Buf → Buf → Buf → UInt64 → UInt64 → Buf
  | 0, s, f, v, t, q, b => o5 s
  | n + 1, s, f, v, t, q, b =>
    if q < b then
      let e := bget v q;
      let d := o9 s f t (q - o1 s 4);
      let x := (e >>> 2) - 1;
      if e < 4 then o18 n s f v t (q + 1) b
      else if (e &&& 3) == 1 then
        (if d == 2 then (if o7 s f x == 0 then o18 n s f v t (q + 1) b else bset s 1 1)
         else o18 n s f v t (q + 1) b)
      else o18 n s f v t (q + 1) b
    else s

/-- `OwnSpec.strip` on [q, b) in place -/
def o19 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, v, q, b => v
  | n + 1, v, q, b =>
    if q < b then
      let e := bget v q;
      if e < 4 then o19 n v (q + 1) b
      else if (e &&& 3) == 0 then o19 n (bset v q 0) (q + 1) b
      else o19 n (bset v q 1) (q + 1) b
    else v

/-- push the n words t[a + j ..] (a callee's result kinds) as entries -/
def o20 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × Buf
  | 0, s, v, t, a, j, n => (o5 s, v)
  | m + 1, s, v, t, a, j, n =>
    if j < n then
      let e := bget t (a + j);
      let (s1, v1) := o6 s v e;
      o20 m s1 v1 t a (j + 1) n
    else (s, v)

/-- flag regions of f, n words from j: c = 0 copy a → b, 1 swap a ↔ b, 2 a |= b, 3 a := 0; inference only: 4 a := 3
(unused), 5 a := 2 where 3 (a parameter never used is read-only) -/
def o22 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, f, a, b, j, n, c => f
  | m + 1, f, a, b, j, n, c =>
    if j < n then
      let x := bget f (a + j);
      let y := bget f (b + j);
      if c == 0 then o22 m (o0 f (b + j) x) a b (j + 1) n c
      else if c == 1 then o22 m (bset (bset f (a + j) y) (b + j) x) a b (j + 1) n c
      else if c == 2 then o22 m (bset f (a + j) (x ||| y)) a b (j + 1) n c
      else if c == 3 then o22 m (o0 f (a + j) 0) a b (j + 1) n c
      else if c == 4 then o22 m (bset f (a + j) 3) a b (j + 1) n c
      else o22 m (bset f (a + j) (if x < 2 then x else 2)) a b (j + 1) n c
    else f

/-- v[a + j] := max (v[a + j], v[m + j]) for j < w -/
def o25 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, v, a, m, j, w => v
  | n + 1, v, a, m, j, w =>
    if j < w then
      let x := bget v (a + j);
      let y := bget v (m + j);
      if x < y then o25 n (bset v (a + j) y) a m (j + 1) w else o25 n v a m (j + 1) w
    else v

/-- `OwnSpec.join` of [a, m) and [m, b), result from a, the value top set -/
def o28 (s v : Buf) (a m b : UInt64) : Buf × Buf :=
  if m == a then (s, v)
  else if b == m then (s, v)
  else if m - a == b - m then (bset s 7 m, o25 16777216 v a m 0 (b - m))
  else if bget s 8 == 0 then (bset (bset s 1 1) 7 m, v) else (bset s 7 m, v)

/-- the value of a `let` (entries from a): mode 0 checks kinds = K[x ..] and the slots live, mode 1 sets K -/
def o26 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × Buf
  | 0, s, f, v, x, j, w, a => (o5 s, f)
  | n + 1, s, f, v, x, j, w, a =>
    if j < w then
      let e := bget v (a + j);
      if bget s 8 == 0 then
        (if e == bget f (x + j) then (if o7 s f (x + j) == 0 then o26 n s f v x (j + 1) w a else (bset s 1 1, f))
         else (bset s 1 1, f))
      else o26 n s (bset f (x + j) (if e < bget f (x + j) then bget f (x + j) else e)) v x (j + 1) w a
    else (s, f)

/-- INFERENCE (mode 1), a `let` whose value is a LOCAL: a let slot known to hold a buffer makes its source one -/
def o16 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × Buf
  | 0, s, f, v, x, j, w, a => (s, f)
  | n + 1, s, f, v, x, j, w, a =>
    if j < w then
      let e := bget v (a + j);
      let y := (e >>> 2) - 1;
      if e < 4 then o16 n s f v x (j + 1) w a
      else if bget f (x + j) == 1 then
        (if bget f y == 1 then o16 n s f v x (j + 1) w a else o16 n (bset s 9 1) (bset f y 1) v x (j + 1) w a)
      else o16 n s f v x (j + 1) w a
    else (s, f)

/-- the entries of `LOCAL x w` -/
def o27 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × Buf
  | 0, s, f, v, x, j, w => (o5 s, v)
  | n + 1, s, f, v, x, j, w =>
    if j < w then
      let e := bget f (x + j) + 4 * (x + j + 1);
      let (s1, v1) := o6 s v e;
      o27 n s1 f v1 x (j + 1) w
    else (s, v)

/-- `OwnSpec.fin` for the top frame (mode 0; mode 1 skips it): argument count, then the two pin passes -/
def o29 (s f v t : Buf) : Buf × Buf :=
  let c := o1 s 3;
  let a := o1 s 4;
  let b := bget s 7;
  let p := o1 s 6;
  let w := (if c == 1 then 2 else if c == 2 then o11 p else if c == 3 then bget t (bget t p) else bget s 2 - 1);
  if bget s 8 == 0 then
    (if c == 0 then
      (let (s1, f1) := o17 16777216 s f v t a b;
       (o18 16777216 s1 f1 v t a b, f1))
     else if b - a == w then
      (let (s1, f1) := o17 16777216 s f v t a b;
       (o18 16777216 s1 f1 v t a b, f1))
     else (bset s 1 1, f))
  else (s, f)

/-- phase 0: start the node at the cursor -/
def o31 (x s f v t : Buf) : Buf × (Buf × Buf) :=
  let i := bget s 0;
  let c := bget x i;
  let e := bget x (i + 1);
  let w := bget x (i + 2);
  let n := bget s 4;
  if c == 1 then (let (s1, v1) := o6 (bset (bset s 0 (i + 2)) 11 1) v 0; (s1, (f, v1)))
  else if c == 2 then
    (if 1048575 < e then (o5 s, (f, v)) else if 1048575 < w then (o5 s, (f, v)) else if bget s 6 < e + w then (o5 s, (f, v))
     else (let (s1, v1) := o27 16777216 (bset (bset s 0 (i + 3)) 11 1) f v e 0 w; (s1, (f, v1))))
  else if c == 3 then (o3 (bset (bset s 0 (i + 2)) 11 2) 3 2 1 0 0, (f, v))
  else if c == 4 then (o3 (bset (bset s 0 (i + 2)) 11 2) 4 4 1 0 0, (f, v))
  else if c == 5 then
    (if 1048575 < e then (o5 s, (f, v)) else if 1048575 < w then (o5 s, (f, v))
     else (o3 (bset (bset s 0 (i + 3)) 11 2) 5 2 0 e w, (f, v)))
  else if c == 6 then (o3 (bset (bset s 0 (i + 2)) 11 2) 6 e 0 0 0, (f, v))
  else if c == 8 then
    (if e < bget s 13 then (o3 (bset (bset s 0 (i + 3)) 11 2) 8 w 3 e 0, (f, v)) else (o5 s, (f, v)))
  else if c == 9 then
    (if 0 < e then (if e < 10 then (o3 (bset (bset s 0 (i + 2)) 11 2) 9 (o11 e) 2 e 0, (f, v)) else (o5 s, (f, v)))
     else (o5 s, (f, v)))
  else if c == 10 then
    (if n == 0 then (o3 (bset (bset s 0 (i + 1)) 11 2) 10 2 0 0 0, (f, v)) else (o5 s, (f, v)))
  else if c == 11 then
    (if e == 6 then (o3 (bset (bset s 0 (i + 3)) 11 2) 11 w 4 0 0, (f, v))
     else (o3 (bset (bset s 0 (i + 1)) 11 2) 11 1 4 0 0, (f, v)))
  else (o5 s, (f, v))

/-- phase 1: a child of the top frame completed (entries [a, b)); no frame = the def body completed -/
def o32 (x s f v t : Buf) : Buf × (Buf × Buf) :=
  if bget s 4 == 0 then (bset s 5 1, (f, v))
  else
  let g := o1 s 0;
  let c := o1 s 2;
  let a := o1 s 5;
  let b := bget s 7;
  let p := bget s 2;
  let n := bget s 6;
  if g == 4 then
    (if c < 2 then (let (s1, f1) := o14 16777216 s f v t a b; (o2 (bset s1 11 2) 2 (c + 1), (f1, v)))
     else if c == 2 then
      (let (s1, z) := o15 16777216 s f v a b;
       let (f1, v1) := z;
       let j := o1 s1 7;
       (o2 (o2 (bset s1 11 2) 6 b) 2 3, (o22 16777216 f1 n (2 * n + n * j) 0 n 1, v1)))
     else
      (let (s1, z) := o15 16777216 s f v a b;
       let (f1, v1) := z;
       let j := o1 s1 7;
       let m := o1 s1 6;
       let u := o1 s1 4;
       let f2 := o22 16777216 f1 n (2 * n + n * j) 0 n 2;
       let (s2, v2) := o28 (bset s1 10 j) v1 u m b;
       (o2 (bset s2 11 2) 2 4, (f2, v2))))
  else if g == 5 then
    (if c == 0 then
      (let y := o1 s 6;
       let w := o1 s 7;
       let (s0, f0) := (if bget s 8 == 1 then o16 16777216 s f v y 0 w a else (s, f));
       let (s1, z) := o15 16777216 s0 f0 v a b;
       let (f1, v1) := z;
       let k := (if y < p then 0 else if n < y + w then 0 else if b - a == w then 1 else 0);
       if k == 1 then
         (let (s2, f2) := o26 16777216 s1 f1 v1 y 0 w a;
          (o2 (bset (bset s2 7 a) 11 2) 2 1, (f2, v1)))
       else if bget s1 8 == 0 then (o2 (bset (bset (bset s1 1 1) 7 a) 11 2) 2 1, (f1, v1))
       else (o2 (bset (bset s1 7 a) 11 2) 2 1, (f1, v1)))
     else
      (let (s1, z) := o15 16777216 s f v a b;
       let (f1, v1) := z;
       (o2 (bset s1 11 2) 2 2, (f1, v1))))
  else if g == 10 then
    (if c == 0 then
      (let (s1, z) := o15 16777216 s f v a b;
       let (f1, v1) := z;
       (o2 (o2 (bset s1 11 2) 6 b) 2 1, (f1, v1)))
     else
      (let (s1, z) := o15 16777216 s f v a b;
       let (f1, v1) := z;
       let m := o1 s1 6;
       let u := o1 s1 4;
       let (s2, v2) := o28 s1 v1 u m b;
       (o2 (bset s2 11 2) 2 2, (f1, v2))))
  else (let (s1, f1) := o14 16777216 s f v t a b; (o2 (bset s1 11 2) 2 (c + 1), (f1, v)))

/-- phase 2: the top frame starts its next child or finishes -/
def o33 (x s f v t : Buf) : Buf × (Buf × Buf) :=
  let g := o1 s 0;
  let k := o1 s 1;
  let c := o1 s 2;
  let b := bget s 7;
  let n := bget s 6;
  let q := bget s 4;
  if c < k then
    (if g == 4 then
      (if c == 2 then
        (let (s1, f1) := o29 s f v t;
         let a := o1 s1 4;
         let j := bget s1 10;
         if j < 1073741824 then
           (let f2 := o22 16777216 f1 n (2 * n + n * j) 0 n 0;
            (o2 (o2 (bset (bset (bset s1 7 a) 10 (j + 1)) 11 0) 5 a) 7 j, (f2, v)))
         else (o5 s1, (f1, v)))
       else (o2 (bset s 11 0) 5 b, (f, v)))
     else if g == 10 then (o2 (bset s 11 0) 5 b, (o22 16777216 f n n 0 n 3, v))
     else (o2 (bset s 11 0) 5 b, (f, v)))
  else if g == 3 then
    (let (s1, f1) := o29 s f v t;
     let a := o1 s1 4;
     let (s2, v1) := o6 (bset s1 7 a) v 0;
     (bset (bset s2 4 (q - 1)) 11 1, (f1, v1)))
  else if g == 6 then
    (let (s1, f1) := o29 s f v t;
     let a := o1 s1 4;
     let m := bget s1 8;
     (bset (bset s1 4 (q - 1)) 11 1, (f1, (if m == 0 then o19 16777216 v a b else v))))
  else if g == 8 then
    (let (s1, f1) := o29 s f v t;
     let a := o1 s1 4;
     let d := bget t (o1 s1 6);
     let (s2, v1) := o20 16777216 (bset s1 7 a) v t (d + 2 + 2 * bget t d) 0 (bget t (d + 1));
     (bset (bset s2 4 (q - 1)) 11 1, (f1, v1)))
  else if g == 9 then
    (let (s1, f1) := o29 s f v t;
     let a := o1 s1 4;
     let p := o1 s1 6;
     let r := (if p == 4 then 1 else if p == 5 then 1 else if p == 8 then 1 else if p == 9 then 1 else 0);
     let (s2, v1) := o6 (bset s1 7 a) v r;
     (bset (bset s2 4 (q - 1)) 11 1, (f1, v1)))
  else if g == 11 then
    (let (s1, f1) := o29 s f v t;
     let a := o1 s1 4;
     (bset (bset (bset s1 7 a) 4 (q - 1)) 11 1, (f1, v)))
  else (bset (bset s 4 (q - 1)) 11 1, (f, v))

/-- one step of the walk -/
def o30 (x s f v t : Buf) : Buf × (Buf × Buf) :=
  let p := bget s 11;
  if p == 0 then o31 x s f v t else if p == 1 then o32 x s f v t else o33 x s f v t

/-- the walk loop: until done or error -/
def o34 : Nat → Buf → Buf → Buf → Buf → Buf → Buf × (Buf × Buf)
  | 0, x, s, f, v, t => (o5 s, (f, v))
  | n + 1, x, s, f, v, t =>
    if bget s 1 == 1 then (s, (f, v))
    else if bget s 5 == 1 then (s, (f, v))
    else
      let (s1, z) := o30 x s f v t;
      let (f1, v1) := z;
      o34 n x s1 f1 v1 t

/-- one walk of the current def's body in mode m (flags cleared), then the transfer of the body's value -/
def o35 (x s f v t : Buf) (m : UInt64) : Buf × (Buf × Buf) :=
  let n := bget s 6;
  let i := bget s 12;
  let s1 := bset (bset (bset (bset (bset (bset (bset (bset s 0 i) 4 0) 5 0) 7 0) 8 m) 10 0) 11 0) 9 0;
  let (s2, z) := o34 16777216 x s1 (o22 16777216 f n n 0 n 3) v t;
  let (f2, v2) := z;
  if bget s2 1 == 1 then (s2, (f2, v2)) else o15 16777216 s2 f2 v2 0 (bget s2 7)

/-- inference rounds (mode 1) until no kind changes -/
def o36 : Nat → Buf → Buf → Buf → Buf → Buf → Buf × (Buf × Buf)
  | 0, x, s, f, v, t => (s, (f, v))
  | n + 1, x, s, f, v, t =>
    let (s1, z) := o35 x s f v t 1;
    let (f1, v1) := z;
    if bget s1 1 == 1 then (s1, (f1, v1))
    else if bget s1 9 == 1 then o36 n x s1 f1 v1 t
    else (s1, (f1, v1))

/-- append y[j ..] (n words) to t; c = 1: the unused flags (y[j] = 3) instead -/
def o37 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, t, y, j, n, c => t
  | m + 1, t, y, j, n, c =>
    if j < n then
      (let e := bget y j;
       o37 m (bpush t (if c == 1 then (if e == 3 then 1 else 0) else e)) y (j + 1) n c)
    else t

/-- k zero words -/
def o40 : Nat → Buf → UInt64 → Buf
  | 0, b, k => b
  | n + 1, b, k => if bsize b < k then o40 n (bpush b 0) k else b

/-- one def (the cursor at its DEF word): kinds (mode 1, a black box: of its result only the kinds f2[0, n) matter, clamped
to ≤ 2; the registers verify reads are set again, sizes checked), verify (mode 0), table entry -/
def o38 (x s f v t : Buf) : Buf × (Buf × (Buf × Buf)) :=
  let i := bget s 0;
  let p := bget x (i + 2);
  let n := bget x (i + 3);
  let r := bget x (i + 5);
  let d := bget s 13;
  let k := (if 1048575 < p then 1 else if 1048575 < n then 1 else if 1048575 < r then 1 else if n < p then 1 else 0);
  if k == 1 then (o5 s, (f, (v, t))) else
  let s1 := bset (bset (bset (bset s 2 p) 3 r) 6 n) 12 (i + 6);
  if d < 4096 then
  let (s2, z) := o36 1000 x s1 (o22 16777216 (o22 16777216 f 0 0 0 (2 * n) 3) 0 0 0 p 4) v t;
  let (f2, v2) := z;
  let s4 := o40 16 s2 16;
  let k2 := (if bsize f2 < 2 * n then 1 else if 1099511627776 < bsize f2 then 1 else if 1099511627776 < bsize s4 then 1
    else if 1099511627776 < bsize v2 then 1 else 0);
  if k2 == 1 then (o5 s4, (f2, (v2, t))) else
  let u := bsize t;
  let t1 := o37 16777216 (bpush (bpush (bset t d u) p) r) f2 0 p 1;
  let s5 := bset (bset (bset (bset (bset s4 1 0) 2 p) 6 n) 12 (i + 6)) 13 d;
  let (s3, z3) := o35 x s5 (o22 16777216 f2 0 0 0 n 5) v2 t1 0;
  let (f3, v3) := z3;
  let j := bget s3 0;
  if bget s3 1 == 1 then (s3, (f3, (v3, t1)))
  else if bget x j == 21 then
    (if bget s3 7 == r then
      (bset (bset s3 0 (j + 1)) 13 (d + 1), (f3, (v3, o37 16777216 (o37 16777216 t1 f3 0 p 0) v3 0 r 0)))
     else (o5 s3, (f3, (v3, t1))))
  else (o5 s3, (f3, (v3, t1)))
  else (o5 s1, (f, (v, t)))

/-- the defs in order; 1 = all accepted -/
def o39 : Nat → Buf → Buf → Buf → Buf → Buf → UInt64
  | 0, x, s, f, v, t => 0
  | n + 1, x, s, f, v, t =>
    let i := bget s 0;
    if bget s 1 == 1 then 0
    else if i < bsize x then
      (if bget x i == 20 then
        (let (s1, z) := o38 x s f v t;
         let (f1, z1) := z;
         let (v1, t1) := z1;
         o39 n x s1 f1 v1 t1)
       else 0)
    else 1

/-- **the ownership stage**: the AST back if every def passes `OwnSpec.chk` with the inferred kinds, else empty -/
def o41 (x : Buf) : Buf :=
  let r := (if bget x 0 == 2 then (if bsize x < 1099511627776 then o39 16777216 x (bset (o40 64 bnew 16) 0 1) bnew bnew (o40 4096 bnew 4096) else 0) else 0);
  if r == 1 then x else bnew

end C

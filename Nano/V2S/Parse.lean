/- nano v2 source: parser stage 2b (`Nano.PS.stage2b`, Nano/ParseS3B.lean) as a byte machine
(Testing/notes/NANO_V2_SRC.md).  The machine `runS` with its state in ONE tuple `PS`:
`(c, f, x, y, p, d, na, cg, cf, o, S, D, F)` = control tag and its fields, the cursor in the tag-format input, the
stack depth, the arity, the current def's name (position of its `14` tag), the def fuel, the output, and three word
buffers: the scope `S` (pairs: name position, slot), the def table `D` (triples: name position, arity, number), the
frame stack `F` (triples: frame tag, two fields).  Names are positions of identifier tokens in the input, compared
by re-reading.
Control tags: 0 done, 1 defs, 2 params, 3 names, 4 dbody, 5 expr, 6 add, 7 mul, 8 mulT, 9 app, 10 args, 11 atom,
12 ret, 13 fail.  Frame tags: 1 letV f x, 2 letB, 3 exprAdd f, 4 addOp f op, 5 mulT f, 6 mulOp f, 7 call j k,
8 args f k, 9 paren.
Constructs: those of the other stages, plus the tuple state (built and taken apart whole) and word buffers
(`bget`, `bsize`, `bpush`, `bpop`, Nano/V2S/Prelude.lean). -/
import Nano.ParseS3B
import Nano.V2S.Inl

namespace Nano.V2S

/-- the parser state -/
abbrev PS := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 ×
  List UInt64 × List UInt64 × List UInt64

/-- the end of the identifier token whose characters start at `q` (`0` if malformed) -/
def idV : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, _ => 0
  | n + 1, xs, q =>
    if q < len xs then
      (if rd xs q == 0 then q + 1 else if rd xs q == 1 && q + 1 < len xs then idV n xs (q + 2) else 0)
    else 0

/-- the position after the token at `p` -/
def tnx (n : Nat) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if rd xs p == 5 then p + 9 else if rd xs p == 14 then idV n xs (p + 1) else p + 1

/-- 1 if the tokens from `p` on are well formed (`decT2 … none = some _`) -/
def vld : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, _ => 0
  | n + 1, xs, p =>
    if p < len xs then
      let t := rd xs p
      if (1 ≤ t && t ≤ 4) || (6 ≤ t && t ≤ 13) then vld n xs (p + 1)
      else if t == 5 then (if p + 9 ≤ len xs then vld n xs (p + 9) else 0)
      else if t == 14 then (if idV n xs (p + 1) == 0 then 0 else vld n xs (idV n xs (p + 1)))
      else 0
    else 1

/-- the number of tokens from `p` on (`c` so far) -/
def ntok : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, _, c => c
  | n + 1, xs, p, c => if p < len xs then ntok n xs (tnx n xs p) (c + 1) else c

/-- 1 if the identifiers whose characters start at `a` and `b` are equal -/
def nmEq : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, _, _ => 0
  | n + 1, xs, a, b =>
    if rd xs a == 1 && rd xs b == 1 then (if rd xs (a + 1) == rd xs (b + 1) then nmEq n xs (a + 2) (b + 2) else 0)
    else if rd xs a == 0 && rd xs b == 0 then 1 else 0

/-- `lookS`: the slot of name `g` among the newest `i` scope entries, plus one (0: none) -/
def lookV : Nat → List UInt8 → List UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, _ => 0
  | n + 1, xs, S, i, g =>
    if i == 0 then 0
    else if nmEq n xs (bget S (2 * i - 2) + 1) (g + 1) == 1 then bget S (2 * i - 1) + 1
    else lookV n xs S (i - 1) g

/-- `findD`: the number (from 1) of the newest of the first `i` def table entries named `g` (0: none) -/
def findV : Nat → List UInt8 → List UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, _ => 0
  | n + 1, xs, D, i, g =>
    if i == 0 then 0
    else if nmEq n xs (bget D (3 * i - 3) + 1) (g + 1) == 1 then i
    else findV n xs D (i - 1) g

/-- the word of the 8 little-endian bytes at `p` -/
def rdW (xs : List UInt8) (p : UInt64) : UInt64 :=
  (rd xs p + 256 * (rd xs (p + 1) + 256 * (rd xs (p + 2) + 256 * rd xs (p + 3)))) + 4294967296 *
    (rd xs (p + 4) + 256 * (rd xs (p + 5) + 256 * (rd xs (p + 6) + 256 * rd xs (p + 7))))

/-- `a - b`, 0 below 0 -/
def sat (a b : UInt64) : UInt64 := if b ≤ a then a - b else 0

/-- `sLi v` -/
def putLi (o : List UInt8) (v : UInt64) : List UInt8 :=
  put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 o 5 0) 6 (v >>> 56)) 6 (v >>> 48)) 6 (v >>> 40)) 6 (v >>> 32))
    6 (v >>> 24)) 6 (v >>> 16)) 6 (v >>> 8)) 6 v

/-- `sCallS j k` -/
def putCall (o : List UInt8) (j k : UInt64) : List UInt8 := put2 (put2 (put2 o 14 (j >>> 8)) 15 j) 9 k

/-- push a frame -/
def fpush (F : List UInt64) (t a b : UInt64) : List UInt64 := bpush (bpush (bpush F t) a) b

/-- drop the top frame -/
def fpop (F : List UInt64) : List UInt64 := bpop (bpop (bpop F))

/-- a variable or a call of an identifier at `p` (`app` / `atom`): `g` is the identifier, `f` the fuel of `args`;
`a` = 1 from `atom` (a call needs arity 0 there) -/
def stId (n : Nat) (xs : List UInt8) (f a : UInt64) (s : PS) : PS :=
  let (c, f0, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let k := lookV n xs S (bsize S / 2) p
  if k ≠ 0 then (12, f0, x, y, tnx n xs p, d + 1, na, cg, cf, put2 (put2 o 7 (sat (sat d 1) (k - 1))) 3 0, S, D, F)
  else
    let e := findV n xs D (bsize D / 3) p
    if e == 0 then (13, f0, x, y, p, d, na, cg, cf, o, S, D, F)
    else
      let ar := bget D (3 * e - 2)
      let j := bget D (3 * e - 1)
      if a == 1 then
        (if ar == 0 then (12, f0, x, y, tnx n xs p, d + 1, na, cg, cf, putCall o j 0, S, D, F)
         else (13, f0, x, y, p, d, na, cg, cf, o, S, D, F))
      else (10, f, ar, y, tnx n xs p, d, na, cg, cf, o, S, D, fpush F 7 j ar)

/-- `retFS`: return into the top frame (the frame is popped) -/
def stRetF (n : Nat) (xs : List UInt8) (s : PS) : PS :=
  let (c, f, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let t := bget F (bsize F - 3)
  let a := bget F (bsize F - 2)
  let b := bget F (bsize F - 1)
  let F := fpop F
  if t == 1 then
    (if rd xs p == 13 then (5, a, x, y, p + 1, d, na, cg, cf, o, bpush (bpush S b) (sat d 1), D, fpush F 2 0 0)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if t == 2 then (12, f, x, y, p, sat d 1, na, cg, cf, put2 o 9 1, bpop (bpop S), D, F)
  else if t == 3 then (6, a, x, y, p, d, na, cg, cf, o, S, D, F)
  else if t == 4 then (6, a, x, y, p, sat d 1, na, cg, cf, put2 o 8 b, S, D, F)
  else if t == 5 then (8, a, x, y, p, d, na, cg, cf, o, S, D, F)
  else if t == 6 then (8, a, x, y, p, sat d 1, na, cg, cf, put2 o 8 40, S, D, F)
  else if t == 7 then (12, f, x, y, p, sat (d + 1) b, na, cg, cf, putCall o a b, S, D, F)
  else if t == 8 then (10, a, b, y, p, d, na, cg, cf, o, S, D, F)
  else (if rd xs p == 7 then (12, f, x, y, p + 1, d, na, cg, cf, o, S, D, F)
        else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))

/-- one step of the machine -/
def pstep (n : Nat) (xs : List UInt8) (s : PS) : PS :=
  let (c, f, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let t := rd xs p
  if c == 1 then
    (if f ≠ 0 && t == 1 && rd xs (p + 1) == 14 then (2, f - 1, 0, y, tnx n xs (p + 1), d, na, p + 1, f - 1, o, [], D, F)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 2 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 6 then (3, f - 1, f - 1, x, p + 1, d, na, cg, cf, o, S, D, F)
     else (4, f, x, y, p, d, x, cg, cf, o, S, D, F))
  else if c == 3 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 14 then (3, f - 1, x, y + 1, tnx n xs p, d, na, cg, cf, o, bpush (bpush S p) y, D, F)
     else if t == 8 && (rd xs (p + 1) == 3 || rd xs (p + 1) == 4) && rd xs (p + 2) == 7 then
       (2, x, y, y, p + 3, d, na, cg, cf, o, S, D, F)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 4 then
    (if t == 8 && (rd xs (p + 1) == 3 || rd xs (p + 1) == 4) && rd xs (p + 2) == 9 then
       (if findV n xs D (bsize D / 3) cg == 0 then (5, cf, x, y, p + 3, na, na, cg, cf, o, S, D, [])
        else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 12 then
    (if bsize F == 0 then
       (if p < len xs then (1, cf, x, y, p, d, na, cg, cf, put2 o 13 na, S,
           bpush (bpush (bpush D cg) na) (bsize D / 3), F)
        else (0, f, x, y, p, d, na, cg, cf, put2 o 13 na, S, D, F))
     else stRetF n xs s)
  else if c == 5 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 2 && rd xs (p + 1) == 14 && rd xs (tnx n xs (p + 1)) == 9 then
       (5, f - 1, x, y, tnx n xs (p + 1) + 1, d, na, cg, cf, o, S, D, fpush F 1 (f - 1) (p + 1))
     else (7, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 3 (f - 1) 0))
  else if c == 6 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 10 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 4 (f - 1) 24)
     else if t == 11 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 4 (f - 1) 32)
     else (12, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 7 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else (9, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 5 (f - 1) 0))
  else if c == 8 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 12 then (9, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 6 (f - 1) 0)
     else (12, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 9 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 14 then stId n xs (f - 1) 0 s
     else if t == 11 && rd xs (p + 1) == 5 then
       (12, f, x, y, p + 10, d + 1, na, cg, cf, put2 (putLi o (0 - rdW xs (p + 2))) 3 0, S, D, F)
     else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 10 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if x == 0 then (12, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 8 (f - 1) (x - 1)))
  else if c == 11 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 5 then (12, f, x, y, p + 9, d + 1, na, cg, cf, put2 (putLi o (rdW xs (p + 1))) 3 0, S, D, F)
     else if t == 14 then stId n xs f 1 s
     else if t == 6 then (5, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 9 0 0)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else (13, f, x, y, p, d, na, cg, cf, o, S, D, F)

/-- the machine, gas `g` -/
def prun : Nat → Nat → List UInt8 → PS → List UInt8
  | 0, _, _, _ => []
  | g + 1, n, xs, s =>
    let s' := pstep n xs s
    let (c, _, _, _, _, _, _, _, _, o, _, _, _) := s'
    if c == 0 then o else if c == 13 then [] else prun g n xs s'

/-- **parser stage 2b, nano v2 source** -/
def p2bV (xs : List UInt8) : List UInt8 :=
  let n := xs.length + 1
  if (rd xs 0 == 1 || rd xs 0 == 2) && vld n xs 1 == 1 then
    prun (13 * xs.length + 6) n xs (1, ntok n xs 1 0 + 1, 0, 0, 1, 0, 0, 0, 0, [], [], [], [])
  else []

end Nano.V2S

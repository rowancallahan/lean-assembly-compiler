/- B₁: the v2 parser `p2bV` (Nano/V2S/Parse.lean) in S3 form (Nano/V2Boot/Prelude.lean) and the bridge
`p2bVS_eq : p2bVS xs = p2bV xs` (inputs of length < 2^27). Beyond the Prelude rules: the word buffers are kept
REVERSED (newest first, `bpushS b v = v :: b`) and the output `o` too; the state tuple is the same 13-tuple. -/
import Nano.V2S.ParseProof
import Nano.V2Boot.Prelude

namespace Nano.V2B
open Nano.V2S

abbrev PSR := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × List UInt8 ×
  List UInt64 × List UInt64 × List UInt64

def nthS : List UInt64 → UInt64 → UInt64
  | [], _ => 0
  | x :: r, i => if i == 0 then x else nthS r (i - 1)

def bsizeS : List UInt64 → UInt64
  | [] => 0
  | _ :: r => bsizeS r + 1

def bpopS : List UInt64 → List UInt64
  | [] => []
  | _ :: r => r

/-- `bget` on the reversed buffer -/
def bgetS (b : List UInt64) (i : UInt64) : UInt64 := if i < bsizeS b then nthS b (bsizeS b - 1 - i) else 0

def sat' (a b : UInt64) : UInt64 := if b ≤ a then a - b else 0

def idVS (f : UInt64) (xs : List UInt8) (q : UInt64) : UInt64 :=
  if h : f = 0 then 0
  else if q < lenS xs then
    (if rdS xs q == 0 then q + 1 else if rdS xs q == 1 && q + 1 < lenS xs then idVS (f - 1) xs (q + 2) else 0)
  else 0
termination_by f.toNat
decreasing_by exact dec_lt h

def tnxS (n : UInt64) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if rdS xs p == 5 then p + 9 else if rdS xs p == 14 then idVS n xs (p + 1) else p + 1

def vldS (f : UInt64) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if h : f = 0 then 0
  else if p < lenS xs then
    if (1 ≤ rdS xs p && rdS xs p ≤ 4) || (6 ≤ rdS xs p && rdS xs p ≤ 13) then vldS (f - 1) xs (p + 1)
    else if rdS xs p == 5 then (if p + 9 ≤ lenS xs then vldS (f - 1) xs (p + 9) else 0)
    else if rdS xs p == 14 then (if idVS (f - 1) xs (p + 1) == 0 then 0 else vldS (f - 1) xs (idVS (f - 1) xs (p + 1)))
    else 0
  else 1
termination_by f.toNat
decreasing_by all_goals exact dec_lt h

def ntokS (f : UInt64) (xs : List UInt8) (p c : UInt64) : UInt64 :=
  if h : f = 0 then c
  else if p < lenS xs then ntokS (f - 1) xs (tnxS (f - 1) xs p) (c + 1) else c
termination_by f.toNat
decreasing_by exact dec_lt h

def nmEqS (f : UInt64) (xs : List UInt8) (a b : UInt64) : UInt64 :=
  if h : f = 0 then 0
  else if rdS xs a == 1 && rdS xs b == 1 then
    (if rdS xs (a + 1) == rdS xs (b + 1) then nmEqS (f - 1) xs (a + 2) (b + 2) else 0)
  else if rdS xs a == 0 && rdS xs b == 0 then 1 else 0
termination_by f.toNat
decreasing_by exact dec_lt h

def lookVS (f : UInt64) (xs : List UInt8) (S : List UInt64) (i g : UInt64) : UInt64 :=
  if h : f = 0 then 0
  else if i == 0 then 0
  else if nmEqS (f - 1) xs (bgetS S (2 * i - 2) + 1) (g + 1) == 1 then bgetS S (2 * i - 1) + 1
  else lookVS (f - 1) xs S (i - 1) g
termination_by f.toNat
decreasing_by exact dec_lt h

def findVS (f : UInt64) (xs : List UInt8) (D : List UInt64) (i g : UInt64) : UInt64 :=
  if h : f = 0 then 0
  else if i == 0 then 0
  else if nmEqS (f - 1) xs (bgetS D (3 * i - 3) + 1) (g + 1) == 1 then i
  else findVS (f - 1) xs D (i - 1) g
termination_by f.toNat
decreasing_by exact dec_lt h

def rdWS (xs : List UInt8) (p : UInt64) : UInt64 :=
  (rdS xs p + 256 * (rdS xs (p + 1) + 256 * (rdS xs (p + 2) + 256 * rdS xs (p + 3)))) + 4294967296 *
    (rdS xs (p + 4) + 256 * (rdS xs (p + 5) + 256 * (rdS xs (p + 6) + 256 * rdS xs (p + 7))))

def putR2 (o : List UInt8) (m x : UInt64) : List UInt8 := putR (putR o m) x

def putLiS (o : List UInt8) (v : UInt64) : List UInt8 :=
  putR2 (putR2 (putR2 (putR2 (putR2 (putR2 (putR2 (putR2 (putR2 o 5 0) 6 (v >>> 56)) 6 (v >>> 48)) 6 (v >>> 40))
    6 (v >>> 32)) 6 (v >>> 24)) 6 (v >>> 16)) 6 (v >>> 8)) 6 v

def putCallS (o : List UInt8) (j k : UInt64) : List UInt8 := putR2 (putR2 (putR2 o 14 (j >>> 8)) 15 j) 9 k

def fpushS (F : List UInt64) (t a b : UInt64) : List UInt64 := b :: a :: t :: F
def fpopS (F : List UInt64) : List UInt64 := bpopS (bpopS (bpopS F))

def stIdS (n : UInt64) (xs : List UInt8) (f a : UInt64) (s : PSR) : PSR :=
  let (c, f0, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let k := lookVS n xs S (bsizeS S / 2) p
  if k ≠ 0 then
    (12, f0, x, y, tnxS n xs p, d + 1, na, cg, cf, putR2 (putR2 o 7 (sat' (sat' d 1) (k - 1))) 3 0, S, D, F)
  else
    let e := findVS n xs D (bsizeS D / 3) p
    if e == 0 then (13, f0, x, y, p, d, na, cg, cf, o, S, D, F)
    else
      let ar := bgetS D (3 * e - 2)
      let j := bgetS D (3 * e - 1)
      if a == 1 then
        (if ar == 0 then (12, f0, x, y, tnxS n xs p, d + 1, na, cg, cf, putCallS o j 0, S, D, F)
         else (13, f0, x, y, p, d, na, cg, cf, o, S, D, F))
      else (10, f, ar, y, tnxS n xs p, d, na, cg, cf, o, S, D, fpushS F 7 j ar)

def stRetFS (n : UInt64) (xs : List UInt8) (s : PSR) : PSR :=
  let (c, f, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let t := bgetS F (bsizeS F - 3)
  let a := bgetS F (bsizeS F - 2)
  let b := bgetS F (bsizeS F - 1)
  let F := fpopS F
  if t == 1 then
    (if rdS xs p == 13 then (5, a, x, y, p + 1, d, na, cg, cf, o, sat' d 1 :: b :: S, D, fpushS F 2 0 0)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if t == 2 then (12, f, x, y, p, sat' d 1, na, cg, cf, putR2 o 9 1, bpopS (bpopS S), D, F)
  else if t == 3 then (6, a, x, y, p, d, na, cg, cf, o, S, D, F)
  else if t == 4 then (6, a, x, y, p, sat' d 1, na, cg, cf, putR2 o 8 b, S, D, F)
  else if t == 5 then (8, a, x, y, p, d, na, cg, cf, o, S, D, F)
  else if t == 6 then (8, a, x, y, p, sat' d 1, na, cg, cf, putR2 o 8 40, S, D, F)
  else if t == 7 then (12, f, x, y, p, sat' (d + 1) b, na, cg, cf, putCallS o a b, S, D, F)
  else if t == 8 then (10, a, b, y, p, d, na, cg, cf, o, S, D, F)
  else (if rdS xs p == 7 then (12, f, x, y, p + 1, d, na, cg, cf, o, S, D, F)
        else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))

def pstepS (n : UInt64) (xs : List UInt8) (s : PSR) : PSR :=
  let (c, f, x, y, p, d, na, cg, cf, o, S, D, F) := s
  let t := rdS xs p
  if c == 1 then
    (if f ≠ 0 && t == 1 && rdS xs (p + 1) == 14 then
       (2, f - 1, 0, y, tnxS n xs (p + 1), d, na, p + 1, f - 1, o, [], D, F)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 2 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 6 then (3, f - 1, f - 1, x, p + 1, d, na, cg, cf, o, S, D, F)
     else (4, f, x, y, p, d, x, cg, cf, o, S, D, F))
  else if c == 3 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 14 then (3, f - 1, x, y + 1, tnxS n xs p, d, na, cg, cf, o, y :: p :: S, D, F)
     else if t == 8 && (rdS xs (p + 1) == 3 || rdS xs (p + 1) == 4) && rdS xs (p + 2) == 7 then
       (2, x, y, y, p + 3, d, na, cg, cf, o, S, D, F)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 4 then
    (if t == 8 && (rdS xs (p + 1) == 3 || rdS xs (p + 1) == 4) && rdS xs (p + 2) == 9 then
       (if findVS n xs D (bsizeS D / 3) cg == 0 then (5, cf, x, y, p + 3, na, na, cg, cf, o, S, D, [])
        else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 12 then
    (if bsizeS F == 0 then
       (if p < lenS xs then (1, cf, x, y, p, d, na, cg, cf, putR2 o 13 na, S,
           bsizeS D / 3 :: na :: cg :: D, F)
        else (0, f, x, y, p, d, na, cg, cf, putR2 o 13 na, S, D, F))
     else stRetFS n xs s)
  else if c == 5 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 2 && rdS xs (p + 1) == 14 && rdS xs (tnxS n xs (p + 1)) == 9 then
       (5, f - 1, x, y, tnxS n xs (p + 1) + 1, d, na, cg, cf, o, S, D, fpushS F 1 (f - 1) (p + 1))
     else (7, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpushS F 3 (f - 1) 0))
  else if c == 6 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 10 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpushS F 4 (f - 1) 24)
     else if t == 11 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpushS F 4 (f - 1) 32)
     else (12, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 7 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else (9, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpushS F 5 (f - 1) 0))
  else if c == 8 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 12 then (9, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpushS F 6 (f - 1) 0)
     else (12, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 9 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 14 then stIdS n xs (f - 1) 0 s
     else if t == 11 && rdS xs (p + 1) == 5 then
       (12, f, x, y, p + 10, d + 1, na, cg, cf, putR2 (putLiS o (0 - rdWS xs (p + 2))) 3 0, S, D, F)
     else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, F))
  else if c == 10 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if x == 0 then (12, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpushS F 8 (f - 1) (x - 1)))
  else if c == 11 then
    (if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
     else if t == 5 then (12, f, x, y, p + 9, d + 1, na, cg, cf, putR2 (putLiS o (rdWS xs (p + 1))) 3 0, S, D, F)
     else if t == 14 then stIdS n xs f 1 s
     else if t == 6 then (5, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpushS F 9 0 0)
     else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
  else (13, f, x, y, p, d, na, cg, cf, o, S, D, F)

def prunS (g : UInt64) (n : UInt64) (xs : List UInt8) (s : PSR) : List UInt8 :=
  if h : g = 0 then []
  else
    let (c, f1, x1, y1, p1, d1, na1, cg1, cf1, o1, S1, D1, F1) := pstepS n xs s
    if c == 0 then o1 else if c == 13 then [] else prunS (g - 1) n xs (c, f1, x1, y1, p1, d1, na1, cg1, cf1, o1, S1, D1, F1)
termination_by g.toNat
decreasing_by exact dec_lt h

def p2bVS (xs : List UInt8) : List UInt8 :=
  let n := 16 * lenS xs + 16
  if (rdS xs 0 == 1 || rdS xs 0 == 2) && vldS n xs 1 == 1 then
    (prunS (13 * lenS xs + 6) n xs (1, ntokS n xs 1 0 + 1, 0, 0, 1, 0, 0, 0, 0, [], [], [], [])).reverse
  else []

end Nano.V2B

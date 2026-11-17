/- nano v2 source: the inliner `inlB` TAIL-ONLY (NANO_V2_SPEC.md §1.1: tail self calls only), with a word-buffer
table (Testing/notes/NANO_V2_SRC.md).  `T` holds the code of every def read so far followed by the code of the def
being read; `O` holds the start offsets in `T` (`O[0] = 0`, one more per closed def).  A call `15 x` of def `t`
copies `T[O[t], O[t+1])` to the end of `T` (`cpy`).  Capacity `kap`: a table that would exceed it is an error
(empty output); the bridge assumes the input is adequate (its table fits).
Constructs: as `inlV` minus the nested call, plus word buffers `bsize`/`bget`/`bpush`. -/
import Nano.V2S.Inl

namespace Nano.V2S

/-- the capacity of the table -/
def kap : UInt64 := 16777216

/-- append `T[i, e)` to `T` -/
def cpy : Nat → List UInt64 → UInt64 → UInt64 → List UInt64
  | 0, T, _, _ => T
  | n + 1, T, i, e => if i < e then cpy n (bpush T (bget T i)) (i + 1) e else T

/-- output `T[i, e)` -/
def emT : Nat → List UInt64 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, _, o => o
  | n + 1, T, i, e, o => if i < e then emT n T (i + 1) e (put o (bget T i)) else o

/-- the result `wrap k last`, `last` = the newest closed def (none: empty) -/
def finT (k : UInt64) (T O : List UInt64) : List UInt8 :=
  let o := putPro 256 k (put2 [] 0 0)
  let o := if 2 ≤ bsize O then emT 16777216 T (bget O (bsize O - 2)) (bget O (bsize O - 1)) o else o
  put2 (putWr (put2 o 7 0)) 12 0

/-- one record per step -/
def inlT : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → List UInt64 → List UInt64 → List UInt8
  | 0, _, _, _, _, _, _ => []
  | n + 1, xs, p, hi, k, T, O =>
    if p + 2 ≤ len xs then
      let m := rd xs p
      let x := rd xs (p + 1)
      if m == 13 then inlT n xs (p + 2) hi x T (bpush O (bsize T))
      else if m == 14 then inlT n xs (p + 2) x k T O
      else if m == 15 then
        (if hi * 256 + x + 1 < bsize O then
          (if bsize T + (bget O (hi * 256 + x + 1) - bget O (hi * 256 + x)) ≤ kap then
            inlT n xs (p + 2) hi k (cpy 16777216 T (bget O (hi * 256 + x)) (bget O (hi * 256 + x + 1))) O
           else [])
         else inlT n xs (p + 2) hi k T O)
      else if bsize T + 2 ≤ kap then inlT n xs (p + 2) hi k (bpush (bpush T m) x) O
      else []
    else finT k T O

/-- **the inliner, tail-only nano v2 source** -/
def inlTV (xs : List UInt8) : List UInt8 := inlT (xs.length + 1) xs 0 0 0 [] [0]

end Nano.V2S

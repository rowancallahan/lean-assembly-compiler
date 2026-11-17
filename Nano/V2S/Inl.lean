/- nano v2 source: the inliner `inlB` (Nano/SerU.lean) as a byte machine (Testing/notes/NANO_V2_SRC.md).
No table: the inlined body of def `t` is recomputed from the input each time it is called (re-reading its records,
nested recursion for its own calls).  One `Nat` fuel per function; `inlBody` takes `(len+1)^2` (a call chain makes at
most `len+1` loop steps per nesting level, and at most `len` levels).
Constructs: UInt64 `+ - * ==  <  ≤`, `if`, `let`, calls, fuel recursion (one non-tail self call in `inlBody`), `rd`,
`len`, `put`.  Bridge: `inlV_eq : inlV xs = inlB xs` for every input of length < 2^32. -/
import Nano.InlS3
import Nano.V2.Asm

namespace Nano.V2

/-- the number of `13` records from position `p` on (`c` so far) -/
def cnt13 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, _, c => c
  | n + 1, xs, p, c =>
    if p + 2 ≤ len xs then cnt13 n xs (p + 2) (if rd xs p == 13 then c + 1 else c) else c

/-- the position after the `t`-th `13` record at or after `p` (`p` when `t = 0`) -/
def startOf : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, p, _ => p
  | n + 1, xs, p, t =>
    if t == 0 then p
    else if p + 2 ≤ len xs then startOf n xs (p + 2) (if rd xs p == 13 then t - 1 else t) else p

/-- the high byte register at position `p`: the argument of the last `14` record in `[q, p)` (`h` before) -/
def hiAt : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, h => h
  | n + 1, xs, q, p, h =>
    if q + 2 ≤ p then hiAt n xs (q + 2) p (if rd xs q == 14 then rd xs (q + 1) else h) else h

/-- the inlined body of def `j` from position `p` (high byte `hi`) up to its `13` record, appended to `o` -/
def inlBody : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, _, _, o => o
  | f + 1, xs, j, p, hi, o =>
    if p + 2 ≤ len xs then
      let m := rd xs p
      let x := rd xs (p + 1)
      if m == 13 then o
      else if m == 14 then inlBody f xs j (p + 2) x o
      else if m == 15 then
        let t := hi * 256 + x
        if t < j then
          let s := startOf (xs.length + 1) xs 0 t
          inlBody f xs j (p + 2) hi (inlBody f xs t s (hiAt (xs.length + 1) xs 0 s 0) o)
        else inlBody f xs j (p + 2) hi o
      else inlBody f xs j (p + 2) hi (put (put o m) x)
    else o

/-- `mo m x` -/
def put2 (o : List UInt8) (m x : UInt64) : List UInt8 := put (put o m) x

/-- `sArg` -/
def putArg (o : List UInt8) : List UInt8 :=
  put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 o 1 0) 2 6) 2 5) 2 4) 2 3) 2 2) 2 1) 2 0) 3 0) 4 0

/-- `sWr` -/
def putWr (o : List UInt8) : List UInt8 :=
  put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 (put2 o
    10 0) 11 0) 10 8) 11 1) 10 16) 11 2) 10 24) 11 3) 10 32) 11 4) 10 40) 11 5) 10 48) 11 6) 10 56) 11 7

/-- `serPro k` appended -/
def putPro : Nat → UInt64 → List UInt8 → List UInt8
  | 0, _, o => o
  | f + 1, k, o => if k == 0 then o else putPro f (k - 1) (putArg o)

/-- **the inliner, nano v2 source** -/
def inlV (xs : List UInt8) : List UInt8 :=
  let n := xs.length + 1
  let J := cnt13 n xs 0 0
  let s := startOf n xs 0 (J - 1)
  let e := startOf n xs 0 J
  let k := if J == 0 then 0 else rd xs (e - 1)
  let o := putPro 256 k (put2 [] 0 0)
  let o := if J == 0 then o else inlBody (n * n) xs (J - 1) s (hiAt n xs 0 s 0) o
  put2 (putWr (put2 o 7 0)) 12 0

end Nano.V2

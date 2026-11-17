/- nano v2 source: stage 1 + parser 2a, `lexA` (Nano/LexS3.lean), as a byte machine (Testing/notes/NANO_V2_SRC.md).
Two passes over the input with the fuel discipline of `lexS` (one unit per token step, the word span bounded by the
same fuel): `lexChk` (4 on failure, else the `uniC` type code), then `lexEmit` (the tag format of the tokens).
`stepK` / `stepN`: the kind of the step at position `p` and the next position.  Kinds: 0 fail, 1 end, 2 skip,
`2 + tag` a token with tag byte `tag` (Nano/ParseS3B.lean `encTok`).
Constructs: UInt64 `+ - * >>> == < ≤ && ||`, `if`, `let`, calls, fuel recursion, `rd`, `len`, `put`. -/
import Nano.LexS3
import Nano.V2.Inl

namespace Nano.V2

/-- 1 if `c` is a word character (letter, digit, `_`) -/
def isWC (c : UInt64) : UInt64 :=
  if (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || (48 ≤ c && c ≤ 57) then 1 else 0

/-- the end of the word starting at `p` (at most `n` characters) -/
def wordEnd : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, p => p
  | n + 1, xs, p => if p < len xs && isWC (rd xs p) == 1 then wordEnd n xs (p + 1) else p

/-- 1 if every byte in `[i, e)` is a digit -/
def allDigR : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, _, _ => 1
  | n + 1, xs, i, e => if i < e then (if 48 ≤ rd xs i && rd xs i ≤ 57 then allDigR n xs (i + 1) e else 0) else 1

/-- 1 if every byte in `[i, e)` is a digit or `_` -/
def allDUR : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, _, _, _ => 1
  | n + 1, xs, i, e =>
    if i < e then (if (48 ≤ rd xs i && rd xs i ≤ 57) || rd xs i == 95 then allDUR n xs (i + 1) e else 0) else 1

/-- the value of the numeral `[i, e)` (`a` so far) -/
def numR : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, a => a
  | n + 1, xs, i, e, a => if i < e then numR n xs (i + 1) e (a * 10 + (rd xs i - 48)) else a

/-- the kind of the word `[p, e)` (`n` bounds its length) -/
def wordK (n : Nat) (xs : List UInt8) (p e : UInt64) : UInt64 :=
  if e ≤ p then 0
  else
    let c := rd xs p
    if 48 ≤ c && c ≤ 57 then (if allDigR n xs p e == 1 then 7 else 0)
    else if e - p == 3 && c == 100 && rd xs (p + 1) == 101 && rd xs (p + 2) == 102 then 3
    else if e - p == 3 && c == 108 && rd xs (p + 1) == 101 && rd xs (p + 2) == 116 then 4
    else if e - p == 6 && c == 85 && rd xs (p + 1) == 73 && rd xs (p + 2) == 110 && rd xs (p + 3) == 116 &&
      rd xs (p + 4) == 54 && rd xs (p + 5) == 52 then 5
    else if e - p == 5 && c == 73 && rd xs (p + 1) == 110 && rd xs (p + 2) == 116 && rd xs (p + 3) == 54 &&
      rd xs (p + 4) == 52 then 6
    else if 97 ≤ c && c ≤ 122 && allDUR n xs (p + 1) e == 1 then 16
    else 0

/-- the kind of the step at `p` (`f`: the fuel left after this step) -/
def stepK (f : Nat) (xs : List UInt8) (p : UInt64) : UInt64 :=
  if p < len xs then
    let c := rd xs p
    if c == 32 then 2
    else if c == 10 then
      if p + 1 < len xs then
        let d := rd xs (p + 1)
        if d == 32 || d == 10 then 2
        else if d == 100 && p + 3 < len xs && rd xs (p + 2) == 101 && rd xs (p + 3) == 102 then
          (if p + 4 < len xs && isWC (rd xs (p + 4)) == 1 then 0 else 2)
        else 0
      else 1
    else if c == 40 then 8
    else if c == 41 then 9
    else if c == 43 then 12
    else if c == 45 then (if p + 1 < len xs && rd xs (p + 1) == 45 then 0 else 13)
    else if c == 42 then 14
    else if c == 59 then 15
    else if c == 58 then (if p + 1 < len xs && rd xs (p + 1) == 61 then 11 else 10)
    else if isWC c == 1 then wordK f xs p (wordEnd f xs p)
    else 0
  else 1

/-- the position after the step at `p` -/
def stepN (f : Nat) (xs : List UInt8) (p : UInt64) : UInt64 :=
  let c := rd xs p
  if c == 58 && p + 1 < len xs && rd xs (p + 1) == 61 then p + 2
  else if isWC c == 1 then wordEnd f xs p
  else p + 1

/-- the type code of a kind (1 `UInt64`, 2 `Int64`, 0 other) -/
def tyK (k : UInt64) : UInt64 := if k == 5 then 1 else if k == 6 then 2 else 0

/-- `uniC` one step -/
def uni (t c : UInt64) : UInt64 := if c == 0 then t else if t == 0 then c else if t == c then c else 3

/-- pass 1: 4 if the lexer fails, else the type code -/
def lexChk : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, xs, p, t => if p < len xs then 4 else t
  | f + 1, xs, p, t =>
    let k := stepK f xs p
    if k == 0 then 4
    else if k == 1 then t
    else lexChk f xs (stepN f xs p) (uni t (tyK k))

/-- `[1, c]` per byte of `[i, e)`, then `0` -/
def emitId : Nat → List UInt8 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, _, o => put o 0
  | n + 1, xs, i, e, o => if i < e then emitId n xs (i + 1) e (put (put o 1) (rd xs i)) else put o 0

/-- the 8 bytes of `v`, little-endian -/
def emitW (o : List UInt8) (v : UInt64) : List UInt8 :=
  put (put (put (put (put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48))
    (v >>> 56)

/-- the tag format of the token of kind `k` at `[p, e)` -/
def emitTok (f : Nat) (xs : List UInt8) (k p e : UInt64) (o : List UInt8) : List UInt8 :=
  if k == 7 then emitW (put o 5) (numR f xs p e 0)
  else if k == 16 then emitId f xs p e (put o 14)
  else put o (k - 2)

/-- pass 2: the tokens -/
def lexEmit : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, o => o
  | f + 1, xs, p, o =>
    let k := stepK f xs p
    if k == 0 || k == 1 then o
    else if k == 2 then lexEmit f xs (stepN f xs p) o
    else lexEmit f xs (stepN f xs p) (emitTok f xs k p (stepN f xs p) o)

/-- 1 if no adjacent pair `[i, i+1]` from `i` on is rejected by `adjOk` -/
def adjL : Nat → List UInt8 → UInt64 → UInt64
  | 0, _, _ => 1
  | n + 1, xs, i =>
    if i + 1 < len xs then
      let a := rd xs i
      let b := rd xs (i + 1)
      if (isWC a == 1 || a == 41) && b == 40 then 0
      else if a == 41 && isWC b == 1 then 0
      else adjL n xs (i + 1)
    else 1

/-- **stage 1 + 2a, nano v2 source** -/
def lexV (xs : List UInt8) : List UInt8 :=
  if adjL xs.length xs 0 == 1 then
    let t := lexChk xs.length xs 0 0
    if t == 1 || t == 2 then lexEmit xs.length xs 0 (put [] t) else []
  else []

end Nano.V2

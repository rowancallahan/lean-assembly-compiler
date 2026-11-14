/- `frontx_compile` on `Id.run do … for … ` loops with mutable locals and on non-recursive functions, mostly
lean-svg code copied verbatim (`LeanSvg/Bytes.lean`, `LeanSvg/PngDecode.lean`, `LeanSvg/GifDecode.lean`).
Nothing in this file is proved by hand; the `with` clauses are the only human input. -/
import Proven.Frontx.Examples

namespace Proven.Frontx.Ex
open Proven Proven.Frontx

/-! ## a first loop -/

def sumTo (xs : ByteArray) : UInt64 := Id.run do
  let mut s : UInt64 := 0
  for i in [0:xs.size] do
    s := s + xs[i]!.toUInt64
  return s

frontx_compile sumTo

/-! ## lean-svg `Bytes` (verbatim; `at'` and `b64Digit` are in `Examples.lean`) -/

@[inline] def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13
@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
@[inline] def isAlpha (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
@[inline] def isNameChar (c : UInt8) : Bool :=
  isAlpha c || isDigit c || c == 45 || c == 95 || c == 46 || c == 58   -- - _ . :
@[inline] def toLower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- Advance from `i` while `p` holds. -/
def skipWhile (bs : ByteArray) (i : Nat) (p : UInt8 → Bool) : Nat := Id.run do
  let mut j := i
  for _ in [i:bs.size] do
    if p (at' bs j) then j := j + 1 else break
  return j

def skipWs (bs : ByteArray) (i : Nat) : Nat := skipWhile bs i isWs

/-- Skip whitespace and commas (SVG list separators). -/
def skipWsComma (bs : ByteArray) (i : Nat) : Nat := skipWhile bs i (fun c => isWs c || c == 44)

/-- Index of the first `c` at or after `i`, or `bs.size`. -/
def findByte (bs : ByteArray) (i : Nat) (c : UInt8) : Nat := Id.run do
  let mut j := i
  for _ in [i:bs.size] do
    if at' bs j == c then return j
    j := j + 1
  return bs.size

/-- lean-svg `PngDecode.be32` -/
@[inline] def be32 (b : ByteArray) (i : Nat) : Nat :=
  ((at' b i).toNat <<< 24) ||| ((at' b (i + 1)).toNat <<< 16) |||
    ((at' b (i + 2)).toNat <<< 8) ||| (at' b (i + 3)).toNat

/-- lean-svg `GifDecode.le16` -/
@[inline] def le16 (b : ByteArray) (i : Nat) : Nat := (at' b i).toNat ||| ((at' b (i + 1)).toNat <<< 8)

-- non-recursive functions: no loop, one pass through the tree
frontx_compile toLower
frontx_compile isNameChar
frontx_compile b64Digit
frontx_compile be32 with fun _ i => i + 3 < 2 ^ 64
frontx_compile le16 with fun _ i => i + 1 < 2 ^ 64

-- loops.  The `with` clause is the loop invariant (parameters, loop index, mutable locals): the local `j` is an
-- unbounded `Nat`; its bound comes from the loop index.
frontx_compile skipWs with fun _ _ i j => j ≤ i
frontx_compile skipWsComma with fun _ _ i j => j ≤ i
frontx_compile findByte with fun _ _ _ i _ j => j ≤ i

end Proven.Frontx.Ex

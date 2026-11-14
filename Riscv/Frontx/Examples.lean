/- `frontx_compile` on ordinary tail-recursive Lean definitions.  Each command adds, kernel-checked:
`f.tree`, `f.lay`, `f.Rep`, `f.out`, `f.step1`, `f.runs`, `f.exec` (see `Translate.lean`).
Nothing in this file is proved by hand. -/
import Riscv.Frontx.Translate

namespace Proven
open Proven.Frontx
namespace Frontx.Ex

/-! ## The two hand-proved loops of `Riscv/Examples/LoopExamples.lean` (definitions copied: that module cannot be
imported together with `Riscv.Examples.ArrExamples`, which the `Implements1` glue needs), now automatic -/

def sumDown (n acc : BitVec 64) : BitVec 64 := if n = 0 then acc else sumDown (n - 1) (acc + n)
termination_by n.toNat
decreasing_by
  have : n.toNat ≠ 0 := fun e => ‹¬n = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.toNat_sub]; simp; omega

def gcdSub (a b : BitVec 64) : BitVec 64 :=
  if a = 0 then b else if b = 0 then a else if a < b then gcdSub a (b - a) else gcdSub (a - b) b
termination_by a.toNat + b.toNat
decreasing_by
  all_goals have ha : a.toNat ≠ 0 := fun e => ‹¬a = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  all_goals have hb : b.toNat ≠ 0 := fun e => ‹¬b = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  · have := ‹a < b›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega
  · have := ‹¬a < b›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega

frontx_compile sumDown
frontx_compile gcdSub

example (a b : BitVec 64) (σ : BState) (h : σ.env 4 = a ∧ σ.env 5 = b) :
    ∃ σ', BExec (prog gcdSub.lay gcdSub.tree 4) σ σ' ∧ σ'.env 4 = gcdSub a b ∧ σ'.heap = σ.heap :=
  gcdSub.exec a b σ h


/-! ## Byte arrays -/

/-- sum of the bytes from `i` on (mod 2^64) -/
def byteSum (xs : ByteArray) (i : Nat) (acc : UInt64) : UInt64 :=
  if h : i < xs.size then byteSum xs (i + 1) (acc + xs[i].toUInt64) else acc
termination_by xs.size - i

/-- index of the first byte equal to `k` at or after `i`, or `xs.size` -/
def find (xs : ByteArray) (k : UInt8) (i : Nat) : Nat :=
  if h : i < xs.size then (if xs[i] = k then i else find xs k (i + 1)) else xs.size
termination_by xs.size - i

/-- number of bytes equal to `k` from `i` on -/
def count (xs : ByteArray) (k : UInt8) (i : Nat) (n : UInt64) : UInt64 :=
  if h : i < xs.size then count xs k (i + 1) (if xs[i] = k then n + 1 else n) else n
termination_by xs.size - i

/-- `xs[i]!` and a `UInt8` accumulator (arithmetic mod 256) -/
def xorAll (xs : ByteArray) (i : Nat) (acc : UInt8) : UInt8 :=
  if i < xs.size then xorAll xs (i + 1) (acc ^^^ xs[i]! + 1) else acc
termination_by xs.size - i

/-- two arrays: `1` if they agree from `i` up to the shorter length, else `0` -/
def eqFrom (xs ys : ByteArray) (i : Nat) : UInt64 :=
  if h : i < xs.size ∧ i < ys.size then (if xs[i] = ys[i] then eqFrom xs ys (i + 1) else 0) else 1
termination_by xs.size - i

frontx_compile byteSum
frontx_compile find
frontx_compile count
frontx_compile xorAll
frontx_compile eqFrom

/-! ## CRC-32 (bitwise, reflected polynomial `0xEDB88320`), 32-bit arithmetic inside 64-bit words -/

def crcBit (c : UInt32) : UInt32 := if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1

def crcByte (c : UInt32) (b : UInt8) : UInt32 :=
  crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (c ^^^ b.toUInt32))))))))

def crcGo (xs : ByteArray) (i : Nat) (c : UInt32) : UInt32 :=
  if h : i < xs.size then crcGo xs (i + 1) (crcByte c xs[i]) else c
termination_by xs.size - i

/-- the usual CRC-32 (PNG, zlib) -/
def crc32 (xs : ByteArray) : UInt32 := crcGo xs 0 0xFFFFFFFF ^^^ 0xFFFFFFFF

frontx_compile crcGo

/-! ## The idioms of lean-svg: recursion on a fuel argument, reads through `at'`, helpers -/

/-- lean-svg `Bytes.at'` (`LeanSvg/Bytes.lean:15`), verbatim -/
@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

/-- lean-svg `Font.b64Digit` (`LeanSvg/Font.lean:554`), verbatim -/
@[inline] def b64Digit (c : UInt8) : UInt32 :=
  if 65 ≤ c && c ≤ 90 then c.toUInt32 - 65
  else if 97 ≤ c && c ≤ 122 then c.toUInt32 - 71
  else if 48 ≤ c && c ≤ 57 then c.toUInt32 + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 64

/-- lean-svg `Png.adlerChunk` (`LeanSvg/Png.lean:113`) with the pair result cut down to its first component
(pair results are not supported) -/
def adlerA (rgba : ByteArray) (i fuel : Nat) (a : UInt64) : UInt64 :=
  match fuel with
  | 0 => a
  | fuel' + 1 =>
    let a' := a + (if _ : i < rgba.size then rgba[i].toUInt64 else 0)
    adlerA rgba (i + 1) fuel' a'

/-- a loop in lean-svg style using both helpers -/
def b64Sum (bs : ByteArray) (i fuel : Nat) (n : UInt32) : UInt32 :=
  match fuel with
  | 0 => n
  | f + 1 => b64Sum bs (i + 1) f (n + b64Digit (at' bs i))

-- `i` is an unbounded `Nat` that the machine holds in 64 bits: the precondition `i + fuel < 2^64` is needed
-- (and is preserved by the recursive call); without it the command fails with the goal `i + 1 < 2^64`.
frontx_compile adlerA with fun _ i fuel _ => i + fuel < 2 ^ 64
frontx_compile b64Sum with fun _ i fuel _ => i + fuel < 2 ^ 64

end Frontx.Ex
end Proven

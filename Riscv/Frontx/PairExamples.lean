/- Round 6: tuples and structures (state of loops, parameters, results written as bytes), `%` / `/` by constants,
`Array.foldl` over the bytes of a `ByteArray`.  Library and book code copied verbatim (provenance per definition);
nothing is proved by hand: the `requires` / `with` clauses are the only human input. -/
import Riscv.Frontx.Impl1
import Riscv.Frontx.DataExamples
import Riscv.Frontx.BookExamples

/-! ## lean-zip Adler-32 (github.com/rowancallahan/lean-zip @ 7e10583), verbatim

`Zip/Spec/Adler32.lean:20,23,29,39,47` and `Zip/Native/Adler32.lean:13,17` (docstrings dropped; no API edits).
`updateBytes` is `data.data.foldl Spec.updateByte s`: the `for` loop over the bytes (`bfoldl_forIn`) with the pair
state `(a, b)` in two variables; `% MOD_ADLER` is one conditional subtraction (the bound `x < 2 * 65521` comes from
the invariant `a, b < 65521`, which is lean-zip's own `Spec.Valid`); `% 65536`, `/ 65536` are a mask and a shift. -/

namespace Adler32.Spec
def MOD_ADLER : Nat := 65521
abbrev State := Nat × Nat
def updateByte (s : State) (byte : UInt8) : State :=
  let a := (s.1 + byte.toNat) % MOD_ADLER
  let b := (s.2 + a) % MOD_ADLER
  (a, b)
def pack (s : State) : UInt32 :=
  (UInt32.ofNat s.2 <<< 16) ||| UInt32.ofNat s.1
def unpack (v : UInt32) : State :=
  (v.toNat % 65536, v.toNat / 65536)
end Adler32.Spec

namespace Adler32.Native
def updateBytes (s : Spec.State) (data : ByteArray) : Spec.State :=
  data.data.foldl Spec.updateByte s
def adler32 (init : UInt32 := 1) (data : ByteArray) : UInt32 :=
  let s := Spec.unpack init
  let s' := updateBytes s data
  Spec.pack s'
end Adler32.Native

namespace Proven.Frontx.Pairs
open Proven Proven.Frontx Proven.Frontx.Data Proven.Frontx.Book

frontx_compile Adler32.Spec.pack
frontx_compile Adler32.Spec.unpack
frontx_compile Adler32.Spec.updateByte requires fun s _ => s.1 < 65521 ∧ s.2 < 65521
frontx_compile Adler32.Native.updateBytes requires fun s _ => s.1 < 65521 ∧ s.2 < 65521
  with fun _ _ _ a b => a < 65521 ∧ b < 65521
frontx_compile Adler32.Native.adler32 requires fun init _ => init.toNat % 65536 < 65521 ∧ init.toNat / 65536 < 65521
  with fun _ _ _ a b => a < 65521 ∧ b < 65521

/-- zlib's `adler32(1, xs)`: 4 bytes -/
def adlerE (xs : ByteArray) : UInt32 := Adler32.Native.adler32 1 xs
frontx_entry adlerE
frontx_implements adlerE

/-- the state after the bytes, from `Spec.init = (1, 0)`: 16 bytes (`a`, `b`, 8 each) -/
def adlerStateE (xs : ByteArray) : Adler32.Spec.State := Adler32.Native.updateBytes (1, 0) xs
frontx_entry adlerStateE
frontx_implements_bytes adlerStateE

/-! ## "Functional Programming in Lean" (github.com/leanprover/fp-lean @ 0abeea5), verbatim

`examples/Examples/Intro.lean:1018` (`PPoint`), `:1203` (`BetterPlicity.replaceX`), `:1879` (`fromOption`),
`examples/Examples/FunctorApplicativeMonad.lean:7,238` (`MythicalCreature`, `small`). -/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

namespace BetterPlicity
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
end BetterPlicity

structure MythicalCreature where
  large : Bool
deriving Repr
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

/-! Entry points (glue, not book code): the arguments are bytes / 16-bit numbers of the input (`u16`). -/

def replaceXAt (xs : ByteArray) (i : Nat) : PPoint Nat :=
  BetterPlicity.replaceX ⟨u16 xs i, u16 xs (i + 2)⟩ (u16 xs (i + 4))
def fromOptionAt (xs : ByteArray) (i : Nat) : Nat :=
  if byteAt xs (i + 1) = 0 then BetterPlicity.fromOption (byteAt xs i).toNat none
  else BetterPlicity.fromOption (byteAt xs i).toNat (some (byteAt xs (i + 2)).toNat)
def smallAt (xs : ByteArray) (i : Nat) : Bool := MythicalCreature.small ⟨byteAt xs i == 1⟩
frontx_compile replaceXAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile fromOptionAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile smallAt requires fun _ i => i + 8 < 2 ^ 64

def replaceXE (xs : ByteArray) : PPoint Nat := replaceXAt xs 0
frontx_entry replaceXE
frontx_implements_bytes replaceXE
def fromOptionE (xs : ByteArray) : Nat := fromOptionAt xs 0
frontx_entry fromOptionE
frontx_implements fromOptionE
def smallE (xs : ByteArray) : Bool := smallAt xs 0
frontx_entry smallE
frontx_implements smallE

/-! ## The structure / tuple examples of `DataExamples.lean`, now with machine theorems -/

def swapAt (xs : ByteArray) (i : Nat) : UInt64 × UInt64 :=
  swap ((byteAt xs i).toUInt64 + ((byteAt xs (i + 1)).toUInt64 <<< 8), (byteAt xs (i + 2)).toUInt64)
def addPointsAt (xs : ByteArray) (i : Nat) : Point :=
  addPoints ⟨(byteAt xs i).toNat, (byteAt xs (i + 1)).toNat⟩ ⟨(byteAt xs (i + 2)).toNat, (byteAt xs (i + 3)).toNat⟩
def zeroXAt (xs : ByteArray) (i : Nat) : Point := zeroX ⟨u16 xs i, u16 xs (i + 2)⟩
/-- a nested tuple result (`(a, b), c`): 1 + 4 + 8 bytes -/
def nestAt (xs : ByteArray) (i : Nat) : (UInt8 × UInt32) × Nat :=
  ((byteAt xs i, (byteAt xs (i + 1)).toUInt32 + 1), (byteAt xs (i + 2)).toNat / 16)
frontx_compile swapAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile addPointsAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile zeroXAt requires fun _ i => i + 8 < 2 ^ 64
frontx_compile nestAt requires fun _ i => i + 8 < 2 ^ 64
/-- `addPoints` on four 16-bit numbers (17 slots) -/
def addPoints16At (xs : ByteArray) (i : Nat) : Point := addPoints ⟨u16 xs i, u16 xs (i + 2)⟩ ⟨u16 xs (i + 4), u16 xs (i + 6)⟩
frontx_compile addPoints16At requires fun _ i => i + 8 < 2 ^ 64

def swapE (xs : ByteArray) : UInt64 × UInt64 := swapAt xs 0
frontx_entry swapE
frontx_implements_bytes swapE
def addPointsE (xs : ByteArray) : Point := addPointsAt xs 0
frontx_entry addPointsE
frontx_implements_bytes addPointsE
def addPoints16E (xs : ByteArray) : Point := addPoints16At xs 0
frontx_entry addPoints16E
frontx_implements_bytes addPoints16E
def zeroXE (xs : ByteArray) : Point := zeroXAt xs 0
frontx_entry zeroXE
frontx_implements_bytes zeroXE
def nestE (xs : ByteArray) : (UInt8 × UInt32) × Nat := nestAt xs 0
frontx_entry nestE
frontx_implements_bytes nestE

end Proven.Frontx.Pairs

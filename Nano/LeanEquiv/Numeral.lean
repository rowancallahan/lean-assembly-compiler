/- Nano/LeanEquiv/Numeral: nano's numeral value `LexSpec.numVal` (decimal, mod 2^64) against Lean's meaning of a
numeral in a `UInt64` position (`instOfNat : OfNat UInt64 n := ⟨UInt64.ofNat n⟩`, Init/Data/UInt/BasicAux).
`decVal` is the unbounded decimal value (the value Lean's `decodeNatLitVal?` computes for a digits-only literal; that
function is `partial` inside, so this link is fuzzed, not proved: Testing/notes/LEAN_EQUIV.md). -/
import Nano.Lexer.Lex2Spec
namespace LeanEquiv
open LexSpec

/-- the decimal value of a digit word, unbounded -/
def decVal (w : List UInt8) : Nat := w.foldl (fun a b => a * 10 + (b.toNat - 48)) 0

theorem numVal_go (w : List UInt8) : ∀ a : Nat,
    w.foldl (fun a b => (a * 10 + (b.toNat - 48)) % 2 ^ 64) (a % 2 ^ 64)
      = w.foldl (fun a b => a * 10 + (b.toNat - 48)) a % 2 ^ 64 := by
  induction w with
  | nil => intro a; rfl
  | cons b w ih =>
    intro a
    have e : ((a % 2 ^ 64) * 10 + (b.toNat - 48)) % 2 ^ 64 = (a * 10 + (b.toNat - 48)) % 2 ^ 64 := by omega
    simp only [List.foldl_cons, e, ih]

/-- nano's value is the decimal value mod 2^64 -/
theorem numVal_eq (w : List UInt8) : numVal w = decVal w % 2 ^ 64 := numVal_go w 0

/-- **numeral meaning**: the `UInt64` nano stores is the `UInt64` Lean's literal `(n : UInt64)` denotes, for the
unbounded decimal value `n` of the digits -/
theorem numVal_eq_lean (w : List UInt8) : UInt64.ofNat (numVal w) = (OfNat.ofNat (decVal w) : UInt64) := by
  show UInt64.ofNat (numVal w) = UInt64.ofNat (decVal w)
  rw [numVal_eq]; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_ofNat']

end LeanEquiv

/- Nano/LeanEquiv/Numeral: nano's numeral value `LexSpec.numVal` (decimal, mod 2^64) against Lean's meaning of a
numeral in a `UInt64` position (`instOfNat : OfNat UInt64 n := ⟨UInt64.ofNat n⟩`, Init/Data/UInt/BasicAux).
`decVal` is the unbounded decimal value (the value Lean's `decodeNatLitVal?` computes for a digits-only literal; that
function is `partial` inside, so this link is fuzzed, not proved: Testing/notes/LEAN_EQUIV.md). -/
import Nano.LeanEquiv.CharClass
import Std.Data.String.ToNat
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

theorem ofDigitChars_go (w : List UInt8) : ∀ a : Nat,
    Nat.ofDigitChars 10 (w.map ch) a = w.foldl (fun a b => a * 10 + (b.toNat - 48)) a := by
  induction w with
  | nil => intro a; simp
  | cons b w ih =>
    intro a
    have hb : (ch b).toNat = b.toNat := by
      have := b.toNat_lt
      simp [ch, Char.ofNat, Nat.isValidChar, show b.toNat < 55296 by omega, Char.ofNatAux, Char.toNat]
    simp [Nat.ofDigitChars_cons, ih, hb, Nat.mul_comm]

/-- **numeral text, subset form**: a word nano accepts as a numeral (non-empty, digits only) is accepted by Lean's
total decimal reader `String.toNat?` with nano's unbounded value.  (`String.toNat?` is not the function Lean's
tokenizer calls; that one, `decodeNatLitVal?`, is `partial` inside.) -/
theorem numeral_sub_toNat? (w : List UInt8) (hne : w ≠ []) (hd : w.all isD = true) :
    (String.ofList (w.map ch)).toNat? = some (decVal w) := by
  have hdig : ∀ c ∈ w.map ch, c.isDigit = true := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact isD_imp_isDigit b (List.all_eq_true.mp hd b hb)
  have hnat : (String.ofList (w.map ch)).isNat = true :=
    String.isNat_of_isDigit (by simpa using hne) (by simpa using hdig)
  have hf : (w.map ch).filter (· != '_') = w.map ch := by
    apply List.filter_eq_self.mpr
    intro c hc
    have := hdig c hc
    simp only [bne_iff_ne, ne_eq]; rintro rfl; revert this; decide
  rw [String.toNat?_eq_some_ofDigitChars hnat]
  simp only [String.toList_ofList, hf, ofDigitChars_go, decVal]

end LeanEquiv

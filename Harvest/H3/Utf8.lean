/- Harvest/H3/Utf8: the byte-level decoding a lexer needs to read a non-ASCII identifier character.  Lean 4.34.1's
`ByteArray.utf8DecodeChar?` (Init/Data/String/Decode.lean:1008) is total and kernel-reducible.  Candidate rule: the
arithmetic decode of a 2/3/4-byte sequence under a guard on the bytes; theorem: under the guard Lean's decoder succeeds
with the same code point.  (Subset form: candidate accepts ⇒ Lean accepts, same value.) -/
import Harvest.H3.LetterLike
namespace H3

abbrev cont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- 2 bytes `110xxxxx 10xxxxxx`, first byte C2..DF -/
def dec2 (b0 b1 : UInt8) : Nat := ((b0.toNat &&& 0x1f) <<< 6) ||| (b1.toNat &&& 0x3f)
def ok2 (b0 b1 : UInt8) : Bool := 0xC2 ≤ b0 && b0 ≤ 0xDF && cont b1

/-- 3 bytes, first byte E1..E2 (no overlong / surrogate special cases; covers U+1000..U+2FFF: subscripts, polytonic
Greek, letterlike block) -/
def dec3 (b0 b1 b2 : UInt8) : Nat := ((b0.toNat &&& 0xf) <<< 12) ||| ((b1.toNat &&& 0x3f) <<< 6) ||| (b2.toNat &&& 0x3f)
def ok3 (b0 b1 b2 : UInt8) : Bool := 0xE1 ≤ b0 && b0 ≤ 0xE2 && cont b1 && cont b2

/-- 4 bytes `F0 9D 92..96 xx`: U+1D480..U+1D5BF, the math alphabets of `isLetterLike` -/
def dec4 (b0 b1 b2 b3 : UInt8) : Nat :=
  ((b0.toNat &&& 0x7) <<< 18) ||| ((b1.toNat &&& 0x3f) <<< 12) ||| ((b2.toNat &&& 0x3f) <<< 6) ||| (b3.toNat &&& 0x3f)
def ok4 (b0 b1 b2 b3 : UInt8) : Bool := b0 == 0xF0 && b1 == 0x9D && 0x92 ≤ b2 && b2 ≤ 0x96 && cont b3

def dc (l : List UInt8) : Option Nat := ((ByteArray.mk l.toArray).utf8DecodeChar? 0).map Char.toNat

/-- bytes of the guard ranges as offsets: `b0 = lo0 + i`, continuation `0x80 + j` -/
private theorem dec2_aux : ∀ i < 30, ∀ j < 64,
    dc [UInt8.ofNat (0xC2 + i), UInt8.ofNat (0x80 + j)] = some (dec2 (UInt8.ofNat (0xC2 + i)) (UInt8.ofNat (0x80 + j))) := by
  decide +kernel
theorem dec2_eq (b0 b1 : UInt8) (h : ok2 b0 b1 = true) : dc [b0, b1] = some (dec2 b0 b1) := by
  simp only [ok2, cont, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h
  have := dec2_aux (b0.toNat - 0xC2) (by simp at h; omega) (b1.toNat - 0x80) (by simp at h; omega)
  rwa [show 0xC2 + (b0.toNat - 0xC2) = b0.toNat by simp at h; omega, show 0x80 + (b1.toNat - 0x80) = b1.toNat by simp at h; omega,
    UInt8.ofNat_toNat, UInt8.ofNat_toNat] at this

private theorem dec3_aux : ∀ i < 2, ∀ j < 64, ∀ k < 64,
    dc [UInt8.ofNat (0xE1 + i), UInt8.ofNat (0x80 + j), UInt8.ofNat (0x80 + k)] =
      some (dec3 (UInt8.ofNat (0xE1 + i)) (UInt8.ofNat (0x80 + j)) (UInt8.ofNat (0x80 + k))) := by
  decide +kernel
theorem dec3_eq (b0 b1 b2 : UInt8) (h : ok3 b0 b1 b2 = true) : dc [b0, b1, b2] = some (dec3 b0 b1 b2) := by
  simp only [ok3, cont, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h
  simp at h
  have := dec3_aux (b0.toNat - 0xE1) (by omega) (b1.toNat - 0x80) (by omega) (b2.toNat - 0x80) (by omega)
  rwa [show 0xE1 + (b0.toNat - 0xE1) = b0.toNat by omega, show 0x80 + (b1.toNat - 0x80) = b1.toNat by omega,
    show 0x80 + (b2.toNat - 0x80) = b2.toNat by omega, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat] at this

private theorem dec4_aux : ∀ k < 5, ∀ l < 64,
    dc [0xF0, 0x9D, UInt8.ofNat (0x92 + k), UInt8.ofNat (0x80 + l)] =
      some (dec4 0xF0 0x9D (UInt8.ofNat (0x92 + k)) (UInt8.ofNat (0x80 + l))) := by
  decide +kernel
theorem dec4_eq (b0 b1 b2 b3 : UInt8) (h : ok4 b0 b1 b2 b3 = true) : dc [b0, b1, b2, b3] = some (dec4 b0 b1 b2 b3) := by
  simp only [ok4, cont, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, beq_iff_eq] at h
  simp at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, h2⟩, h2'⟩, h3⟩ := h
  have := dec4_aux (b2.toNat - 0x92) (by omega) (b3.toNat - 0x80) (by omega)
  rwa [show 0x92 + (b2.toNat - 0x92) = b2.toNat by omega, show 0x80 + (b3.toNat - 0x80) = b3.toNat by omega,
    UInt8.ofNat_toNat, UInt8.ofNat_toNat] at this

/-! Composition: a candidate byte-level identifier-character rule (guard + code-point table) ⇒ Lean decodes the bytes to
a `Char` for which `isIdRest` / `isIdFirst` holds. -/
theorem idRest2 (b0 b1 : UInt8) (h : ok2 b0 b1 = true) (hc : idRestC (dec2 b0 b1) = true) :
    ((ByteArray.mk #[b0, b1]).utf8DecodeChar? 0).map Lean.isIdRest = some true := by
  have := dec2_eq b0 b1 h
  unfold dc at this
  cases hd : (ByteArray.mk #[b0, b1]).utf8DecodeChar? 0 with
  | none => simp [hd] at this
  | some c => simp [hd] at this ⊢; rw [idRest_eq]; exact (show c.val.toNat = _ from this) ▸ hc
theorem idRest3 (b0 b1 b2 : UInt8) (h : ok3 b0 b1 b2 = true) (hc : idRestC (dec3 b0 b1 b2) = true) :
    ((ByteArray.mk #[b0, b1, b2]).utf8DecodeChar? 0).map Lean.isIdRest = some true := by
  have := dec3_eq b0 b1 b2 h
  unfold dc at this
  cases hd : (ByteArray.mk #[b0, b1, b2]).utf8DecodeChar? 0 with
  | none => simp [hd] at this
  | some c => simp [hd] at this ⊢; rw [idRest_eq]; exact (show c.val.toNat = _ from this) ▸ hc
theorem idFirst2 (b0 b1 : UInt8) (h : ok2 b0 b1 = true) (hc : idFirstC (dec2 b0 b1) = true) :
    ((ByteArray.mk #[b0, b1]).utf8DecodeChar? 0).map Lean.isIdFirst = some true := by
  have := dec2_eq b0 b1 h
  unfold dc at this
  cases hd : (ByteArray.mk #[b0, b1]).utf8DecodeChar? 0 with
  | none => simp [hd] at this
  | some c => simp [hd] at this ⊢; rw [idFirst_eq]; exact (show c.val.toNat = _ from this) ▸ hc

/-- worked examples: `α`(CE B1) and `x₁`'s subscript (E2 82 81) -/
example : idFirstC (dec2 0xCE 0xB1) = true ∧ ok2 0xCE 0xB1 = true := by decide +kernel
example : idRestC (dec3 0xE2 0x82 0x81) = true ∧ idFirstC (dec3 0xE2 0x82 0x81) = false ∧ ok3 0xE2 0x82 0x81 = true := by
  decide +kernel
/-- `λ` (CE BB) is accepted by the guard but not by the table: it stays a keyword -/
example : ok2 0xCE 0xBB = true ∧ idFirstC (dec2 0xCE 0xBB) = false ∧ idRestC (dec2 0xCE 0xBB) = false := by decide +kernel

end H3

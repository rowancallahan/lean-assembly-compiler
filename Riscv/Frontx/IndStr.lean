/- `String`s in the inductive path (NOTES section 23): a `String` value is the list of its UTF-8 bytes
(`s.toUTF8`), a chain of cells `Bytes8` (one byte per cell, the `UInt8` field stored as a 1-byte scalar `Fld.b`).

Byte format of a `String` field (`frontx_ind_type`, stated in `Compiler/Ind.lean`'s `C.enc`): the `Bytes8` value
`Bytes8.ofString s`, i.e. per UTF-8 byte `b` of `s` the tag of `cons` and then `b`, then the tag of `nil`; the
tags are the type's constructor count `k` (`nil`) and `k + 1` (`cons`) after the constructors of the types before
it in the shape.  Equality of strings is `Bytes8.eqb` on the chains (`eqb_ofString`). -/
import Riscv.Frontx.Ind

namespace Proven.Frontx.Ind

/-- the bytes of a string, one per cell -/
inductive Bytes8 where
  | nil
  | cons (b : UInt8) (rest : Bytes8)

def Bytes8.ofList : List UInt8 → Bytes8
  | [] => .nil
  | b :: bs => .cons b (ofList bs)

/-- a string as the chain of its UTF-8 bytes -/
def Bytes8.ofString (s : String) : Bytes8 := ofList s.toUTF8.data.toList

/-- equality of byte chains (compiled with the program when a function compares strings) -/
def Bytes8.eqb : Bytes8 → Bytes8 → Bool
  | .nil, .nil => true
  | .cons a r, .cons b s => a == b && eqb r s
  | _, _ => false

theorem Bytes8.eqb_ofList : ∀ (a b : List UInt8), Bytes8.eqb (ofList a) (ofList b) = decide (a = b)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [ofList, eqb, eqb_ofList xs ys, List.cons.injEq]
    by_cases h : x = y <;> by_cases h' : xs = ys <;> simp [h, h']

theorem toUTF8_list_inj {s t : String} (h : s.toUTF8.data.toList = t.toUTF8.data.toList) : s = t := by
  have h1 : s.toUTF8 = t.toUTF8 := by
    cases hs : s.toUTF8; cases ht : t.toUTF8
    rw [hs, ht] at h; simp only at h; rw [Array.toList_inj] at h; rw [h]
  obtain ⟨a, ha⟩ := s; obtain ⟨b, hb⟩ := t
  have : a = b := h1
  subst this; rfl

@[simp] theorem Bytes8.eqb_ofString (s t : String) :
    Bytes8.eqb (ofString s) (ofString t) = decide (s = t) := by
  unfold ofString; rw [eqb_ofList]
  by_cases h : s = t
  · subst h; simp
  · have : s.toUTF8.data.toList ≠ t.toUTF8.data.toList := fun e => h (toUTF8_list_inj e)
    rw [decide_eq_false this, decide_eq_false h]

@[simp] theorem bw_eqz (c : Bool) : Op.eval .eq (bw c) 0#64 = bw (!c) := by cases c <;> rfl

/-- a byte as a word -/
theorem u8_eq (x y : UInt8) :
    Op.eval .eq (BitVec.ofNat 64 x.toNat) (BitVec.ofNat 64 y.toNat) = bw (decide (x = y)) := by
  have e : BitVec.ofNat 64 x.toNat = BitVec.ofNat 64 y.toNat ↔ x = y := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by have := x.toNat_lt; omega), Nat.mod_eq_of_lt (by have := y.toNat_lt; omega)] at this
      exact UInt8.toNat_inj.1 this
    · intro h; rw [h]
  simp only [Op.eval, bw]
  by_cases h : x = y <;> simp [h, e]

@[simp] theorem u8_lt' (x : UInt8) : x.toNat < 256 := x.toNat_lt

theorem u8_lt (x : UInt8) : (BitVec.ofNat 64 x.toNat).toNat < 256 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.toNat_lt; omega)]; exact x.toNat_lt

end Proven.Frontx.Ind

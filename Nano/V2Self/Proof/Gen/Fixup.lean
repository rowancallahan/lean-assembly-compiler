/- The fixup lemma (Astra-11): Gen's jump emission and patching (`g19` / `g20`, Nano/V2Self/C/Gen.lean).
A patched placeholder (`g20 r o p`, no error) is the word C emits for J's `jal x0, (h − p)` — the jump from word p to
the current end h of the code — and every other word is unchanged; `g19` appends the same kind of word.  With
`SimW.encJ` this is the word `sim_stepW` runs. -/
import Nano.V2Self.Proof.Machine.RvEnc
import Nano.V2Self.Proof.Gen.BufL

namespace Fixup

/-- C's jump offset `(b − a) <<< 2` is the two's-complement `4·(b − a)` -/
theorem off_eq (a b : UInt64) : (b - a) <<< 2 = UInt64.ofInt (4 * ((b.toNat : Int) - a.toNat)) := by
  apply UInt64.toBitVec_inj.mp
  rw [SimW.ofInt_bv']
  apply BitVec.eq_of_toNat_eq
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp [UInt64.toBitVec_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ofInt, Nat.shiftLeft_eq]
  omega

/-- the jump word `g13 0 a b` is J's `jal x0 (b − a)` -/
theorem g13_encJ (a b : UInt64) :
    (C.g13 0 a b).toNat = SimW.encJ (.jal 0 ((b.toNat : Int) - a.toNat)) := by
  simp [C.g13, SimW.encJ, off_eq]

/-- **fixup**: patching placeholder `p` makes it the jump to `h = bsize o`; nothing else changes -/
theorem g20_ok (r o : Buf) (p : UInt64) (hp : p.toNat < o.length) :
    (C.g20 r o p).2.length = o.length ∧
    (bget (C.g20 r o p).2 p).toNat = SimW.encJ (.jal 0 (((bsize o).toNat : Int) - p.toNat)) ∧
    ∀ i : UInt64, i.toNat ≠ p.toNat → bget (C.g20 r o p).2 i = bget o i := by
  have e : (C.g20 r o p).2 = bset o p (C.g13 0 p (bsize o)) := by
    unfold C.g20
    by_cases h : (C.g14 p (bsize o) == 1) = true
    · simp only [h, if_true]
    · simp only [h, if_false, Bool.false_eq_true]
  rw [e]
  refine ⟨BufL.length_bset _ _ _, ?_, fun i hi => BufL.bget_bset_other _ _ _ _ (Ne.symm hi)⟩
  rw [BufL.bget_bset_same _ _ _ hp, g13_encJ]

/-- **emit**: `g19 r o 0 b` appends the jump from the new word (index `bsize o`) to word `b` -/
theorem g19_ok (r o : Buf) (b : UInt64) :
    (C.g19 r o 0 b).2 = o ++ [C.g13 0 (bsize o) b] ∧
    (C.g13 0 (bsize o) b).toNat = SimW.encJ (.jal 0 ((b.toNat : Int) - (bsize o).toNat)) := by
  refine ⟨?_, g13_encJ _ _⟩
  unfold C.g19
  by_cases h : (C.g14 (bsize o) b == 1) = true
  · simp only [h, if_true]; rfl
  · simp only [h, if_false, Bool.false_eq_true]; rfl

end Fixup

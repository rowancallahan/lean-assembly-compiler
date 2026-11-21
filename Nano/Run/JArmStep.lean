/- E4, the per-atom obligation of the nano translator (statement; one lemma per atom code, to be proved from
`JArmBits`): at J pc `q` of Gen's words `Cj.map encG`, when the atom selection gives code `t` (`candC`, = `e35` by
`e35_eq`) and the translator's check `e37` passes,
* the spec has an atom `T` there (`mkAtom`), it is the head of the rest of the program (`atomize`'s check), `T.ok`;
* it kills no register, has at most 4 words; `e36` is its J length; `e65` is its jump target (if any);
* `e40` appends its A64 words `T.a π q h`, with `π p` = the translator's table lookup `e59 z p` and `h` the word count
  so far (any buffers `z`, `o`: offsets are computed modulo 2^64 on both sides).
`StepAt t` for the 21 codes gives `StepOK` (`stepOK_of`), which the pass proofs (JArmPass.lean) consume. -/
import Nano.Run.JArmCand
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-- the word index the translator reads for J pc `p` from its boundary table `z` -/
def zpi (z : Buf) (p : Nat) : Nat := (e59 z p.toUInt64).toNat

/-- the obligation for atom code `t` -/
def StepAt (t : UInt64) : Prop :=
  ∀ (Cj : List J), (∀ j ∈ Cj, JOK j) → Cj.length < 2 ^ 18 → ∀ (q : Nat), q < Cj.length →
    candC (Cj.drop q) = t →
    e37 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 t ≠ 0 →
    ∃ T : NTm, mkAtom t (Cj.drop q) = some T ∧ (Cj.drop q).take T.j.length = T.j ∧ T.ok = true ∧
      T.kills 5 = false ∧ T.kills 6 = false ∧ T.alen ≤ 4 ∧
      e36 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 t = T.j.length.toUInt64 ∧
      (∀ p ∈ T.tg q, p < 2 ^ 62 ∧ e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 t = p.toUInt64) ∧
      ∀ (z o : Buf),
        e40 (Cj.map encG) (bsize (Cj.map encG)) z o q.toUInt64 t = o ++ (T.a (zpi z) q o.length).map Nat.toUInt64

/-- the obligation for every code -/
def StepOK : Prop := ∀ t : UInt64, t ≠ 0 → StepAt t

theorem ite_mem {c : Prop} [Decidable c] {a b : UInt64} {S : List UInt64} (ha : a ∈ S) (hb : b ∈ S) :
    (if c then a else b) ∈ S := by
  split <;> assumption

/-- the codes `candC` produces -/
theorem candC_codes (l : List J) : candC l ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22] : List UInt64) := by
  unfold candC
  simp only []
  repeat' (first | decide | apply ite_mem)

/-- the 21 per-code lemmas give `StepOK` -/
theorem stepOK_of (h1 : StepAt 1) (h2 : StepAt 2) (h3 : StepAt 3) (h4 : StepAt 4) (h5 : StepAt 5) (h6 : StepAt 6)
    (h7 : StepAt 7) (h8 : StepAt 8) (h9 : StepAt 9) (h10 : StepAt 10) (h11 : StepAt 11) (h12 : StepAt 12)
    (h13 : StepAt 13) (h14 : StepAt 14) (h15 : StepAt 15) (h16 : StepAt 16) (h18 : StepAt 18) (h19 : StepAt 19)
    (h20 : StepAt 20) (h21 : StepAt 21) (h22 : StepAt 22) : StepOK := by
  intro t ht Cj hJ hl q hq hc
  have hm := candC_codes (Cj.drop q)
  rw [hc] at hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ht
  · exact h1 Cj hJ hl q hq hc
  · exact h2 Cj hJ hl q hq hc
  · exact h3 Cj hJ hl q hq hc
  · exact h4 Cj hJ hl q hq hc
  · exact h5 Cj hJ hl q hq hc
  · exact h6 Cj hJ hl q hq hc
  · exact h7 Cj hJ hl q hq hc
  · exact h8 Cj hJ hl q hq hc
  · exact h9 Cj hJ hl q hq hc
  · exact h10 Cj hJ hl q hq hc
  · exact h11 Cj hJ hl q hq hc
  · exact h12 Cj hJ hl q hq hc
  · exact h13 Cj hJ hl q hq hc
  · exact h14 Cj hJ hl q hq hc
  · exact h15 Cj hJ hl q hq hc
  · exact h16 Cj hJ hl q hq hc
  · exact h18 Cj hJ hl q hq hc
  · exact h19 Cj hJ hl q hq hc
  · exact h20 Cj hJ hl q hq hc
  · exact h21 Cj hJ hl q hq hc
  · exact h22 Cj hJ hl q hq hc

end JT

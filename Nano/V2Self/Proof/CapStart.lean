/- Opus box E: the start code at the capacity exit: setup, then main's kinded semantics fails with `cap` ⇒ the run
reaches the cap stub (word 6) with main's invariant, the start registers kept. -/
import Nano.V2Self.Proof.CapProg
import Nano.V2Self.Proof.StartAllS
namespace Templates
open CallProbe SimW

theorem start_capX {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {S w hb E0 : Nat} {IG : St → Prop} {Sd : SemDX}
    (hC : C.all dstOk = true) (h0 : At C 0 (stubJ S)) (hS : At C S (startJ S w)) (hM : CapD fk tg KL C w 0 IG hb E0 Sd)
    (s0 : St) (z0 : s0.x 0 = 0) (hhb : hb = (s0.x 12).toNat + 16) (ha8 : (s0.x 12).toNat % 8 = 0)
    (hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0) (hroom : hb ≤ E0) (hE62 : E0 < 2 ^ 62)
    (hret : s0.b + 4 * (S + 12) < 2 ^ 64)
    (hIG : ∀ s1, Entry s0 s1 S → IG s1) (hSd : Sd [] E0 ⟨hb, fun _ => none⟩ = .error fk)
    (hlo : KL.lo ≤ (s0.x 12).toNat) (hhi : E0 ≤ KL.hi) (hbase : s0.b = KL.base) (hE8 : E0 % 8 = 0)
    (hCl : S + 32 ≤ C.length) (hC18 : C.length < 2 ^ 18) (hwl : w < C.length) :
    ∃ s2, SStarX KL C (0, s0) (tg, s2) ∧ IG s2 ∧ s2.x 0 = 0 ∧ (∀ j, keepR j = true → s2.x j = s0.x j) ∧ s2.b = s0.b := by
  subst hhb hE0
  have l12 := (s0.x 12).toNat_lt
  obtain ⟨s1, h1, en⟩ := start_setupX (K := KL) h0 hS s0 z0 (by omega) hroom ⟨hlo, by omega, ha8⟩
    ⟨by omega, by omega, by omega⟩ hCl hC18 hwl
  have b1 : s1.b = s0.b := by rw [h1.star.b]
  have R1 : HRel ((s0.x 12).toNat + 16) s1 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ := by
    refine ⟨by omega, Nat.le_refl _, by rw [en.x31]; exact hroom, by simp; omega, ?_, fun _ _ _ _ h => by simp at h⟩
    rw [en.x30]; simp; omega
  obtain ⟨s2, h2, I2, z2⟩ := hM.cap s1 [] _ (S + 12) (hIG s1 en) en.x0 R1 rfl
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [en.x31]; omega) hE62 (by rw [en.x1, b1]) (by rw [b1]; exact hret)
    (by omega) hhi (by rw [b1, hbase]) (by rw [en.x31]; omega) (fun _ _ h => by simp at h)
    (by rw [en.x31]; exact hSd)
  have h12 := h1.trans h2
  exact ⟨s2, h12, I2, z2, fun j hj => star_keep hC h12.star hj, h12.star.b⟩

end Templates

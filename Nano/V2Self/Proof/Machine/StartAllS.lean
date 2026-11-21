/- EVS P7a (Opus box E): the whole start code as a SAFE run (`start_runX`): setup, main by `DefXS`, tail. -/
import Nano.V2Self.Proof.Machine.StartRun
import Nano.V2Self.Proof.Machine.NoW
import Nano.V2Self.Proof.Machine.StartSafe
import Nano.V2Self.Proof.Machine.EVSDefs
namespace Templates
open CallProbe SimW

theorem start_runX {KL : LayW} {C : List J} {S w hb E0 : Nat} {IG : St → Prop}
    {Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)}
    (hC : C.all dstOk = true) (h0 : At C 0 (stubJ S)) (hS : At C S (startJ S w)) (hM : DefXS KL C w 0 1 IG hb E0 Sd)
    (s0 : St) (z0 : s0.x 0 = 0) (hhb : hb = (s0.x 12).toNat + 16) (ha8 : (s0.x 12).toNat % 8 = 0)
    (hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0) (hroom : hb ≤ E0) (hE62 : E0 < 2 ^ 62)
    (hret : s0.b + s0.lo (S + 12) < 2 ^ 64)
    (hIG : ∀ s1, Entry s0 s1 S → IG s1)
    (hIGm : ∀ s, IG s → s.m (s0.x 12).toNat = s0.x 1 ∧ s.m ((s0.x 12).toNat + 8) = s0.x 8)
    {vs : List UInt64} {H' : Hp} (hSd : Sd [] E0 ⟨hb, fun _ => none⟩ = some (vs, H'))
    {N : UInt64} {bs : Nat → UInt64}
    (hN : H'.m (vs.getD 0 0).toNat = some N) (hPb : hb ≤ (vs.getD 0 0).toNat)
    (hPN : (vs.getD 0 0).toNat + 16 + 8 * N.toNat ≤ H'.top)
    (hbs : ∀ i, i < N.toNat → H'.m ((vs.getD 0 0).toNat + 16 + 8 * i) = some (bs i))
    (hQ : (s0.x 13).toNat + N.toNat < 2 ^ 64)
    (hout : (s0.x 13).toNat + N.toNat ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 13).toNat)
    (hlo : KL.lo ≤ (s0.x 12).toNat) (hhi : E0 ≤ KL.hi) (hbase : s0.b = KL.base) (hE8 : E0 % 8 = 0)
    (hCl : S + 32 ≤ C.length) (hC18 : C.length < 2 ^ 18) (hwl : w < C.length)
    (hwO : ∀ i, i < N.toNat → sok KL ((s0.x 13).toNat + i)) :
    ∃ s3, SStarX KL C (0, s0) (S + 31, s3) ∧ C[S + 31]? = some (.jalr 0 1) ∧ s3.b = s0.b ∧ s3.x 1 = s0.x 1 ∧ s3.x 8 = s0.x 8 ∧
      s3.x 10 = (if N = 0 then 1 else 0) ∧ s3.x 11 = N ∧
      ∀ i, i < N.toNat → lbm s3.m ((s0.x 13).toNat + i) = bs i &&& 255 := by
  subst hhb hE0
  have l12 := (s0.x 12).toNat_lt
  obtain ⟨s1, h1, en⟩ := start_setupX (K := KL) h0 hS s0 z0 (by omega) hroom ⟨hlo, by omega, ha8⟩
    ⟨by omega, by omega, by omega⟩ hCl hC18 hwl
  have b1 : s1.b = s0.b := by rw [h1.star.b]
  have w1 : s1.lo = s0.lo := St.w_eq h1.star.w
  have R1 : HRel ((s0.x 12).toNat + 16) s1 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ := by
    refine ⟨by omega, Nat.le_refl _, by rw [en.x31]; exact hroom, by simp; omega, ?_, fun _ _ _ _ h => by simp at h⟩
    rw [en.x30]; simp; omega
  obtain ⟨s2, h2, I2, z2, x31, vl, vv, x8, R2, A2, -⟩ := hM.run s1 [] _ vs H' (S + 12) (hIG s1 en) en.x0 R1 rfl
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [en.x31]; omega) hE62 (by rw [en.x1, b1, w1]) (by rw [b1, w1]; exact hret)
    (by omega) hhi (by rw [b1, hbase]) (by rw [en.x31]; omega) (fun _ _ h => by simp at h)
    (by rw [en.x31]; exact hSd)
  have b2 : s2.b = s0.b := by rw [h2.star.b, b1]
  have k12 : s2.x 12 = s0.x 12 := by rw [star_keep hC h2.star rfl, en.x12]
  have k13 : s2.x 13 = s0.x 13 := by rw [star_keep hC h2.star rfl, en.x13]
  rw [en.x31] at x31; simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at x31
  obtain ⟨_, _, htop, htop8, _, hHI⟩ := R2
  have hP2 : s2.m (s2.x 31).toNat = vs.getD 0 0 := by
    have := vv 0 (by omega); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one] at this
    rw [x31]; rw [en.x31] at this; exact this
  have hN2 : s2.m (vs.getD 0 0).toNat = N := hHI _ _ hPb (by omega) hN
  obtain ⟨ra, s8⟩ := hIGm s2 I2
  have l31 := (s2.x 31).toNat_lt
  have aP := A2 _ _ hN
  obtain ⟨s3, h3, c31, b3, x1, x8', -, x10, x11, hby⟩ := start_tailX (KL := KL) hS s2 z2 (by rw [k12]; omega)
    (by rw [hP2, hN2]; omega) (by rw [hP2, hN2, k13]; exact hQ)
    (by
      rw [hP2, hN2, k12, k13]
      intro i hi hk
      rcases hk with hk | hk | ⟨j, hj, hk⟩ <;> rcases hout with ho | ho <;> omega)
    hCl ⟨by omega, by omega, by omega⟩ (by rw [hP2]; exact ⟨by omega, by omega, aP⟩)
    (by rw [k12]; exact ⟨hlo, by omega, ha8⟩) (by rw [k12]; exact ⟨by omega, by omega, by omega⟩)
    (fun i hi => by rw [hP2]; rw [hP2, hN2] at hi; exact ⟨by omega, by omega, by omega⟩)
    (fun i hi => by rw [k13]; rw [hP2, hN2] at hi; exact hwO i hi)
  rw [k12, ra] at x1
  rw [k12, s8] at x8'
  rw [hP2, hN2] at x10 x11 hby
  refine ⟨s3, h1.trans (h2.trans h3), c31, by rw [b3, b2], x1, x8', x10, x11, fun i hi => ?_⟩
  rw [← k13, hby i hi, hHI _ _ (by omega) (by omega) (hbs i hi)]

end Templates

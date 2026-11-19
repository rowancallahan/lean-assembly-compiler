/- EVS P7 (Opus box E): **Gen's program on Sail**.  `gen_runS`: on g41 success, the emitted program C (stubs ++ def
templates ++ start code) runs from word 0 as a SafeX J run to the host's return address with main's buffer bytes at a3;
given the Sail code words are Gen's (`KL.W = C.map encG`), `SimW.sim_starX` turns it into retired Sail instructions
keeping `RelW`. -/
import Nano.V2Self.Proof.GenRun
import Nano.V2Self.Proof.EVSProg
import Nano.V2Self.Proof.StartAllS
import Nano.V2Self.Proof.TmGood
namespace Templates
open CallProbe C GenRef ParSpec

theorem gen_runS (KL : SimW.LayW) (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d)
    (s0 : St) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      (
        let P := pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (fun i => lbm s0.m ((s0.x 10).toNat + i)) T
        let D := defsJ P ds 0 hs.length
        let C := stubJ (11 + D.length) ++ D ++ startJ (11 + D.length) (P.T (hs.length - 1))
        g41 c (serialize ds) = g40 16777216 c (C.map encG) 0 [] ∧
        ((∀ k, k < hs.length → ScV (scAt P ds k) (dA ds k).body ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) →
         ∀ E0, ((s0.x 2 >>> 3) <<< 3).toNat = E0 → s0.x 0 = 0 → (s0.x 12).toNat % 8 = 0 →
         (s0.x 12).toNat + 16 ≤ E0 → E0 < 2 ^ 62 → s0.b + 4 * C.length < 2 ^ 64 →
         (s0.x 10).toNat + (s0.x 11).toNat < 2 ^ 63 →
         ((s0.x 10).toNat + (s0.x 11).toNat ≤ (s0.x 12).toNat ∨ E0 + 8 ≤ (s0.x 10).toNat) →
         ∀ vs H', semAt P ds (hs.length - 1) [] E0 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ = some (vs, H') →
         ∀ (N : UInt64) (bs : Nat → UInt64), H'.m (vs.getD 0 0).toNat = some N →
         (s0.x 12).toNat + 16 ≤ (vs.getD 0 0).toNat → (vs.getD 0 0).toNat + 16 + 8 * N.toNat < H'.top →
         (∀ i, i < N.toNat → H'.m ((vs.getD 0 0).toNat + 16 + 8 * i) = some (bs i)) →
         (s0.x 13).toNat + N.toNat < 2 ^ 64 →
         ((s0.x 13).toNat + N.toNat ≤ (s0.x 12).toNat ∨ E0 + 8 ≤ (s0.x 13).toNat) →
         KL.lo ≤ (s0.x 12).toNat → E0 ≤ KL.hi → s0.b = KL.base →
         (∀ i, i < (s0.x 11).toNat → SimW.wok KL ((s0.x 10).toNat + i - ((s0.x 10).toNat + i) % 8)) →
         (∀ i, i < N.toNat → SimW.wok KL ((s0.x 13).toNat + i - ((s0.x 13).toNat + i) % 8)) →
         (∃ j, (s0.x 1).toNat = KL.base + 4 * j) →
         ∃ s3, SimW.SStarX KL C (0, s0) (((s0.x 1).toNat - s0.b) / 4, s3) ∧ s3.b = s0.b ∧ s3.x 1 = s0.x 1 ∧
           s3.x 8 = s0.x 8 ∧ s3.x 10 = (if N = 0 then 1 else 0) ∧ s3.x 11 = N ∧
           (∀ i, i < N.toNat → lbm s3.m ((s0.x 13).toNat + i) = bs i &&& 255) ∧
           (KL.Ok → KL.W = (C.map encG).map UInt64.toNat → ∀ t, SimW.RelW KL (0, s0) t →
             ∃ n t', Proven.Steps n t t' ∧ SimW.RelW KL (((s0.x 1).toNat - s0.b) / 4, s3) t'))) := by
  obtain ⟨hs, T, o, hD, hne, hr⟩ := gen_C c ds hXl h hdb ((s0.x 12).toNat + 16) (s0.x 11)
    (fun i => lbm s0.m ((s0.x 10).toNat + i))
  refine ⟨hs, T, o, hD, hne, ?_⟩
  obtain ⟨hg, np, nr, hcl, hopv, hbd, hTp, hpk, -⟩ := hr
  refine ⟨hg, ?_⟩
  intro hpar E0 hE0 z0 ha8 hroom hE62 hcb hin63 hin vs H' hSd N bs hN hPb hPN hbs hQ hout hlo hhi hbase
    hinw hwO hra
  have hE8 : E0 % 8 = 0 := by
    rw [← hE0]; simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]; simp; omega
  generalize hPd : pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (fun i => lbm s0.m ((s0.x 10).toNat + i)) T = P at *
  have hPhb : P.hb = (s0.x 12).toNat + 16 := by rw [← hPd]; rfl
  have hPc : P.c29 = s0.x 11 := by rw [← hPd]; rfl
  have hPi : P.inp = fun i => lbm s0.m ((s0.x 10).toNat + i) := by rw [← hPd]; rfl
  generalize hDd : defsJ P ds 0 hs.length = D at *
  generalize hCd : stubJ (11 + D.length) ++ D ++ startJ (11 + D.length) (P.T (hs.length - 1)) = C at *
  have hc18 : C.length < 2 ^ 18 := by rw [← hCd]; simp [stubJ, startJ]; omega
  have AC : At C 0 C := fun i _ => by simp
  have A0 : At C 0 (stubJ (11 + D.length)) := by rw [← hCd] at AC ⊢; exact AC.left.left
  have AD : At C (g34 bnew).length D := by
    rw [g34_len]; rw [← hCd] at AC ⊢; exact AC.left.right
  have AS : At C (11 + D.length) (startJ (11 + D.length) (P.T (hs.length - 1))) := by
    rw [← hCd] at AC ⊢; exact At.cast (At.right AC) (by simp; rfl)
  have hsl : 0 < hs.length := List.length_pos_iff.mpr hne
  have hM := gen_defs_runS P ds C (IGs s0 (fun i => lbm s0.m ((s0.x 10).toNat + i))) E0 (s0.x 10) KL
    hs.length (g34 bnew).length (by rw [hPhb]; exact IGs_ok s0 _ E0 hin) hE62
    (fun s hs => by rw [hs.2.2.2.2.2]; exact hcb)
    (fun s hs => by rw [hPc, hPi]; exact ⟨hs.1, hs.2.1, hs.2.2.1, hin63⟩)
    (fun s hs i hi => by rw [hs.1, hs.2.1] at *; exact hinw i hi) hc18 (by rw [hDd]; exact AD)
    (fun j hj => hTp j hj)
    (fun k hk => by
      obtain ⟨a3, a4⟩ := hpar k hk
      obtain ⟨b1, b2⟩ := hpk k hk a3
      obtain ⟨c1, c2, c3, c4⟩ := hbd k hk
      exact ⟨by omega, c4, b1, b2, a4, hopv k hk, c2, c3⟩) (hs.length - 1) (by omega)
  rw [np, nr] at hM
  have hok : C.all dstOk = true := by
    rw [← hCd]; simp only [List.all_append, stubJ_ok, startJ_ok, Bool.and_true, Bool.true_and]
    rw [← hDd]; exact defsJ_ok P ds 0 hs.length
  have lC : 11 + D.length + 32 ≤ C.length := by rw [← hCd]; simp [stubJ, startJ]; omega
  have hwl : P.T (hs.length - 1) < C.length := by
    have hA := At_defsJ hs.length 0 (g34 bnew).length (by rw [hDd]; exact AD)
      (fun j hj => by rw [Nat.zero_add]; exact hTp j hj) (hs.length - 1) (by omega)
    rw [Nat.zero_add] at hA
    have := At.len hA (defT_ne _ _ _ _)
    have : 0 < (defT (scAt P ds (hs.length - 1)) (dA ds (hs.length - 1)).body (P.T (hs.length - 1))
      (dA ds (hs.length - 1)).nres).length := List.length_pos_iff.mpr (defT_ne _ _ _ _)
    omega
  obtain ⟨s3, h3, r1, r2, r3, r4, r5, r6⟩ := start_runX (KL := KL) hok A0 AS hM s0 z0 hPhb ha8 hE0 (by rw [hPhb]; exact hroom) hE62 (by have := lC; omega)
    (fun s1 en => ⟨en.x28, en.x29, fun i hi => by
        rw [en.m]
        have := Nat.mod_lt ((s0.x 10).toNat + i) (show 8 > 0 by omega)
        exact lbm_eq (by rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]),
      by rw [en.m, upd_other _ _ (by omega), upd_same], by rw [en.m, upd_same], en.b⟩)
    (fun s hs => ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩) (by rw [hPhb]; exact hSd) hN (by rw [hPhb]; exact hPb) hPN hbs hQ hout hlo hhi hbase hE8 (by omega) hc18
    hwl hwO hra
  refine ⟨s3, h3, r1, r2, r3, r4, r5, r6, fun hK hW t hR => SimW.sim_starX hK ?_ h3 hR⟩
  rw [hW, ← hCd, ← hDd]
  exact words_encJX (prog_good P ds _ _ hs.length (fun k hk => by
    obtain ⟨c1, c2, c3, c4⟩ := hbd k hk
    exact ⟨c2, c4, c3, (hpar k hk).1, hopv k hk⟩))

end Templates

/- Machine bridge (Opus box E): Gen's final words are the J program `stubJ S ++ defsJ ++ startJ S w` (w = main's
start word), and running it from word 0 outputs main's buffer (`start_run` with every def's `DefX` from `gen_top`). -/
import Nano.V2Self.Proof.StartAll
namespace Templates
open CallProbe C GenRef ParSpec

theorem defsJ_ge (P : PC) (ds : List DefA) : ∀ k n, n ≤ (defsJ P ds k n).length
  | _, 0 => Nat.le_refl _
  | k, n + 1 => by
    have := defsJ_ge P ds (k + 1) n
    simp [defsJ, defT, proA, pushA, push]; omega

theorem gen_C (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d) (h251 : ∀ d ∈ ds, d.npw < 251 ∧ d.nres < 251)
    (hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      (o.length < 2 ^ 24 →
        g41 c (serialize ds) = g40 16777216 c ((stubJ (11 + (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).length) ++
          defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length ++
          startJ (11 + (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).length)
            ((pcOf 524288 hb c29 inp T).T (hs.length - 1))).map encG) 0 [] ∧
        (dA ds (hs.length - 1)).npw = 0 ∧ (dA ds (hs.length - 1)).nres = 1 ∧
        (∀ k, k < hs.length → OpV (dA ds k).body) ∧
        ∀ (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64), IGOK hb E0 IG → E0 < 2 ^ 62 →
          (∀ s, IG s → s.b + 4 * C.length < 2 ^ 64) → InpOK IG c28 c29 inp →
          At C (g34 bnew).length (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length) →
          (∀ k, k < hs.length → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧
            ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) →
          ∀ k, k < hs.length → DefX C ((pcOf 524288 hb c29 inp T).T k) (dA ds k).npw (dA ds k).nres IG hb E0
            (semAt (pcOf 524288 hb c29 inp T) ds k)) := by
  obtain ⟨hs, T, o, hD, hne, hg, l2, l5, hrest⟩ := gen_top c ds hXl h hdb h251 hb c29 inp
  refine ⟨hs, T, o, hD, hne, fun hol => ?_⟩
  obtain ⟨ho, hhd, hX⟩ := hrest hol
  have hsl : 0 < hs.length := List.length_pos_iff.mpr hne
  have hlast : hs.getLastD 0 = hs.getD (hs.length - 1) 0 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]; simp [List.getD_eq_getElem?_getD]
  obtain ⟨h2, h5, -⟩ := hhd (hs.length - 1) (by omega)
  rw [← hlast, l2] at h2; rw [← hlast, l5] at h5
  obtain ⟨_, dnp, _, _, dnr, _⟩ := DB_dA hdb (hs.length - 1)
  have np : (dA ds (hs.length - 1)).npw = 0 := by
    have := congrArg UInt64.toNat h2; simp [Nat.toUInt64] at this; omega
  have nr : (dA ds (hs.length - 1)).nres = 1 := by
    have := congrArg UInt64.toNat h5; simp [Nat.toUInt64] at this; omega
  refine ⟨?_, np, nr, fun k hk => (hhd k hk).2.2, hX⟩
  have hTl : T.length = hs.length := by have := (DefsC.prefix hD).2; simpa [bnew] using this
  have hT1 : bsize T - 1 = (hs.length - 1).toUInt64 := by
    unfold bsize; rw [hTl]
    have : hs.length < 2 ^ 64 := by
      have := defsJ_ge (pcOf 524288 hb c29 inp T) ds 0 hs.length
      have := congrArg List.length ho; simp at this; omega
    apply UInt64.toNat_inj.mp
    simp only [Nat.toUInt64]
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp; omega
  have hDl := congrArg List.length ho; simp only [List.length_append, List.length_map, g34_len] at hDl
  have sl : ∀ S, (stubJ S).length = 11 := fun _ => rfl
  rw [hg, hT1, ho, stubs_exact _ (by simp; omega), startW_exact _ _ (by simp [sl]; omega)]
  simp [pcOf, sl]

/-- the start code's global invariant: input registers and bytes, the ra / s0 save slots, the code base -/
def IGs (s0 : St) (inp : Nat → UInt64) : St → Prop := fun s =>
  s.x 28 = s0.x 10 ∧ s.x 29 = s0.x 11 ∧ (∀ i, i < (s0.x 11).toNat → lbm s.m ((s0.x 10).toNat + i) = inp i) ∧
  s.m (s0.x 12).toNat = s0.x 1 ∧ s.m ((s0.x 12).toNat + 8) = s0.x 8 ∧ s.b = s0.b

theorem lbm_eq {m m' : Nat → UInt64} {a : Nat} (h : m' (a - a % 8) = m (a - a % 8)) : lbm m' a = lbm m a := by
  unfold lbm; rw [h]

theorem IGs_ok (s0 : St) (inp : Nat → UInt64) (E0 : Nat)
    (hin : (s0.x 10).toNat + (s0.x 11).toNat ≤ (s0.x 12).toNat ∨ E0 + 8 ≤ (s0.x 10).toNat) :
    IGOK ((s0.x 12).toNat + 16) E0 (IGs s0 inp) := by
  intro s s' ⟨i28, i29, iin, ira, is8, ib⟩ e28 e29 eb hm
  refine ⟨by rw [e28, i28], by rw [e29, i29], fun i hi => ?_, by rw [hm _ (by omega), ira],
    by rw [hm _ (by omega), is8], by rw [eb, ib]⟩
  rw [lbm_eq (hm _ (by have := Nat.mod_lt ((s0.x 10).toNat + i) (show 8 > 0 by omega); omega)), iin i hi]

/-- **Gen's program runs**: on g41 success its words are `C.map encG`; from word 0 with the host's registers, C runs
main (the last def, 0 params, 1 result) per `semAt` and returns to ra with main's buffer bytes at a3, a0/a1 set. -/
theorem gen_run (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d) (h251 : ∀ d ∈ ds, d.npw < 251 ∧ d.nres < 251)
    (s0 : St) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      (o.length < 2 ^ 24 →
        let P := pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (fun i => lbm s0.m ((s0.x 10).toNat + i)) T
        let D := defsJ P ds 0 hs.length
        let C := stubJ (11 + D.length) ++ D ++ startJ (11 + D.length) (P.T (hs.length - 1))
        g41 c (serialize ds) = g40 16777216 c (C.map encG) 0 [] ∧
        ((∀ k, k < hs.length → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧
            ScV (scAt P ds k) (dA ds k).body ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) →
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
         ∃ s3, Star C (0, s0) (((s0.x 1).toNat - s0.b) / 4, s3) ∧ s3.b = s0.b ∧ s3.x 1 = s0.x 1 ∧
           s3.x 8 = s0.x 8 ∧ s3.x 10 = (if N = 0 then 1 else 0) ∧ s3.x 11 = N ∧
           ∀ i, i < N.toNat → lbm s3.m ((s0.x 13).toNat + i) = bs i &&& 255)) := by
  obtain ⟨hs, T, o, hD, hne, hr⟩ := gen_C c ds hXl h hdb h251 ((s0.x 12).toNat + 16) (s0.x 11)
    (fun i => lbm s0.m ((s0.x 10).toNat + i))
  refine ⟨hs, T, o, hD, hne, fun hol => ?_⟩
  obtain ⟨hg, np, nr, -, hX⟩ := hr hol
  refine ⟨hg, ?_⟩
  intro hpar E0 hE0 z0 ha8 hroom hE62 hcb hin63 hin vs H' hSd N bs hN hPb hPN hbs hQ hout
  generalize pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (fun i => lbm s0.m ((s0.x 10).toNat + i)) T = P at *
  generalize hDd : defsJ P ds 0 hs.length = D at *
  generalize hCd : stubJ (11 + D.length) ++ D ++ startJ (11 + D.length) (P.T (hs.length - 1)) = C at *
  have AC : At C 0 C := fun i _ => by simp
  have A0 : At C 0 (stubJ (11 + D.length)) := by rw [← hCd] at AC ⊢; exact AC.left.left
  have AD : At C (g34 bnew).length D := by
    rw [g34_len]; rw [← hCd] at AC ⊢; exact AC.left.right
  have AS : At C (11 + D.length) (startJ (11 + D.length) (P.T (hs.length - 1))) := by
    rw [← hCd] at AC ⊢; exact At.cast (At.right AC) (by simp; rfl)
  have hsl : 0 < hs.length := List.length_pos_iff.mpr hne
  have hM := hX C (IGs s0 (fun i => lbm s0.m ((s0.x 10).toNat + i))) E0 (s0.x 10) (IGs_ok s0 _ E0 hin) hE62
    (fun s hs => by rw [hs.2.2.2.2.2]; exact hcb)
    (fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1, hin63⟩) AD hpar (hs.length - 1) (by omega)
  rw [np, nr] at hM
  have hok : C.all dstOk = true := by
    rw [← hCd]; simp only [List.all_append, stubJ_ok, startJ_ok, Bool.and_true, Bool.true_and]
    rw [← hDd]; exact defsJ_ok P ds 0 hs.length
  have lC : 11 + D.length + 12 ≤ C.length := by rw [← hCd]; simp [stubJ, startJ]; omega
  exact start_run hok A0 AS hM s0 z0 rfl ha8 hE0 hroom hE62 (by omega)
    (fun s1 en => ⟨en.x28, en.x29, fun i hi => by
        rw [en.m]
        have := Nat.mod_lt ((s0.x 10).toNat + i) (show 8 > 0 by omega)
        exact lbm_eq (by rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]),
      by rw [en.m, upd_other _ _ (by omega), upd_same], by rw [en.m, upd_same], en.b⟩)
    (fun s hs => ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩) hSd hN hPb hPN hbs hQ hout

end Templates

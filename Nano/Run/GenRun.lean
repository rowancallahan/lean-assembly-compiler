/- Machine bridge (Opus box E): Gen's final words are the J program `stubJ S ++ defsJ ++ startJ S w` (w = main's
start word).  The run itself is `gen_runS` (GenRunS.lean, safe contracts). -/
import Nano.Run.StartRun
import Nano.Run.NoW
namespace Templates
open CallProbe C GenRef ParSpec

theorem defsJ_ge (P : PC) (ds : List DefA) : ∀ k n, n ≤ (defsJ P ds k n).length
  | _, 0 => Nat.le_refl _
  | k, n + 1 => by
    have := defsJ_ge P ds (k + 1) n
    simp [defsJ, defT, proA, pushA, push]; omega

theorem gen_C (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d)
    (hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      (
        g41 c (serialize ds) = g40 16777216 c ((stubJ (11 + (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).length) ++
          defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length ++
          startJ (11 + (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).length)
            ((pcOf 524288 hb c29 inp T).T (hs.length - 1))).map encG) 0 [] ∧
        (dA ds (hs.length - 1)).npw = 0 ∧ (dA ds (hs.length - 1)).nres = 1 ∧
        11 + (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).length + 32 < 2 ^ 18 ∧
        (∀ k, k < hs.length → OpV (dA ds k).body) ∧
        (∀ j, j < hs.length → (dA ds j).npw < 251 ∧ (dA ds j).nslots < 251 ∧ (dA ds j).nres < 251 ∧
          (dA ds j).npw ≤ (dA ds j).nslots) ∧
        (∀ j, j < hs.length → (pcOf 524288 hb c29 inp T).T j =
          (g34 bnew).length + (defsJ (pcOf 524288 hb c29 inp T) ds 0 j).length) ∧
        (∀ k, k < hs.length → ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body →
          OkV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧
          wd (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body = (dA ds k).nres)) := by
  obtain ⟨hs, T, o, hD, hne, hg, l2, l5, hol, hc18, hrest⟩ := gen_top c ds hXl h hdb hb c29 inp
  refine ⟨hs, T, o, hD, hne, ?_⟩
  obtain ⟨ho, hhd, hbd, hTp, hpk⟩ := hrest hol
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
  refine ⟨?_, np, nr, ?_, fun k hk => (hhd k hk).2.2, hbd, hTp, hpk⟩
  rotate_left
  · have := congrArg List.length ho; simp [g34_len] at this; omega
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
  s.m (s0.x 12).toNat = s0.x 1 ∧ s.m ((s0.x 12).toNat + 8) = s0.x 8 ∧ s.b = s0.b ∧ s.wk = s0.wk

theorem lbm_eq {m m' : Nat → UInt64} {a : Nat} (h : m' (a - a % 8) = m (a - a % 8)) : lbm m' a = lbm m a := by
  unfold lbm; rw [h]

theorem IGs_ok (s0 : St) (inp : Nat → UInt64) (E0 : Nat) (hE8 : E0 % 8 = 0)
    (hin : (s0.x 10).toNat + (s0.x 11).toNat ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 10).toNat) :
    IGOK ((s0.x 12).toNat + 16) E0 (IGs s0 inp) := by
  intro s s' ⟨i28, i29, iin, ira, is8, ib, iw⟩ e28 e29 eb ew hm
  refine ⟨by rw [e28, i28], by rw [e29, i29], fun i hi => ?_, by rw [hm _ (by omega), ira],
    by rw [hm _ (by omega), is8], by rw [eb, ib], by rw [ew, iw]⟩
  rw [lbm_eq (hm _ (by have := Nat.mod_lt ((s0.x 10).toNat + i) (show 8 > 0 by omega); omega)), iin i hi]

end Templates

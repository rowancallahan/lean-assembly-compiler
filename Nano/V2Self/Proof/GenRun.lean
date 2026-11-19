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
        ∀ (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64), IGOK hb E0 IG → E0 < 2 ^ 62 →
          (∀ s, IG s → s.b + 4 * C.length < 2 ^ 64) → InpOK IG c28 c29 inp →
          At C (g34 bnew).length (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length) →
          (∀ k, k < hs.length → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧
            ScV (scAt (pcOf 524288 hb c29 inp T) ds k) (dA ds k).body ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) →
          ∀ k, k < hs.length → DefX C ((pcOf 524288 hb c29 inp T).T k) (dA ds k).npw (dA ds k).nres IG hb E0
            (semAt (pcOf 524288 hb c29 inp T) ds k)) := by
  obtain ⟨hs, T, o, hD, hne, hg, hrest⟩ := gen_top c ds hXl h hdb h251 hb c29 inp
  refine ⟨hs, T, o, hD, hne, fun hol => ⟨?_, (hrest hol).2⟩⟩
  obtain ⟨ho, -⟩ := hrest hol
  have hTl : T.length = hs.length := by have := (DefsC.prefix hD).2; simpa [bnew] using this
  have hsl : 0 < hs.length := List.length_pos_iff.mpr hne
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

end Templates

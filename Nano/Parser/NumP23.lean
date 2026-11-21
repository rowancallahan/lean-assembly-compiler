/- Nano/Parser/NumP23: the machine's marking rounds compute `marked`. -/
import Nano.Parser.NumP22
namespace NumP
open C ParSpec OwnP

theorem mk54_ok (k : UInt64) (hk : k ≠ 0) : ∀ (vs : List Nat) (f : Buf), (∀ v ∈ vs, v < f.length) → f.length < 2 ^ 62 →
    (mk54 k f (vs.map u)).length = f.length ∧ ∀ i, i < f.length →
      (mk54 k f (vs.map u)).getD i 0 = if i ∈ vs ∧ f.getD i 0 = 0 then k else f.getD i 0
  | [], f, _, _ => ⟨rfl, fun i _ => by simp [mk54]⟩
  | v :: vs, f, hv, hl => by
    have hv0 := hv v (by simp)
    have e1 : mk54 k f ((v :: vs).map u) = mk54 k (if bget f (u v) == 0 then bset f (u v) k else f) (vs.map u) := rfl
    rw [e1, bget_u _ (by omega), bset_u _ (by omega)]
    generalize hf' : (if (f.getD v 0 == 0) = true then f.set v k else f) = f'
    have hl' : f'.length = f.length := by rw [← hf']; split <;> simp
    have hg' : ∀ i, f'.getD i 0 = if i = v ∧ f.getD v 0 = 0 then k else f.getD i 0 := by
      intro i; rw [← hf']
      by_cases h0 : f.getD v 0 = 0
      · rw [if_pos (by rw [h0]; rfl), getD_set]
        by_cases hi : i = v
        · subst hi; rw [if_pos ⟨rfl, hv0⟩, if_pos ⟨rfl, h0⟩]
        · rw [if_neg (fun h => hi h.1.symm), if_neg (fun h => hi h.1)]
      · rw [if_neg (by simpa using h0), if_neg (fun h => h0 h.2)]
    obtain ⟨ih1, ih2⟩ := mk54_ok k hk vs f' (by intro w hw; rw [hl']; exact hv w (by simp [hw])) (by omega)
    refine ⟨by rw [ih1, hl'], fun i hi => ?_⟩
    rw [ih2 i (by omega), hg' i]
    by_cases hiv : i = v
    · subst hiv
      by_cases h0 : f.getD i 0 = 0
      · rw [if_pos (show i = i ∧ f.getD i 0 = 0 from ⟨rfl, h0⟩), if_neg (show ¬ (i ∈ vs ∧ k = 0) from fun h => hk h.2),
          if_pos (show i ∈ i :: vs ∧ f.getD i 0 = 0 from ⟨List.mem_cons_self, h0⟩)]
      · rw [if_neg (show ¬ (i = i ∧ f.getD i 0 = 0) from fun h => h0 h.2),
          if_neg (show ¬ (i ∈ vs ∧ f.getD i 0 = 0) from fun h => h0 h.2),
          if_neg (show ¬ (i ∈ i :: vs ∧ f.getD i 0 = 0) from fun h => h0 h.2)]
    · rw [if_neg (show ¬ (i = v ∧ f.getD v 0 = 0) from fun h => hiv h.1)]
      have hmem : i ∈ v :: vs ↔ i ∈ vs := by simp [hiv]
      by_cases hc : i ∈ vs ∧ f.getD i 0 = 0
      · rw [if_pos hc, if_pos (show i ∈ v :: vs ∧ f.getD i 0 = 0 from ⟨hmem.2 hc.1, hc.2⟩)]
      · rw [if_neg hc, if_neg (show ¬ (i ∈ v :: vs ∧ f.getD i 0 = 0) from fun h => hc ⟨hmem.1 h.1, h.2⟩)]

section
variable (q' : Nat) (X : List NumSpec.G) (N : Nat)

/-- after K rounds: each slot's word is the round that marked it -/
def INV (K : Nat) (f : Buf) : Prop :=
  f.length = N ∧ ∀ v, v < N → ∃ j, j ≤ K ∧ f.getD v 0 = u j ∧ (j ≠ 0 ↔ v ∈ NumSpec.marked q' X K [])

/-- during round K + 1: S is the set of slots its selected groups so far have -/
def RI (K : Nat) (f : Buf) (S : Nat → Prop) : Prop :=
  f.length = N ∧ ∀ v, v < N → ∃ j, j ≤ K + 1 ∧ f.getD v 0 = u j ∧
    ((j ≠ 0 ∧ j < K + 1) ↔ v ∈ NumSpec.marked q' X K []) ∧ (j = K + 1 ↔ (v ∉ NumSpec.marked q' X K [] ∧ S v))

end

theorem bget_slot {f : Buf} {v : Nat} (h : v < 2 ^ 64) : bget f (u v) = f.getD v 0 := bget_u _ h

theorem rnd_ok (q' : Nat) (hq : q' < 3) (X : List NumSpec.G) (N : Nat) (hN : N < 2 ^ 24) (K : Nat) (hK : K + 1 < 2 ^ 24) :
    ∀ (B : List NumSpec.G) (f : Buf) (S : Nat → Prop), (∀ G ∈ B, G.d < 3 ∧ ∀ v ∈ G.vs, v < N) → RI q' X N K f S →
    RI q' X N K (rnd (u q') (u (K + 1)) f B) (fun v => S v ∨ ∃ G ∈ B,
      (G.d = q' ∨ ∃ w ∈ G.vs, w ∈ NumSpec.marked q' X K []) ∧ v ∈ G.vs)
  | [], f, S, _, hR => by simpa [rnd] using hR
  | G :: B, f, S, hB, hR => by
    obtain ⟨hGd, hGv⟩ := hB G (by simp)
    obtain ⟨hl, hv⟩ := hR
    -- the selection test
    have hsel : sel (u q') (u (K + 1)) f G = (decide (G.d = q' ∨ ∃ w ∈ G.vs, w ∈ NumSpec.marked q' X K [])) := by
      unfold sel
      rw [ueq (by omega) (by omega)]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_map, List.any_eq_true, Function.comp, Bool.and_eq_true,
        bne_iff_ne, ne_eq, decide_eq_true_eq]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        refine ⟨w, hw, ?_⟩
        obtain ⟨j, hj, hfj, hj1, -⟩ := hv w (hGv w hw)
        rw [bget_slot (by have := hGv w hw; omega), hfj] at h1 h2
        refine hj1.1 ⟨fun h => h1 (by rw [h]; rfl), ?_⟩
        rwa [ult (by omega) (by omega)] at h2
      · rintro ⟨w, hw, hm⟩
        refine ⟨w, hw, ?_⟩
        obtain ⟨j, hj, hfj, hj1, -⟩ := hv w (hGv w hw)
        obtain ⟨hj0, hjk⟩ := hj1.2 hm
        rw [bget_slot (by have := hGv w hw; omega), hfj, ult (by omega) (by omega)]
        refine ⟨fun h => hj0 ?_, hjk⟩
        have := congrArg UInt64.toNat h
        rw [u_toNat (by omega)] at this; simpa using this
    -- one group
    have hstep : RI q' X N K (if sel (u q') (u (K + 1)) f G then mk54 (u (K + 1)) f (G.vs.map u) else f)
        (fun v => S v ∨ ((G.d = q' ∨ ∃ w ∈ G.vs, w ∈ NumSpec.marked q' X K []) ∧ v ∈ G.vs)) := by
      rw [hsel]
      by_cases hs : G.d = q' ∨ ∃ w ∈ G.vs, w ∈ NumSpec.marked q' X K []
      · rw [if_pos (by simpa using hs)]
        obtain ⟨m1, m2⟩ := mk54_ok (u (K + 1)) (by
          intro h; have := congrArg UInt64.toNat h; rw [u_toNat (by omega)] at this; simp at this)
          G.vs f (by intro v hv; rw [hl]; exact hGv v hv) (by omega)
        refine ⟨by rw [m1, hl], fun v hvN => ?_⟩
        obtain ⟨j, hj, hfj, hj1, hj2⟩ := hv v hvN
        rw [m2 v (by omega), hfj]
        by_cases hm : v ∈ G.vs ∧ u j = 0
        · have hj0 : j = 0 := by
            have := congrArg UInt64.toNat hm.2; rw [u_toNat (by omega)] at this; simpa using this
          subst hj0
          rw [if_pos hm]
          refine ⟨K + 1, Nat.le_refl _, rfl, ?_, ?_⟩
          · constructor
            · rintro ⟨-, h⟩; omega
            · intro h; have := hj1.2 h; omega
          · constructor
            · intro _; refine ⟨fun h => ?_, Or.inr ⟨hs, hm.1⟩⟩
              have := hj1.2 h; omega
            · intro _; rfl
        · rw [if_neg hm]
          refine ⟨j, hj, rfl, hj1, ?_⟩
          rw [hj2]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩
          · rintro ⟨h1, h2 | ⟨-, h3⟩⟩
            · exact ⟨h1, h2⟩
            · have hj0 : j ≠ 0 := fun h => hm ⟨h3, by rw [h]; rfl⟩
              have hjK : j = K + 1 := by
                rcases Nat.lt_or_ge j (K + 1) with hlt | hge
                · exact absurd (hj1.1 ⟨hj0, hlt⟩) h1
                · omega
              exact hj2.1 hjK
      · rw [if_neg (by simpa using hs)]
        refine ⟨hl, fun v hvN => ?_⟩
        obtain ⟨j, hj, hfj, hj1, hj2⟩ := hv v hvN
        refine ⟨j, hj, hfj, hj1, ?_⟩
        rw [hj2]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩
        · rintro ⟨h1, h2 | ⟨h3, -⟩⟩
          · exact ⟨h1, h2⟩
          · exact absurd h3 hs
    have ih := rnd_ok q' hq X N hN K hK B _ _ (fun G hG => hB G (by simp [hG])) hstep
    simp only [rnd]
    refine ⟨ih.1, fun v hvN => ?_⟩
    obtain ⟨j, hj, hfj, hj1, hj2⟩ := ih.2 v hvN
    refine ⟨j, hj, hfj, hj1, ?_⟩
    rw [hj2]
    constructor
    · rintro ⟨h1, (h2 | h2) | ⟨G', hG', h3⟩⟩
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr ⟨G, by simp, h2⟩⟩
      · exact ⟨h1, Or.inr ⟨G', by simp [hG'], h3⟩⟩
    · rintro ⟨h1, h2 | ⟨G', hG', h3⟩⟩
      · exact ⟨h1, Or.inl (Or.inl h2)⟩
      · simp at hG'
        rcases hG' with rfl | hG'
        · exact ⟨h1, Or.inl (Or.inr h3)⟩
        · exact ⟨h1, Or.inr ⟨G', hG', h3⟩⟩

end NumP

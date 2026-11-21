/- Nano/Parser/NumP21: the class check's group loops (`u51`, `u55`, `u56`, `u58`) over the groups buffer `encG X`. -/
import Nano.Parser.NumP20
namespace NumP
open C ParSpec OwnP

/-- the header words of a group record -/
def ghd (G : NumSpec.G) : List UInt64 := [u G.vs.length, u G.d, w2 G.ar]

theorem encGr_eq (G : NumSpec.G) : encGr G = ghd G ++ G.vs.map u := rfl

/-- reading the record of G in `encG (A ++ G :: B)` -/
theorem rec_rd {A B : List NumSpec.G} {G : NumSpec.G} {g : Buf} (hg : g = encG (A ++ G :: B)) (hl : g.length < 2 ^ 62) :
    bget g (u (encG A).length) = u G.vs.length ∧ bget g (u (encG A).length + 1) = u G.d ∧
    bget g (u (encG A).length + 2) = w2 G.ar ∧ (encG A ++ ghd G) ++ G.vs.map u <+: g ∧
    u (encG A).length + 3 = u (encG A ++ ghd G).length ∧
    u (encG A ++ ghd G).length + u G.vs.length = u ((encG A ++ ghd G).length + (G.vs.map u).length) ∧
    (encG A ++ ghd G).length + (G.vs.map u).length = (encG (A ++ [G])).length ∧
    (encG A).length < g.length := by
  have hg' : g = (encG A ++ ghd G) ++ G.vs.map u ++ encG B := by
    rw [hg]; simp [encG_app, encG, encGr, ghd]
  have hpre : (encG A ++ ghd G) ++ G.vs.map u <+: g := by rw [hg']; exact List.prefix_append _ _
  have hlen := hpre.length_le; simp [ghd] at hlen
  have r0 : bget g (u (encG A).length) = u G.vs.length := by
    rw [bget_pre hpre (by simp [ghd]) (by omega)]; simp [ghd, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have r1 : bget g (u (encG A).length + 1) = u G.d := by
    rw [u1, uadd, bget_pre hpre (by simp [ghd]) (by omega)]
    simp [ghd, List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left]
  have r2 : bget g (u (encG A).length + 2) = w2 G.ar := by
    rw [u2, uadd, bget_pre hpre (by simp [ghd]) (by omega)]
    simp [ghd, List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left]
  refine ⟨r0, r1, r2, hpre, by simp [ghd, u3, uadd], by simp [uadd], ?_, by omega⟩
  simp [encG_app, encG, encGr, ghd]; omega

theorem gend {g : Buf} {X : List NumSpec.G} (hg : g = encG X) (hl : g.length < 2 ^ 62) :
    ¬ (u (encG X).length < bsize g) := by
  rw [bsize_u, hg, ult (by subst hg; omega) (by subst hg; omega)]; simp

theorem glt {g : Buf} {A : List NumSpec.G} (hl : g.length < 2 ^ 62) (h : (encG A).length < g.length) :
    u (encG A).length < bsize g := by
  rw [bsize_u, ult (by omega) (by omega)]; exact h

/-- zeta-reduce only, at a location -/
macro "zeta_at" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| dsimp (config := {iota := false, proj := false, etaStruct := .none, beta := false, eta := false}) only $(loc)?)

/-- `u51`: every slot word is below n -/
theorem u51_ok {g : Buf} (n : UInt64) (hl : g.length < 2 ^ 62) : ∀ (m : Nat) (A B : List NumSpec.G), g = encG (A ++ B) →
    u51 m g (u (encG A).length) n = 1 → ∀ G ∈ B, ∀ v ∈ G.vs, u v < n
  | 0, _, _, _, h => by simp [u51] at h
  | m + 1, A, [], _, _ => by simp
  | m + 1, A, G :: B, hg, h => by
    obtain ⟨r0, -, -, hpre, e3, e4, e5, hlt⟩ := rec_rd hg hl
    simp only [u51, if_pos (glt hl hlt), r0] at h
    rw [e3, e4] at h
    by_cases h52 : u52 16777216 g (u (encG A ++ ghd G).length) (u ((encG A ++ ghd G).length + (G.vs.map u).length)) n = 1
    · rw [if_pos (by rw [h52]; rfl), e5] at h
      have ih := u51_ok n hl m (A ++ [G]) B (by simpa using hg) h
      have hs := u52_ok 16777216 _ _ g n hpre hl h52
      intro G' hG' v hv
      simp at hG'; rcases hG' with rfl | hG'
      · exact hs (u v) (by simp; exact ⟨v, hv, rfl⟩)
      · exact ih G' hG' v hv
    · rw [if_neg (by simpa using h52)] at h; exact absurd h (by decide)

/-- a round of `marked q` selects a group -/
def sel (q k : UInt64) (f : Buf) (G : NumSpec.G) : Bool :=
  (u G.d == q) || (G.vs.map u).any fun w => bget f w != 0 && decide (bget f w < k)

/-- a round of `marked q` (k: the round's stamp), group by group -/
def rnd (q k : UInt64) : Buf → List NumSpec.G → Buf
  | f, [] => f
  | f, G :: B => rnd q k (if sel q k f G then mk54 k f (G.vs.map u) else f) B

theorem u55_ok {g : Buf} (q k : UInt64) (hl : g.length < 2 ^ 62) : ∀ (m : Nat) (A B : List NumSpec.G) (f : Buf),
    g = encG (A ++ B) → (u55 m f g (u (encG A).length) q k).2 = 1 → (u55 m f g (u (encG A).length) q k).1 = rnd q k f B
  | 0, _, _, _, _, h => by simp [u55] at h
  | m + 1, A, [], f, hg, _ => by
    rw [u55, if_neg (gend (by simpa using hg) hl)]; simp [rnd]
  | m + 1, A, G :: B, f, hg, h => by
    obtain ⟨r0, r1, -, hpre, e3, e4, e5, hlt⟩ := rec_rd hg hl
    rw [u55] at h ⊢
    zeta_at at h ⊢
    rw [if_pos (glt hl hlt), r0, r1, e3, e4] at h ⊢
    have ih := u55_ok q k hl m (A ++ [G]) B
    rw [← e5] at ih
    have hg2 : g = encG ((A ++ [G]) ++ B) := by simpa using hg
    rcases u53_ok f k 16777216 _ _ g hpre hl with h53 | h53
    · by_cases hq : (u G.d == q) = true
      · rw [if_pos hq, if_neg (kne (show ((1 : UInt64) == 2) = false from rfl)),
          if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at h ⊢
        have h54 := u54_ok k 16777216 _ _ g f hpre hl
        generalize u54 16777216 f g _ _ k = U at h h54 ⊢
        obtain ⟨f1, ok⟩ := U
        iota_only at h ⊢
        by_cases hok : ok = 1
        · subst hok
          rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at h ⊢
          have h54' := h54 rfl; simp only at h54'
          rw [ih f1 hg2 h, h54']
          simp [rnd, sel, hq]
        · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
      · rw [if_neg hq, h53, if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at h
        exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    · rw [h53] at h ⊢
      have hsel : sel q k f G = ((u G.d == q) || (G.vs.map u).any fun w => bget f w != 0 && decide (bget f w < k)) := rfl
      cases hs : sel q k f G
      · have hq : (u G.d == q) = false := by simp [sel] at hs; simp [hs.1]
        have ha : ((G.vs.map u).any fun w => bget f w != 0 && decide (bget f w < k)) = false := by
          rw [hsel, hq, Bool.false_or] at hs; exact hs
        rw [if_neg (kne hq), ha, if_neg (kne (show (w2 false == 2) = false from rfl)),
          if_neg (kne (show (w2 false == 1) = false from rfl))] at h ⊢
        rw [ih f hg2 h]; simp [rnd, hs]
      · have hh : (if (u G.d == q) = true then (1 : UInt64)
            else w2 ((G.vs.map u).any fun w => bget f w != 0 && decide (bget f w < k))) = 1 := by
          rw [hsel] at hs
          by_cases hq : (u G.d == q) = true
          · rw [if_pos hq]
          · rw [if_neg hq]; simp [hq] at hs; simp [hs, w2]
        rw [hh, if_neg (kne (show ((1 : UInt64) == 2) = false from rfl)),
          if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at h ⊢
        have h54 := u54_ok k 16777216 _ _ g f hpre hl
        generalize u54 16777216 f g _ _ k = U at h h54 ⊢
        obtain ⟨f1, ok⟩ := U
        iota_only at h ⊢
        by_cases hok : ok = 1
        · subst hok
          rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at h ⊢
          have h54' := h54 rfl; simp only at h54'
          rw [ih f1 hg2 h, h54']
          simp [rnd, hs]
        · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

end NumP

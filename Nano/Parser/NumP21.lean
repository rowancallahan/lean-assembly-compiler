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
    (u (encG X).length < bsize g) = False := by
  rw [bsize_u, hg, ult (by subst hg; omega) (by subst hg; omega)]; simp

theorem glt {g : Buf} {A : List NumSpec.G} (hl : g.length < 2 ^ 62) (h : (encG A).length < g.length) :
    (u (encG A).length < bsize g) = True := by
  rw [bsize_u, ult (by omega) (by omega)]; simp [h]

/-- `u51`: every slot word is below n -/
theorem u51_ok {g : Buf} (n : UInt64) (hl : g.length < 2 ^ 62) : ∀ (m : Nat) (A B : List NumSpec.G), g = encG (A ++ B) →
    u51 m g (u (encG A).length) n = 1 → ∀ G ∈ B, ∀ v ∈ G.vs, u v < n
  | 0, _, _, _, h => by simp [u51] at h
  | m + 1, A, [], _, _ => by simp
  | m + 1, A, G :: B, hg, h => by
    obtain ⟨r0, -, -, hpre, e3, e4, e5, hlt⟩ := rec_rd hg hl
    simp only [u51, glt hl hlt, if_true, r0] at h
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

end NumP

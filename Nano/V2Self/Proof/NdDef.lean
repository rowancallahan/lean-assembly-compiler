/- Machine bridge (Opus box E): one def.  `defRun`: the def template (Gen's prologue `proA`, the body template, the
epilogue `epi`) at word f satisfies the def contract `DefX` for `defS p nl (sv S body)`.  `defWords`: Gen's DefC
output is exactly that template `.map encG` (exits patched to the epilogue start). -/
import Nano.V2Self.Proof.NdCGm
namespace Templates
open CallProbe C GenRef ParSpec

/-- the def template at word f: prologue (r = nl − p local words), body at f + 12, epilogue -/
def defT (S : SC) (e : Nd) (f q : Nat) : List J := proA 1 f (S.nl - S.p) ++ tm S e (f + 12) ++ epi S.p q

theorem defRun {S : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} (X : RunCx S C IG E0 c28)
    {e : Nd} {f q : Nat} (ok : OkV S e) (hw : wd S e = q) (hR : ∀ k, rd e k → k < S.p) (hpn : S.p ≤ S.nl)
    (hC : At C f (defT S e f q)) : DefX C f S.p q IG S.hb E0 (defS S.p S.nl (sv S e)) := by
  obtain ⟨hP, hB, hE⟩ := At.mid hC
  have lp : (proA 1 f (S.nl - S.p)).length = 12 := by simp [proA, pushA, push]
  rw [lp] at hB hE; rw [tm_len] at hE
  exact defX X.ig hP ((runV X e (f + 12) ok hB).wid hw) hE hpn hR

/-- patching the exit placeholders: every listed word becomes the jump to H, nothing else changes -/
theorem patchR_get (H : UInt64) : ∀ (L : List UInt64) (o : Buf) (j : Nat), (∀ e ∈ L, e.toNat < o.length) →
    (patchR H o L)[j]? = if (∃ e ∈ L, e.toNat = j) then some (g13 0 j.toUInt64 H) else o[j]?
  | [], o, j, _ => by simp [patchR]
  | e :: L, o, j, hL => by
    simp only [patchR]
    rw [patchR_get H L _ j (fun e' he' => by rw [BufL.length_bset]; exact hL e' (List.mem_cons_of_mem _ he'))]
    simp only [bset, List.mem_cons, exists_eq_or_imp]
    by_cases h1 : ∃ e' ∈ L, e'.toNat = j
    · simp [h1]
    · simp only [h1, or_false, if_false]
      rw [List.getElem?_set]
      by_cases h2 : e.toNat = j
      · have he : e = j.toUInt64 := by subst h2; simp [Nat.toUInt64]
        have hl : j < o.length := by rw [← h2]; exact hL e (by simp)
        have hj : j < 2 ^ 64 := by rw [← h2]; exact e.toNat_lt
        simp [he, hl, Nat.mod_eq_of_lt hj, hj]
      · simp [h2]

theorem toU_toNat_lt (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by simp [Nat.toUInt64]; omega

/-- patching a matched block's exits to its end gives the template's words -/
theorem Mt.patch {c : List UInt64} {l : List J} {h : Nat} {E : List Nat} {o0 : Buf}
    (m : Mt c l h E (h + c.length)) (ho : o0.length = h) (hb : h + c.length < 2 ^ 32) :
    patchR (bsize (o0 ++ c)) (o0 ++ c) (E.map Nat.toUInt64).reverse = o0 ++ l.map encG := by
  obtain ⟨hl, hE, hf⟩ := m
  have hb' : bsize (o0 ++ c) = (h + c.length).toUInt64 := by simp [bsize, ho]
  apply List.ext_getElem?
  intro j
  rw [patchR_get _ _ _ _ (fun e he => by
    simp only [List.mem_reverse, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    have := hE x hx; rw [toU_toNat_lt x (by omega)]; simp; omega)]
  have hiff : (∃ e ∈ (E.map Nat.toUInt64).reverse, e.toNat = j) ↔ j ∈ E := by
    simp only [List.mem_reverse, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, e⟩
      have := hE x hx; rw [toU_toNat_lt x (by omega)] at e; subst e; exact hx
    · intro hj; have := hE j hj; exact ⟨_, ⟨j, hj, rfl⟩, toU_toNat_lt j (by omega)⟩
  by_cases hj : j ∈ E
  · rw [if_pos (hiff.mpr hj)]
    have := hE j hj
    obtain ⟨q1, q2⟩ := (hf (j - h) (by omega)).1 (by rw [show h + (j - h) = j by omega]; exact hj)
    rw [List.getElem?_append_right (by omega), List.getElem?_map, ho, q2, hb',
      show h + (j - h) = j by omega]
    rw [show g13 0 j.toUInt64 (h + c.length).toUInt64 = encG (J.jal 0 (((h + c.length : Nat) : Int) - (j : Int)))
      from g13_enc 0 j _ (by omega) hb]
    rfl
  · rw [if_neg (fun q => hj (hiff.mp q))]
    by_cases hjh : j < h
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), ho]
      by_cases hjl : j - h < l.length
      · rw [(hf (j - h) hjl).2 (by rw [show h + (j - h) = j by omega]; exact hj), List.getElem?_map]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end Templates

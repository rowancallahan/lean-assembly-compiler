/- Machine bridge (Opus box E): one def.  `defRun`: the def template (Gen's prologue `proA`, the body template, the
epilogue `epi`) at word f satisfies the def contract `DefX` for `defS p nl (sv S body)`.  `defWords`: Gen's DefC
output is exactly that template `.map encG` (exits patched to the epilogue start). -/
import Nano.V2Self.Proof.Machine.NdCGm
namespace Templates
open CallProbe C GenRef ParSpec

/-- the def template at word f: prologue (r = nl − p local words), body at f + 12, epilogue -/
def defT (S : SC) (e : Nd) (f q : Nat) : List J := proA 1 f (S.nl - S.p) ++ tm S e (f + 12) ++ epi S.p q

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

theorem toNat_toU (x : UInt64) : x.toNat.toUInt64 = x := by simp [Nat.toUInt64]

/-- **one def's words**: DefC's output is the def template `.map encG` (body = the AST node at i + 6) -/
theorem defWords {X : Buf} {u : UInt64} {T : Buf} {i : Nat} {o o' : Buf} {i' : Nat} (hD : DefC X u T i o o' i')
    {S : SC} {e : Nd} (hS : SK S (dK X u (bpush T (bsize o)) i)) (hnl : S.nl = (tg X (i + 3)).toNat)
    (nb : NB S.p e) (sa : SerAt X (i + 6) e.ser) (hlen : o'.length < 2 ^ 24) :
    i' = i + 6 + e.ser.length + 1 ∧ o' = o ++ (defT S e o.length (tg X (i + 5)).toNat).map encG ∧ OpV e := by
  obtain ⟨t20, hns, hpn, hq, _, c, i1, E, hcg, t21, rfl, rfl, _⟩ := hD
  have hp : S.p = (tg X (i + 2)).toNat := hS.p
  have ns251 : (tg X (i + 3)).toNat < 251 := by rw [UInt64.lt_iff_toNat_lt] at hns; exact hns
  have q251 : (tg X (i + 5)).toNat < 251 := by rw [UInt64.lt_iff_toNat_lt] at hq; exact hq
  have pns : (tg X (i + 2)).toNat ≤ (tg X (i + 3)).toNat := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hpn; simp at hpn; omega
  -- the prologue
  have ensp : tg X (i + 3) - tg X (i + 2) = (S.nl - S.p).toUInt64 := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hnl, hp, toU_toNat_lt _ (by omega)]
  -- the epilogue
  have eq' : ∀ w : Buf, g29 512 (tg X (i + 2)) (tg X (i + 5)) 0 (bpush (bpush w (g11 14 8 8)) (g11 15 8 0)) =
      w ++ (epi S.p (tg X (i + 5)).toNat).map encG := by
    intro w
    have := epi_exact w (tg X (i + 2)).toNat (tg X (i + 5)).toNat (by omega) q251
    rw [toNat_toU, toNat_toU] at this
    rw [hp]; exact this
  rw [eq'] at hlen ⊢
  simp only [List.length_append, patchR_len, List.length_map] at hlen
  have hpo : o.length ≤ (proW (tg X (i + 2)) (tg X (i + 3)) o).length := by
    rw [pi_pro _ _ o]; simp
  have epro : proW (tg X (i + 2)) (tg X (i + 3)) o = o ++ (proA 1 o.length (S.nl - S.p)).map encG := by
    unfold proW; rw [ensp]
    exact pro_exact o _ (by omega) (by omega)
  rw [epro] at hcg hlen ⊢
  have lp : (proA 1 o.length (S.nl - S.p)).length = 12 := by simp [proA, pushA, push]
  simp only [List.length_append, List.length_map, lp] at hcg hlen
  obtain ⟨e1, m, _, hop⟩ := cgV hS e 1 (i + 6) (o.length + 12) c i1 E nb sa hcg (Nat.le_refl 1) (by omega)
  have hm := m.patch (o0 := o ++ (proA 1 o.length (S.nl - S.p)).map encG) (by simp [lp]) (by omega)
  refine ⟨by rw [e1], ?_, hop⟩
  rw [hm]
  simp [defT, List.append_assoc]

end Templates

/- Nano/V2Self/Proof/MainBridge12: the Sem ⇐ sv bridge — tail mode (loop arms: E's `st` ↔ `ev`'s `.inl` exit / `.inr`
CONTINUE). -/
import Nano.V2Self.Proof.MainBridge11

namespace NanoMain
open Templates

/-- a value-mode expression's tail template is its value template, exiting -/
theorem st_none (K : SC) {D : List Sig} : ∀ {Γ S e ks}, TyN D Γ S e ks → S = none →
    ∀ env sp H, st K e env sp H = exitS (sv K e) env sp H
  | _, _, _, _, .const, _, _, _, _ => by simp only [st]
  | _, _, _, _, .loc _, _, _, _, _ => by simp only [st]
  | _, _, _, _, .bin _ _ _ _, _, _, _, _ => by simp only [st]
  | _, _, _, _, .pair _, _, _, _, _ => by simp only [st]
  | _, _, _, _, .call _ _, _, _, _, _ => by simp only [st]
  | _, _, _, _, .prim _ _ _, _, _, _, _ => by simp only [st]
  | _, _, _, _, .cont _, hS, _, _, _ => by cases hS
  | _, _, _, _, .ite (c := c) (a := a) (b := b) (t := t) (e := e) _ _ _ tt te, hS, env, sp, H => by
    simp only [st, sv, ifTS, ifS, exitS]
    cases h : pairS 1 (sv K a) (sv K b) env sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      split
      · split
        · rw [st_none K tt hS env sp]; simp_all [exitS]
        · rw [st_none K te hS env sp]; simp_all [exitS]
      · split <;> simp_all
  | _, _, _, _, .letE (s := s) (w := w) (v := v) (b := b) _ _ _ _ tb, hS, env, sp, H => by
    simp only [st, sv, letTS, letS, exitS]
    cases h : sv K v env sp H with
    | none => rfl
    | some r => simp only [Option.bind_some]; rw [st_none K tb hS _ sp]; rfl

/-- tail-mode entry counts: a CONTINUE has none, an exit has one per result word -/
theorem chk_len_tail {oc : OwnSpec.Cx} {D : List Sig} (hR : RsOK oc D) : ∀ {Γ S e ks}, TyN D Γ S e ks →
    ∀ F F' es, OwnSpec.chk oc e F = some (F', es) → es = [] ∨ es.length = ks.length
  | Γ, _, _, _, .const, F, F', es, h => .inr (chk_len hR (Γ := Γ) (S := none) .const rfl F F' es h)
  | _, _, _, _, .loc hk, F, F', es, h => .inr (chk_len hR (S := none) (.loc hk) rfl F F' es h)
  | _, _, _, _, .bin o1 o2 ta tb, F, F', es, h => .inr (chk_len hR (S := none) (.bin o1 o2 ta tb) rfl F F' es h)
  | _, _, _, _, .pair tl, F, F', es, h => .inr (chk_len hR (S := none) (.pair tl) rfl F F' es h)
  | _, _, _, _, .call tl hd, F, F', es, h => .inr (chk_len hR (S := none) (.call tl hd) rfl F F' es h)
  | _, _, _, _, .prim tl hp hn, F, F', es, h => .inr (chk_len hR (S := none) (.prim tl hp hn) rfl F F' es h)
  | _, _, _, _, .cont _, F, F', es, h => by
    unfold OwnSpec.chk at h
    split at h
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y, -, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; exact .inl he.2.symm
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨y, -, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; exact .inl he.2.symm
      · cases h
  | _, _, _, _, .ite _ _ _ tt te, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a0, -, b0, -, y, -, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := h
    simp only [Prod.mk.injEq] at hk; obtain ⟨-, rfl⟩ := hk
    have lt := chk_len_tail hR tt _ _ _ h1
    have le := chk_len_tail hR te _ _ _ h3
    have lt1 := tr_len _ _ _ _ h2
    have le1 := tr_len _ _ _ _ h4
    unfold OwnSpec.join at hj
    split at hj
    · simp only [Option.some.injEq] at hj; subst hj
      rcases le with h | h
      · left; rw [← List.length_eq_zero_iff, le1, h]; rfl
      · right; omega
    · split at hj
      · simp only [Option.some.injEq] at hj; subst hj
        rcases lt with h | h
        · left; rw [← List.length_eq_zero_iff, lt1, h]; rfl
        · right; omega
      · split at hj
        · simp only [Option.some.injEq] at hj; subst hj
          rename_i h0 h0' hl
          right; simp only [List.length_zipWith]
          rcases lt with h | h
          · exact absurd (List.length_eq_zero_iff.1 (by rw [lt1, h]; rfl)) h0
          · omega
        · cases hj
  | _, _, _, _, .letE _ _ _ _ tb, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at h
    obtain ⟨v0, -, v1, -, h⟩ := h
    split at h
    · obtain ⟨b0, hb0, hb1⟩ := Option.bind_eq_some_iff.mp h
      rw [← List.length_eq_zero_iff, tr_len _ _ _ _ hb1, List.length_eq_zero_iff]
      exact chk_len_tail hR tb _ _ _ hb0
    · cases h

end NanoMain

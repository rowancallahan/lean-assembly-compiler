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

/-! ## an argument list closed by `fin` at destinations `P` -/

theorem fin_args {σ σ1 : AH} {Kk : List Nat} {F x1 yF : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {P es : List Nat} {v : List W} {vs : List UInt64} (hR1 : ResI σ1 Kk x1 Γ env ew es v vs)
    (hE1 : EnvI σ1 Kk x1 Γ env ew) (hr1 : R2 Kk x1) (hS1 : Src σ Γ F x1 env ew es v vs) (hM1 : Mono F x1)
    (hfc : OwnSpec.finC (some P) x1 0 es = some yF) (hfb : OwnSpec.finB (some P) yF 0 es = true)
    (hlP : es.length = P.length)
    (hok : ∀ (i e : Nat), es[i]? = some e → ∃ G, OwnSpec.ok1 G e (OwnSpec.dest (some P) i) = true) :
    ArgsR σ1 P v vs ∧
    (∀ (j : Nat) (l : List UInt64) (u : UInt64), P[j]? = some 1 → v[j]? = some (W.b l) → vs[j]? = some u →
      (∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead yF s = false → env[s]? = some (.b ls) → ew s ≠ u) ∧
      ((σ u.toNat).isSome → ∃ j' l', Kn Γ j' ∧ Cons F yF j' ∧ env[j']? = some (.b l') ∧ ew j' = u)) ∧
    (∀ (j : Nat) (l : List UInt64) (u : UInt64), P[j]? = some 3 → v[j]? = some (W.b l) → vs[j]? = some u →
      ∃ k l', Kn Γ k ∧ Kk.getD k 0 = 2 ∧ env[k]? = some (.b l') ∧ ew k = u) := by
  have mf := finC_mono _ _ _ _ hfc
  have ln := hR1.len
  have hlive : ∀ (j e : Nat), es[j]? = some e → OwnSpec.own e = true → OwnSpec.dead x1 (e / 4 - 1) = false := by
    intro j e he ho
    obtain ⟨G, hG⟩ := hok j e he
    simp only [OwnSpec.own, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho
    unfold OwnSpec.ok1 at hG; rw [if_neg (by omega), if_neg (by omega), if_pos ho.2] at hG
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hG
    rcases hG.1 with hd | hd
    · exact (finC_own1 _ _ _ _ hfc j e he (by simp [OwnSpec.own, ho.2]; omega) (by simpa using hd)).1
    · exact live_of_mono mf (finB_own2 0 _ hfb j e he (by simp [OwnSpec.own, ho.2]; omega) (by simpa using hd))
  refine ⟨⟨by have := ln.1; have := ln.2; omega, by have := ln.1; have := ln.2; omega, fun j x u hv hu => ?_,
    fun j x hPj hv => ?_, args_distinct hR1 hE1 hr1 hfc hfb hok⟩, fun j l u hPj hv hu => ?_, fun j l u hPj hv hu => ?_⟩
  · obtain ⟨e, he⟩ := get_of_len ln.1 hv
    obtain ⟨G, hG⟩ := hok j e he
    exact arg_vr hR1 hE1 hr1 he hv hu hG (hlive j e he)
  · obtain ⟨e, he⟩ := get_of_len ln.1 hv
    obtain ⟨u, hu⟩ := get_of_len ln.2.symm hv
    obtain ⟨G, hG⟩ := hok j e he
    rw [dest_some hPj] at hG
    exact ⟨u, arg_word hR1 hE1 he hv hu hG⟩
  · obtain ⟨e, he⟩ := get_of_len ln.1 hv
    obtain ⟨G, hG⟩ := hok j e he
    rw [dest_some hPj] at hG
    obtain ⟨-, a, b⟩ := own_idx hR1 hE1 hS1 hM1 hfc (dest_some hPj) he hv hu hG
    exact ⟨a, b⟩
  · obtain ⟨e, he⟩ := get_of_len ln.1 hv
    obtain ⟨G, hG⟩ := hok j e he
    rw [dest_some hPj] at hG
    unfold OwnSpec.ok1 at hG
    split at hG
    · simp at hG; obtain ⟨y, hy⟩ := (resI_idx j hR1 he hv hu).2.1 (by omega); cases hy
    · rename_i h4
      obtain ⟨ua, ex, ek, kn⟩ := resI_tag j hR1 he hv hu (by omega)
      split at hG
      · obtain ⟨y, hy, -, wd⟩ := hE1.val _ kn (.inl (by omega))
        rw [ex] at hy; cases hy; obtain ⟨z, hz⟩ := wd (by omega); cases hz
      · split at hG
        · simp at hG
        · split at hG
          · exact ⟨_, l, kn, by omega, ex, ua.symm⟩
          · cases hG

/-! ## tail mode -/

/-- a CONTINUE's new states: related as callee arguments at the state kinds `P`; an owned state's pre-existing block
is a consumed slot's; a read-only state is a read-only slot's block -/
def StOK (σ σ' : AH) (Kk : List Nat) (F F' : List Bool) (Γ : List (Option Kd)) (env : List W) (ew : Env) (P : List Nat)
    (st : List W) (ws : List UInt64) : Prop :=
  ArgsR σ' P st ws ∧
  (∀ (j : Nat) (l : List UInt64) (u : UInt64), P[j]? = some 1 → st[j]? = some (W.b l) → ws[j]? = some u →
    (σ u.toNat).isSome → ∃ j' l', Kn Γ j' ∧ Cons F F' j' ∧ env[j']? = some (.b l') ∧ ew j' = u) ∧
  (∀ (j : Nat) (l : List UInt64) (u : UInt64), P[j]? = some 3 → st[j]? = some (W.b l) → ws[j]? = some u →
    ∃ k l', Kn Γ k ∧ Kk.getD k 0 = 2 ∧ env[k]? = some (.b l') ∧ ew k = u)

/-- the tail-mode claim (loop step arm, typed with the state kinds `sk`) -/
def TailOK (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ sk ks F F' es env ew σ sp H r H', TyN D Γ (some sk) e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → st K e ew sp H = some (r, H') →
    ∃ σ' out, ev cx e env = .ok out ∧ AHeap K.hb K.κ H' σ' ∧ EnvI σ' oc.K F' Γ env ew ∧ Ch σ σ' Γ F F' env ew ∧
      Mono F F' ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top ∧ Grow σ σ' ∧
      ((∃ v vs, out = .inl v ∧ r = .inl vs ∧ ResI σ' oc.K F' Γ env ew es v vs ∧ Src σ Γ F F' env ew es v vs ∧
          ∀ x ∈ es, x ≤ 1 ∨ 4 ≤ x) ∨
       (∃ st' ws, out = .inr st' ∧ r = .inr ws ∧ StOK σ σ' oc.K F F' Γ env ew (OwnSpec.stD oc.K oc.npw) st' ws))

theorem tail_exit {cx : Ctx} {K : SC} {oc : OwnSpec.Cx} {D : List Sig} {e : ParSpec.Nd} (hN : NodeOK cx K oc D e)
    (hT' : ∀ Γ sk ks, TyN D Γ (some sk) e ks → TyN D Γ none e ks)
    (hst : ∀ env sp H, st K e env sp H = exitS (sv K e) env sp H) : TailOK cx K oc D e := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H r H' hT hc hE hA h8 hhb hr hs
  rw [hst] at hs
  simp only [exitS, Option.map_eq_some_iff] at hs
  obtain ⟨⟨vs, H2⟩, hs, he⟩ := hs
  simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨σ', v, ev', hA', hR', hE', hCh, hM, h8', hb', hS, hsh, hG⟩ :=
    hN hC hK2 Γ ks F F' es env ew σ sp H vs H2 (hT' Γ sk ks hT) hc hE hA h8 hhb hr hs
  exact ⟨σ', .inl v, ev', hA', hE', hCh, hM, h8', hb', hG, .inl ⟨v, vs, rfl, rfl, hR', hS, hsh⟩⟩

theorem tail_cont {cx : Ctx} {K : SC} {oc : OwnSpec.Cx} {D : List Sig} (hW : RsW oc)
    (hAll : ∀ n, NodeOK cx K oc D n) (e : ParSpec.Nd) : TailOK cx K oc D (ParSpec.Nd.cont e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H r H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | cont te =>
    simp only [st, contS, Option.map_eq_some_iff] at hs
    obtain ⟨⟨ua, H1⟩, hs, he⟩ := hs
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    unfold OwnSpec.chk at hc
    split at hc
    · -- CONTINUE (a, b, …): the argument list closed at the state kinds
      rename_i cs
      cases te with
      | pair tl =>
        obtain ⟨⟨x1, x2⟩, hl, h⟩ := Option.bind_eq_some_iff.1 hc
        obtain ⟨⟨yF, yE⟩, hf, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        simp only [sv] at hs
        obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW cs (fun n _ => hAll n) tl hl hE hA h8 hhb hr hs
        simp only [List.nil_append] at hesA; subst hesA
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨hlP, hfc, hfb⟩ := fin_some hf
        simp only at hlP hfc hfb
        have mf := finC_mono _ _ _ _ hfc
        obtain ⟨hArgs, hown, hro⟩ := fin_args hR1 hE1 hr1 hS1 hM1 hfc hfb hlP (fun i e he => by simpa using hok i e he)
        refine ⟨σ1, .inr v, by simp [ev, evl, val, bind, Except.bind, pure, Except.pure], hA1, hE1.mono mf,
          hCh1.weak mf, hM1.trans mf, h81, hb1, hGr, .inr ⟨v, ua, rfl, rfl, hArgs, fun j l u a b c d => (hown j l u a b c).2 d,
          hro⟩⟩
    · -- CONTINUE e: one value, checked at the state kinds
      obtain ⟨⟨x1, x2⟩, hcx, h⟩ := Option.bind_eq_some_iff.1 hc
      split at h
      · rename_i hokA
        obtain ⟨⟨yF, yE⟩, hf, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨σ1, v, evv, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr⟩ :=
          hAll e hC hK2 Γ sk F x1 x2 env ew σ sp H ua H1 te hcx hE hA h8 hhb hr hs
        have hr1 : R2 oc.K x1 := hr.keep (chk_keep hK2 hW te rfl _ _ _ hcx).1
        obtain ⟨hlP, hfc, hfb⟩ := fin_some hf
        simp only at hlP hfc hfb
        have mf := finC_mono _ _ _ _ hfc
        obtain ⟨hArgs, hown, hro⟩ := fin_args hR1 hE1 hr1 hS1 hM1 hfc hfb hlP
          (fun i e he => ⟨_, by simpa using okAll_idx hokA i e he⟩)
        refine ⟨σ1, .inr v, by simp [ev, evv, val, bind, Except.bind, pure, Except.pure], hA1, hE1.mono mf,
          hCh1.weak mf, hM1.trans mf, h81, hb1, hGr, .inr ⟨v, ua, rfl, rfl, hArgs, fun j l u a b c d => (hown j l u a b c).2 d,
          hro⟩⟩
      · cases h

end NanoMain

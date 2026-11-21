/- Nano/SelfHost/Bridge/MainBridge12: the Sem ⇐ sv bridge — tail mode (loop arms: E's `st` ↔ `ev`'s `.inl` exit / `.inr`
CONTINUE). -/
import Nano.SelfHost.Bridge.MainBridge11

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

theorem tr_mono : ∀ (F F1 : List Bool) (es es1 : List Nat), OwnSpec.tr F es = some (F1, es1) → Mono F F1
  | F, F1, [], es1, h => by
    simp only [OwnSpec.tr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact Mono.refl _
  | F, F1, e :: es, es1, h => by
    simp only [OwnSpec.tr] at h
    split at h
    · split at h
      · obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he; exact tr_mono _ _ _ _ h2
      · cases h
    · split at h
      · obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he; exact tr_mono _ _ _ _ h2
      · split at h
        · obtain ⟨Fh, hc, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨F2, es2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
          exact (consume_spec hc).2.2.1.trans (tr_mono _ _ _ _ h2)
        · cases h

theorem StOK.mono {σ σ' : AH} {Kk : List Nat} {F F1 F2 : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {P : List Nat} {st : List W} {ws : List UInt64} (m : Mono F1 F2) (h : StOK σ σ' Kk F F1 Γ env ew P st ws) :
    StOK σ σ' Kk F F2 Γ env ew P st ws :=
  ⟨h.1, fun j l u a b c d => by
    obtain ⟨j', l', x, y, z, w⟩ := h.2.1 j l u a b c d; exact ⟨j', l', x, ⟨y.1, m j' y.2⟩, z, w⟩, h.2.2⟩

theorem StOK.pre {σ σ2 σ' : AH} {Kk : List Nat} {F F2 F' : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {P : List Nat} {st : List W} {ws : List UInt64} (hCh : Ch σ σ2 Γ F F2 env ew) (m1 : Mono F F2) (m2 : Mono F2 F')
    (h : StOK σ2 σ' Kk F2 F' Γ env ew P st ws) : StOK σ σ' Kk F F' Γ env ew P st ws :=
  ⟨h.1, fun j l u a b c hs => by
    by_cases hx : ∃ j l', Kn Γ j ∧ Cons F F2 j ∧ env[j]? = some (.b l') ∧ (ew j).toNat = u.toNat
    · obtain ⟨j, l', x, y, z, w⟩ := hx; exact ⟨j, l', x, ⟨y.1, m2 j y.2⟩, z, UInt64.toNat_inj.1 w⟩
    · have e2 := hCh _ hs fun s l' hk hc hl' hq => hx ⟨s, l', hk, hc, hl', hq⟩
      obtain ⟨j, l', x, y, z, w⟩ := h.2.1 j l u a b c (by rw [e2]; exact hs)
      exact ⟨j, l', x, ⟨live_of_mono m1 y.1, y.2⟩, z, w⟩, h.2.2⟩

theorem join_nil_r {t k : List Nat} (h : OwnSpec.join t [] = some k) : k = t := by
  unfold OwnSpec.join at h
  split at h
  · simp only [Option.some.injEq] at h; subst_vars; rfl
  · simp at h; exact h.symm

theorem tail_ite (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc)
    (hAll : ∀ n, NodeOK cx K oc D n) (c : Nat) (a b t e : ParSpec.Nd) (iht : TailOK cx K oc D t)
    (ihe : TailOK cx K oc D e) : TailOK cx K oc D (ParSpec.Nd.ite c a b t e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H r H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    simp only [Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
    simp only [st, ifTS, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨u, H2⟩, hp, hrest⟩ := hs
    have hry : R2 oc.K y.1 := by
      obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ hca
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hcb
      exact hr.keep ((ka.trans kb).trans (two_keep ta' tb' hy))
    obtain ⟨σ2, x1, x2, eva, evb, rfl, hA2, hE2, hCh2, hM2, h82, hb2, hG2⟩ :=
      operands2 (hAll a) (hAll b) hC hK2 hW ta tb hca hcb hy hE hA h8 hhb hr hp
    have hev : ev cx (ParSpec.Nd.ite c a b t e) env =
        (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
      rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
    simp only at hrest
    have mt := tr_mono _ _ _ _ h2
    have me := tr_mono _ _ _ _ h4
    have lt1 := tr_len _ _ _ _ h2
    have le1 := tr_len _ _ _ _ h4
    have ct := chk_len_tail hRs tt _ _ _ h1
    have ce := chk_len_tail hRs te _ _ _ h3
    by_cases hcmp : cmpF c x1 x2
    · rw [if_pos hcmp] at hrest
      have hev' : ev cx (ParSpec.Nd.ite c a b t e) env = ev cx t env := by
        rw [hev, if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)]
      obtain ⟨σ3, out, evt, hA3, hE3, hCh3, hM3, h83, hb3, hG3, hout⟩ :=
        iht hC hK2 Γ sk ks _ _ _ env ew σ2 sp H2 r H' tt h1 hE2 hA2 h82 hb2 hry hrest
      have mo := mono_orF_l t1.1 e1.1
      refine ⟨σ3, out, by rw [hev']; exact evt, hA3, (hE3.mono mt).mono mo, (Ch.trans hCh2 hCh3 hM2 hM3).weak (mt.trans mo),
        ((hM2.trans hM3).trans mt).trans mo, h83, hb3, hG2.trans hG3, ?_⟩
      rcases hout with ⟨v, vs, rfl, rfl, hR3, hS3, -⟩ | ⟨st', ws, rfl, rfl, hst⟩
      · left
        obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR3 hE3 h2
        have sT := (tr_src _ _ _ _ _ _ hR3 hM3 hS3 h2).2
        have kv := (ev_ok hC tt env hE.ty).2.1 v evt
        have lv : t0.2.length = ks.length := by rw [hR3.len.1, ← kOf_length, kv]
        have hk1 : ∀ x ∈ k, x ≤ 1 := by
          intro x hx
          by_cases h0 : e1.2 = []
          · rw [h0] at hj; rw [join_nil_r hj] at hx; exact r4 x hx
          · exact (resI_join hR4 r4 (tr_le1 _ _ _ _ h4) (by rcases ce with h | h <;> simp_all) hj).2 x hx
        refine ⟨v, vs, rfl, rfl, ?_, ?_, fun z hz => .inl (hk1 z hz)⟩
        · by_cases h0 : e1.2 = []
          · rw [h0] at hj; rw [join_nil_r hj]; exact ResI.mono mo hR4
          · exact ResI.mono mo (resI_join hR4 r4 (tr_le1 _ _ _ _ h4) (by rcases ce with h | h <;> simp_all) hj).1
        · refine Src.pre hCh2 hM2 ((hM3.trans m4).trans mo) (Src.mono mo ?_)
          by_cases h0 : e1.2 = []
          · rw [h0] at hj; rw [join_nil_r hj]; exact sT
          · exact src_join hR4 sT r4 (tr_le1 _ _ _ _ h4) hj
      · exact .inr ⟨st', ws, rfl, rfl, StOK.pre hCh2 hM2 ((hM3.trans mt).trans mo) (StOK.mono (mt.trans mo) hst)⟩
    · rw [if_neg hcmp] at hrest
      have hev' : ev cx (ParSpec.Nd.ite c a b t e) env = ev cx e env := by
        rw [hev, if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))]
      obtain ⟨σ3, out, evt, hA3, hE3, hCh3, hM3, h83, hb3, hG3, hout⟩ :=
        ihe hC hK2 Γ sk ks _ _ _ env ew σ2 sp H2 r H' te h3 hE2 hA2 h82 hb2 hry hrest
      have mo := mono_orF_r t1.1 e1.1
      refine ⟨σ3, out, by rw [hev']; exact evt, hA3, (hE3.mono me).mono mo, (Ch.trans hCh2 hCh3 hM2 hM3).weak (me.trans mo),
        ((hM2.trans hM3).trans me).trans mo, h83, hb3, hG2.trans hG3, ?_⟩
      rcases hout with ⟨v, vs, rfl, rfl, hR3, hS3, -⟩ | ⟨st', ws, rfl, rfl, hst⟩
      · left
        obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR3 hE3 h4
        have sT := (tr_src _ _ _ _ _ _ hR3 hM3 hS3 h4).2
        have kv := (ev_ok hC te env hE.ty).2.1 v evt
        have lv : e0.2.length = ks.length := by rw [hR3.len.1, ← kOf_length, kv]
        have hjr : OwnSpec.join t1.2 e1.2 = some k → (t1.2 = [] ∧ k = e1.2) ∨ (t1.2.length = e1.2.length) := by
          intro hj'
          by_cases h0 : t1.2 = []
          · rw [h0] at hj'; unfold OwnSpec.join at hj'; simp at hj'; exact .inl ⟨h0, hj'.symm⟩
          · rcases ct with h | h
            · exact absurd (List.length_eq_zero_iff.1 (by rw [lt1, h]; rfl)) h0
            · exact .inr (by omega)
        have hk1 : ∀ x ∈ k, x ≤ 1 := by
          intro x hx
          rcases hjr hj with ⟨-, rfl⟩ | hl
          · exact r4 x hx
          · exact (resI_join_r hR4 (tr_le1 _ _ _ _ h2) r4 hl hj).2 x hx
        refine ⟨v, vs, rfl, rfl, ?_, ?_, fun z hz => .inl (hk1 z hz)⟩
        · rcases hjr hj with ⟨-, rfl⟩ | hl
          · exact ResI.mono mo hR4
          · exact ResI.mono mo (resI_join_r hR4 (tr_le1 _ _ _ _ h2) r4 hl hj).1
        · refine Src.pre hCh2 hM2 ((hM3.trans m4).trans mo) (Src.mono mo ?_)
          rcases hjr hj with ⟨-, rfl⟩ | hl
          · exact sT
          · exact src_join_r hR4 sT (tr_le1 _ _ _ _ h2) r4 hj
      · exact .inr ⟨st', ws, rfl, rfl, StOK.pre hCh2 hM2 ((hM3.trans me).trans mo) (StOK.mono (me.trans mo) hst)⟩

theorem tail_let (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc)
    (hAll : ∀ n, NodeOK cx K oc D n) (s w : Nat) (v b : ParSpec.Nd) (ihb : TailOK cx K oc D b) :
    TailOK cx K oc D (ParSpec.Nd.letE s w v b) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H rr H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | letE hv htv hsl hfr hb =>
    rename_i tv
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨v0, hcv, v1, htr, hc⟩ := hc
    split at hc
    · rename_i hcond
      obtain ⟨-, hsK, hv12, -⟩ := hcond
      obtain ⟨b0, hcb, htr2⟩ := Option.bind_eq_some_iff.1 hc
      simp only [st, letTS, Option.bind_eq_some_iff] at hs
      obtain ⟨⟨r, H1⟩, hsv, hsb⟩ := hs
      obtain ⟨σ1, x, evv, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hG1⟩ :=
        hAll v hC hK2 Γ tv F _ _ env ew σ sp H r H1 hv hcv hE hA h8 hhb hr hsv
      obtain ⟨m2, hR2, r2, -, -⟩ := tr_spec hK2 _ x r _ _ _ hR1 hE1 htr
      obtain ⟨-, hS2⟩ := tr_src _ _ _ _ _ _ hR1 hM1 hS1 htr
      obtain ⟨-, kv, -⟩ := ev_ok hC hv env hE.ty
      have hk := kv x evv
      have hxl : x.length = w := by rw [← kOf_length, hk, htv]
      have hel := hE.len
      have hss : setSlots env s x = .ok (env.take s ++ x ++ env.drop (s + x.length)) := by
        simp only [setSlots]; rw [if_pos (by omega)]
      obtain ⟨env1, e1, he1⟩ := setSlots_ok (vs := x) (s := s) hE.ty (by omega)
      rw [hss] at e1; cases e1
      rw [hk] at he1
      have hrv : R2 oc.K v1.1 := by
        obtain ⟨kv, tv'⟩ := chk_keep hK2 hW hv rfl _ _ _ hcv
        exact hr.keep (kv.trans (tr_keep _ _ _ _ tv' htr).1)
      have hEb := let_envI (r := r) (hE1.mono m2) hR2 hv12 r2 hxl hsK htv hsl hfr he1
      obtain ⟨σ2, out, evb, hA2, hE3, hCh3, hM3, h83, hb3, hG3, hout⟩ :=
        ihb hC hK2 _ sk ks _ _ _ _ _ σ1 sp H1 rr H' hb hcb hEb hA1 h81 hb1 hrv hsb
      have m4 := tr_mono _ _ _ _ htr2
      have P := let_outer (r := r) (ew := ew) hxl htv hsl hel hfr
      have mF1 : Mono F v1.1 := hM1.trans m2
      have mG : Mono v1.1 F' := hM3.trans m4
      have S1 := let_src1 (σ := σ) hR2 hS2 hv12 r2 hxl hsK htv hsl hel mF1 mG
      have hCh1' := hCh1.weak m2
      have hev : ev cx (ParSpec.Nd.letE s w v b) env = .ok out := by
        simp only [ev, evv, val, bind, Except.bind]; rw [if_pos hxl]; simp only [hss]; exact evb
      refine ⟨σ2, out, hev, hA2, envI_restrict P (hE3.mono m4) hel hE.ty, ?_, mF1.trans mG, h83, hb3, hG1.trans hG3, ?_⟩
      · intro a ha hn
        have e1 : σ1 a = σ a := hCh1' a ha fun t l kt ct et => hn t l kt ⟨ct.1, mG t ct.2⟩ et
        rw [← e1]
        refine hCh3 a (by rw [e1]; exact ha) fun t l kt ct et hq => ?_
        obtain ⟨j, l', kj, cj, ej, wj⟩ := S1 t l kt et (by rw [hq]; exact ha) ⟨ct.1, m4 t ct.2⟩
        exact hn j l' kj cj ej (by rw [wj]; exact hq)
      · -- the outer-frame image of an owned block's source
        have back : ∀ u, (σ u.toNat).isSome → ((σ1 u.toNat).isSome → ∃ j l', Kn (setK Γ s tv) j ∧ Cons v1.1 F' j ∧
            (env.take s ++ x ++ env.drop (s + x.length))[j]? = some (.b l') ∧ setW ew s w r j = u) →
            ∃ j l', Kn Γ j ∧ Cons F F' j ∧ env[j]? = some (.b l') ∧ ew j = u := by
          intro u hu H
          by_cases hx : ∃ j l', Kn Γ j ∧ Cons F v1.1 j ∧ env[j]? = some (.b l') ∧ (ew j).toNat = u.toNat
          · obtain ⟨j, l', a, c, d, e⟩ := hx; exact ⟨j, l', a, ⟨c.1, mG j c.2⟩, d, UInt64.toNat_inj.1 e⟩
          · have e2 := hCh1' _ hu fun t l' kt ct et hq => hx ⟨t, l', kt, ct, et, hq⟩
            obtain ⟨j, l', kj, cj, ej, wj⟩ := H (by rw [e2]; exact hu)
            obtain ⟨j', l'', a, c, d, e⟩ := S1 j l' kj ej (by rw [wj]; exact hu) cj
            exact ⟨j', l'', a, c, d, by rw [e, wj]⟩
        rcases hout with ⟨y, vs, rfl, rfl, hR3, hS3, -⟩ | ⟨st', ws, rfl, rfl, hst⟩
        · left
          obtain ⟨m4', hR4, r4, -, -⟩ := tr_spec hK2 _ y vs _ _ _ hR3 hE3 htr2
          obtain ⟨-, hS4⟩ := tr_src _ _ _ _ _ _ hR3 hM3 hS3 htr2
          exact ⟨y, vs, rfl, rfl, resI_restrict P hR4 (fun e he => by have := r4 e he; omega),
            Src.imp (fun u hu H => back u hu (fun h => H h)) hS4, fun z hz => .inl (r4 z hz)⟩
        · right
          refine ⟨st', ws, rfl, rfl, hst.1, fun j l u a b c hu => back u hu fun h => ?_, fun j l u a b c => ?_⟩
          · obtain ⟨j', l', kj, cj, ej, wj⟩ := hst.2.1 j l u a b c h
            exact ⟨j', l', kj, ⟨cj.1, m4 j' cj.2⟩, ej, wj⟩
          · obtain ⟨k, l', kk, k2, ek, wk⟩ := hst.2.2 j l u a b c
            have ho : k < s ∨ s + w ≤ k := by
              refine Classical.byContradiction fun h => ?_
              have hi : k - s < w := by omega
              have e' : v1.2[k - s]? = some (oc.K.getD k 0) := by
                rw [hv12, List.getElem?_take_of_lt hi, List.getElem?_drop, show s + (k - s) = k by omega,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < oc.K.length by omega)]
                rfl
              have := r2 _ (List.mem_of_getElem? e'); omega
            obtain ⟨kd, hkd⟩ := kk
            refine ⟨k, l', ⟨kd, by rw [← setK_get_out (Γ := Γ) (s := s) (ks := tv) (by omega) k (by omega), hkd]⟩, k2,
              by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact ek, ?_⟩
            rw [← wk, setW_out _ _ _ _ _ ho]
    · cases hc

theorem tail_loop (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (z s : ParSpec.Nd) :
    TailOK cx K oc D (ParSpec.Nd.loop z s) := by
  intro _ _ Γ sk ks F F' es env ew σ sp H r H' _ hc
  simp [OwnSpec.chk] at hc

/-- **tail mode, every node** -/
theorem tail_all (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) : ∀ e : ParSpec.Nd, TailOK cx K oc D e
  | .ite c a b t e => tail_ite cx K oc D hRs hW (node_all cx K oc D hRs hW hX hCR) c a b t e
      (tail_all cx K oc D hRs hW hX hCR t) (tail_all cx K oc D hRs hW hX hCR e)
  | .letE s w v b => tail_let cx K oc D hRs hW (node_all cx K oc D hRs hW hX hCR) s w v b
      (tail_all cx K oc D hRs hW hX hCR b)
  | .cont e => tail_cont hW (node_all cx K oc D hRs hW hX hCR) e
  | .loop z s => tail_loop cx K oc D z s
  | .const v => tail_exit (node_all cx K oc D hRs hW hX hCR _) (fun _ _ _ h => by cases h; exact .const)
      (fun _ _ _ => by simp only [st])
  | .loc s w => tail_exit (node_all cx K oc D hRs hW hX hCR _) (fun _ _ _ h => by cases h with | loc hk => exact .loc hk)
      (fun _ _ _ => by simp only [st])
  | .bin op a b => tail_exit (node_all cx K oc D hRs hW hX hCR _)
      (fun _ _ _ h => by cases h with | bin o1 o2 ta tb => exact .bin o1 o2 ta tb) (fun _ _ _ => by simp only [st])
  | .pair cs => tail_exit (node_all cx K oc D hRs hW hX hCR _)
      (fun _ _ _ h => by cases h with | pair tl => exact .pair tl) (fun _ _ _ => by simp only [st])
  | .call i as => tail_exit (node_all cx K oc D hRs hW hX hCR _)
      (fun _ _ _ h => by cases h with | call tl hd => exact .call tl hd) (fun _ _ _ => by simp only [st])
  | .prim p as => tail_exit (node_all cx K oc D hRs hW hX hCR _)
      (fun _ _ _ h => by cases h with | prim tl hp hn => exact .prim tl hp hn) (fun _ _ _ => by simp only [st])

end NanoMain

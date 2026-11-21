/- Nano/SelfHost/Bridge/MainBridge7: the Sem ⇐ sv bridge — LET (bound slots enter Γ / env / E's word env; results and
invariants restricted back to the outer frame). -/
import Nano.SelfHost.Bridge.MainBridge6

namespace NanoMain
open Templates

/-! ## indexed views of `ResI` / `OwnFree` / `Src` -/

theorem resI_idx {σ Kk F Γ env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64} (i : Nat),
    ResI σ Kk F Γ env ew es v vs → ∀ {e x u}, es[i]? = some e → v[i]? = some x → vs[i]? = some u →
    (e < 4 → VR σ x u) ∧ (e = 0 → ∃ y, x = .w y) ∧ (e = 1 → ∀ l, x = .b l → ∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 →
      OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ u)
  | _ :: _, _ :: _, _ :: _, 0, h, _, _, _, he, hx, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hx hu; subst he hx hu
    exact ⟨h.1, h.2.1, fun h1 l hl => (h.2.2.1 h1 l hl).1⟩
  | _ :: _, _ :: _, _ :: _, i + 1, h, _, _, _, he, hx, hu => by
    simp only [List.getElem?_cons_succ] at he hx hu; exact resI_idx i h.2.2.2.2 he hx hu
  | [], _, _, _, _, _, _, _, he, _, _ => by simp at he
  | _ :: _, [], _, _, _, _, _, _, _, hx, _ => by simp at hx
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hu => by simp at hu

theorem ownFree_idx : ∀ {es : List Nat} {v : List W} {vs : List UInt64} {u : UInt64} (j : Nat), OwnFree es v vs u →
    ∀ {l u'}, es[j]? = some 1 → v[j]? = some (.b l) → vs[j]? = some u' → u' ≠ u
  | _ :: _, _ :: _, _ :: _, _, 0, h, _, _, he, hx, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hx hu; subst hx hu; exact h.1 he _ rfl
  | _ :: _, _ :: _, _ :: _, _, j + 1, h, _, _, he, hx, hu => by
    simp only [List.getElem?_cons_succ] at he hx hu; exact ownFree_idx j h.2 he hx hu
  | [], _, _, _, _, _, _, _, he, _, _ => by simp at he
  | _ :: _, [], _, _, _, _, _, _, _, hx, _ => by simp at hx
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hu => by simp at hu

theorem resI_pair {σ Kk F Γ env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64} (i j : Nat),
    ResI σ Kk F Γ env ew es v vs → i < j → ∀ {li lj ui uj}, es[i]? = some 1 → es[j]? = some 1 → v[i]? = some (.b li) →
    v[j]? = some (.b lj) → vs[i]? = some ui → vs[j]? = some uj → ui ≠ uj
  | _ :: _, _ :: _, _ :: _, 0, j + 1, h, _, _, _, _, _, ei, ej, xi, xj, hi, hj => by
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ei xi hi ej xj hj
    subst xi hi
    exact Ne.symm (ownFree_idx j ((h.2.2.1 ei _ rfl).2) ej xj hj)
  | _ :: _, _ :: _, _ :: _, i + 1, j + 1, h, hij, _, _, _, _, ei, ej, xi, xj, hi, hj => by
    simp only [List.getElem?_cons_succ] at ei xi hi ej xj hj
    exact resI_pair i j h.2.2.2.2 (by omega) ei ej xi xj hi hj
  | [], _, _, _, _, _, _, _, _, _, _, ei, _, _, _, _, _ => by simp at ei
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, xi, _, _, _ => by simp at xi
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, hi, _ => by simp at hi
  | _ :: _, _ :: _, _ :: _, _, 0, _, hij, _, _, _, _, _, _, _, _, _, _ => by omega

theorem src_idx {σ Γ F F' env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64} (i : Nat),
    Src σ Γ F F' env ew es v vs → ∀ {l u}, es[i]? = some 1 → v[i]? = some (.b l) → vs[i]? = some u →
    (σ u.toNat).isSome → ∃ j l', Kn Γ j ∧ Cons F F' j ∧ env[j]? = some (.b l') ∧ ew j = u
  | _ :: _, _ :: _, _ :: _, 0, h, _, _, he, hx, hu, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hx hu; subst hx hu; exact h.1 he _ rfl hs
  | _ :: _, _ :: _, _ :: _, i + 1, h, _, _, he, hx, hu, hs => by
    simp only [List.getElem?_cons_succ] at he hx hu; exact src_idx i h.2 he hx hu hs
  | [], _, _, _, _, _, _, he, _, _, _ => by simp at he
  | _ :: _, [], _, _, _, _, _, _, hx, _, _ => by simp at hx
  | _ :: _, _ :: _, [], _, _, _, _, _, _, hu, _ => by simp at hu

/-! ## restriction to an outer frame (no tags, outer slots unchanged) -/

def Outer (Γ Γ' : List (Option Kd)) (env env' : List W) (ew ew' : Env) : Prop :=
  ∀ t, Kn Γ t → Kn Γ' t ∧ env'[t]? = env[t]? ∧ ew' t = ew t

theorem resI_restrict {σ Kk F Γ Γ' env env' ew ew'} (P : Outer Γ Γ' env env' ew ew') :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, ResI σ Kk F Γ' env' ew' es v vs → (∀ e ∈ es, e < 4) →
    ResI σ Kk F Γ env ew es v vs
  | [], [], [], _, _ => trivial
  | e :: es, x :: v, u :: vs, ⟨c1, c2, c3, _, cR⟩, h4 => by
    refine ⟨c1, c2, fun h1 l hl => ⟨fun t ls kt k0 dt et => ?_, (c3 h1 l hl).2⟩,
      fun h => absurd (h4 e (by simp)) (by omega), resI_restrict P cR fun z hz => h4 z (by simp [hz])⟩
    obtain ⟨k', e', w'⟩ := P t kt
    rw [← w']; exact (c3 h1 l hl).1 t ls k' k0 dt (by rw [e', et])
  | [], _ :: _, _, h, _ | [], [], _ :: _, h, _ | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], h, _ => by simp [ResI] at h

theorem envI_restrict {σ Kk F Γ Γ' env env' ew ew'} (P : Outer Γ Γ' env env' ew ew') (h : EnvI σ Kk F Γ' env' ew')
    (hl : env.length = Γ.length) (ht : EnvOK env Γ) : EnvI σ Kk F Γ env ew where
  len := hl
  ty := ht
  val s ks hr := by
    obtain ⟨k', e', w'⟩ := P s ks
    obtain ⟨y, hy, vr, wd⟩ := h.val s k' hr
    exact ⟨y, by rw [← e', hy], by rw [← w']; exact vr, wd⟩
  dist s t ls lt hst ks kt k1 k0 ds dt es et := by
    obtain ⟨k1', e1', w1'⟩ := P s ks
    obtain ⟨k2', e2', w2'⟩ := P t kt
    rw [← w1', ← w2']; exact h.dist s t ls lt hst k1' k2' k1 k0 ds dt (by rw [e1', es]) (by rw [e2', et])

/-! ## the LET slot layout -/

theorem rng (s w k : Nat) : (k < s ∨ s + w ≤ k) ∨ ∃ i, i < w ∧ k = s + i := by
  by_cases h : k < s ∨ s + w ≤ k
  · exact .inl h
  · exact .inr ⟨k - s, by omega, by omega⟩

theorem ss_in {env x : List W} {s i : Nat} (hs : s + x.length ≤ env.length) (hi : i < x.length) :
    (env.take s ++ x ++ env.drop (s + x.length))[s + i]? = x[i]? := by
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega)]
  have : (List.take s env).length = s := by simp; omega
  rw [this, Nat.add_sub_cancel_left, List.getElem?_append_left hi]

theorem ss_out {env x : List W} {s k : Nat} (hs : s + x.length ≤ env.length) (hk : k < s ∨ s + x.length ≤ k) :
    (env.take s ++ x ++ env.drop (s + x.length))[k]? = env[k]? := by
  rcases hk with hk | hk
  · rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]
  · have : (List.take s env ++ x).length = s + x.length := by simp; omega
    rw [List.getElem?_append_right (by omega), this, List.getElem?_drop]; congr 1; omega

theorem setW_in (ew : Env) (s w : Nat) (r : List UInt64) (i : Nat) (hi : i < w) : setW ew s w r (s + i) = r.getD i 0 := by
  simp [setW, hi]

theorem setW_out (ew : Env) (s w : Nat) (r : List UInt64) (k : Nat) (hk : k < s ∨ s + w ≤ k) : setW ew s w r k = ew k := by
  simp only [setW]; rw [if_neg (by omega)]

theorem let_outer {Γ : List (Option Kd)} {env x : List W} {ew : Env} {s w : Nat} {tv : List Kd} {r : List UInt64}
    (hxl : x.length = w) (htv : tv.length = w) (hsl : s + w ≤ Γ.length) (hel : env.length = Γ.length)
    (hfr : ∀ k, s ≤ k → k < s + w → Γ[k]? = some none) :
    Outer Γ (setK Γ s tv) env (env.take s ++ x ++ env.drop (s + x.length)) ew (setW ew s w r) := by
  intro t ⟨kd, hk⟩
  have ho : t < s ∨ s + w ≤ t := by
    refine Classical.byContradiction fun h => ?_
    rw [hfr t (by omega) (by omega)] at hk; cases hk
  exact ⟨⟨kd, by rw [setK_get_out (by omega) t (by omega), hk]⟩, ss_out (by omega) (by omega), setW_out _ _ _ _ _ ho⟩

theorem let_envI {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env x : List W} {ew : Env}
    {s w : Nat} {tv : List Kd} {r : List UInt64} {es : List Nat}
    (hE : EnvI σ Kk F Γ env ew) (hR : ResI σ Kk F Γ env ew es x r) (hes : es = (Kk.drop s).take w)
    (h1 : ∀ e ∈ es, e ≤ 1) (hxl : x.length = w) (hsK : s + w ≤ Kk.length) (htv : tv.length = w)
    (hsl : s + w ≤ Γ.length) (hfr : ∀ k, s ≤ k → k < s + w → Γ[k]? = some none)
    (he' : EnvOK (env.take s ++ x ++ env.drop (s + x.length)) (setK Γ s tv)) :
    EnvI σ Kk F (setK Γ s tv) (env.take s ++ x ++ env.drop (s + x.length)) (setW ew s w r) := by
  have hel := hE.len
  have hrl : r.length = w := by have := hR.len; rw [← this.2, hxl]
  have esi : ∀ i, i < w → es[i]? = some (Kk.getD (s + i) 0) := by
    intro i hi; rw [hes, List.getElem?_take_of_lt hi, List.getElem?_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show s + i < Kk.length by omega)]; rfl
  have xi : ∀ i (hi : i < w), x[i]? = some (x[i]'(by omega)) := fun i hi => List.getElem?_eq_getElem (by omega)
  have ri : ∀ i, i < w → r[i]? = some (r.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < r.length by omega)]; rfl
  have k1 : ∀ i, i < w → Kk.getD (s + i) 0 ≤ 1 := fun i hi => h1 _ (List.mem_of_getElem? (esi i hi))
  have Kout : ∀ k, (k < s ∨ s + w ≤ k) → Kn (setK Γ s tv) k → Kn Γ k := fun k hk ⟨kd, h⟩ =>
    ⟨kd, by rw [← setK_get_out (Γ := Γ) (s := s) (ks := tv) (by omega) k (by omega), h]⟩
  refine ⟨he'.length_eq, he', fun k kn hr => ?_, fun a b la lb hab ka kb ka1 kb0 da db ea eb => ?_⟩
  · rcases rng s w k with hk | ⟨i, hi, rfl⟩
    · obtain ⟨y, hy, vr, wd⟩ := hE.val k (Kout k hk kn) hr
      exact ⟨y, by rw [ss_out (by omega) (by omega), hy], by rw [setW_out _ _ _ _ _ hk]; exact vr, wd⟩
    · obtain ⟨c1, c2, -⟩ := resI_idx i hR (esi i hi) (xi i hi) (ri i hi)
      have := k1 i hi
      exact ⟨x[i]'(by omega), by rw [ss_in (by omega) (by omega), xi i hi], by rw [setW_in _ _ _ _ _ hi]; exact c1 (by omega), c2⟩
  · rcases rng s w a with ha | ⟨i, hi, rfl⟩ <;> rcases rng s w b with hb | ⟨j, hj, rfl⟩
    · rw [setW_out _ _ _ _ _ ha, setW_out _ _ _ _ _ hb]
      exact hE.dist a b la lb hab (Kout a ha ka) (Kout b hb kb) ka1 kb0 da db
        (by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact ea)
        (by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact eb)
    · rw [setW_out _ _ _ _ _ ha, setW_in _ _ _ _ _ hj]
      have := k1 j hj
      rw [ss_in (by omega) (by omega)] at eb
      obtain ⟨-, -, c3⟩ := resI_idx j hR (esi j hj) eb (ri j hj)
      exact c3 (by omega) lb rfl a la (Kout a ha ka) (by omega) da
        (by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact ea)
    · rw [setW_in _ _ _ _ _ hi, setW_out _ _ _ _ _ hb]
      rw [ss_in (by omega) (by omega)] at ea
      obtain ⟨-, -, c3⟩ := resI_idx i hR (esi i hi) ea (ri i hi)
      exact Ne.symm (c3 ka1 la rfl b lb (Kout b hb kb) kb0 db
        (by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact eb))
    · rw [setW_in _ _ _ _ _ hi, setW_in _ _ _ _ _ hj]
      have := k1 j hj
      rw [ss_in (by omega) (by omega)] at ea eb
      have ei := esi i hi; have ej := esi j hj
      rw [ka1] at ei; rw [show Kk.getD (s + j) 0 = 1 by omega] at ej
      rcases Nat.lt_or_gt_of_ne (show i ≠ j by omega) with h | h
      · exact resI_pair i j hR h ei ej ea eb (ri i hi) (ri j hj)
      · exact Ne.symm (resI_pair j i hR h ej ei eb ea (ri j hj) (ri i hi))

theorem Src.imp {σ σ' : AH} {Γ Γ' : List (Option Kd)} {F F' G G' : List Bool} {env env' : List W} {ew ew' : Env}
    (h : ∀ u, (σ u.toNat).isSome → ((σ' u.toNat).isSome → ∃ j l', Kn Γ' j ∧ Cons G G' j ∧ env'[j]? = some (.b l') ∧
      ew' j = u) → ∃ j l', Kn Γ j ∧ Cons F F' j ∧ env[j]? = some (.b l') ∧ ew j = u) :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, Src σ' Γ' G G' env' ew' es v vs → Src σ Γ F F' env ew es v vs
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ => by simp [Src]
  | _ :: _, _ :: _, u :: _, ⟨h1, t⟩ => ⟨fun e1 l hl hs => h u hs (h1 e1 l hl), Src.imp h t⟩

/-- a buffer slot of the LET frame whose block pre-existed is an outer slot, or a bound slot holding a block that an
outer slot consumed by the value gave up -/
theorem let_src1 {σ σ1 : AH} {Kk : List Nat} {F F1 G : List Bool} {Γ : List (Option Kd)} {env x : List W} {ew : Env}
    {s w : Nat} {tv : List Kd} {r : List UInt64} {es : List Nat}
    (hR : ResI σ1 Kk F1 Γ env ew es x r) (hS : Src σ Γ F F1 env ew es x r) (hes : es = (Kk.drop s).take w)
    (h1 : ∀ e ∈ es, e ≤ 1) (hxl : x.length = w) (hsK : s + w ≤ Kk.length) (htv : tv.length = w)
    (hsl : s + w ≤ Γ.length) (hel : env.length = Γ.length) (mF : Mono F F1) (mG : Mono F1 G) :
    ∀ t l, Kn (setK Γ s tv) t → (env.take s ++ x ++ env.drop (s + x.length))[t]? = some (.b l) →
      (σ (setW ew s w r t).toNat).isSome → Cons F1 G t →
      ∃ j l', Kn Γ j ∧ Cons F G j ∧ env[j]? = some (.b l') ∧ ew j = setW ew s w r t := by
  intro t l kt et hs ct
  have hrl : r.length = w := by have := hR.len; rw [← this.2, hxl]
  rcases rng s w t with ht | ⟨i, hi, rfl⟩
  · obtain ⟨kd, hk⟩ := kt
    refine ⟨t, l, ⟨kd, by rw [← setK_get_out (Γ := Γ) (s := s) (ks := tv) (by omega) t (by omega), hk]⟩,
      ⟨live_of_mono mF ct.1, ct.2⟩, by rw [← ss_out (x := x) (s := s) (by omega) (by omega)]; exact et,
      (setW_out _ _ _ _ _ ht).symm⟩
  · have esi : es[i]? = some (Kk.getD (s + i) 0) := by
      rw [hes, List.getElem?_take_of_lt hi, List.getElem?_drop, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show s + i < Kk.length by omega)]; rfl
    have ri : r[i]? = some (r.getD i 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < r.length by omega)]; rfl
    rw [ss_in (by omega) (by omega)] at et
    rw [setW_in _ _ _ _ _ hi] at hs ⊢
    have k1 := h1 _ (List.mem_of_getElem? esi)
    obtain ⟨-, c2, -⟩ := resI_idx i hR esi et ri
    have k1' : Kk.getD (s + i) 0 = 1 := by
      rcases Nat.lt_or_ge (Kk.getD (s + i) 0) 1 with h0 | h0
      · obtain ⟨y, hy⟩ := c2 (by omega); cases hy
      · omega
    rw [k1'] at esi
    obtain ⟨j, l', a, b, c, d⟩ := src_idx i hS esi et ri hs
    exact ⟨j, l', a, ⟨b.1, mG j b.2⟩, c, d⟩

theorem node_let (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (s w : Nat)
    (v b : ParSpec.Nd) (ihv : NodeOK cx K oc D v) (ihb : NodeOK cx K oc D b) :
    NodeOK cx K oc D (ParSpec.Nd.letE s w v b) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | letE hv htv hsl hfr hb =>
    rename_i tv
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨v0, hcv, v1, htr, hc⟩ := hc
    split at hc
    · rename_i hcond
      obtain ⟨-, hsK, hv12, -⟩ := hcond
      obtain ⟨b0, hcb, htr2⟩ := Option.bind_eq_some_iff.1 hc
      simp only [sv, letS, Option.bind_eq_some_iff] at hs
      obtain ⟨⟨r, H1⟩, hsv, hsb⟩ := hs
      obtain ⟨σ1, x, evv, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hG1⟩ :=
        ihv hC hK2 Γ tv F _ _ env ew σ sp H r H1 hv hcv hE hA h8 hhb hr hsv
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
      obtain ⟨σ2, y, evb, hA2, hR3, hE3, hCh3, hM3, h83, hb3, hS3, -, hG3⟩ :=
        ihb hC hK2 _ ks _ _ _ _ _ σ1 sp H1 vs H' hb hcb hEb hA1 h81 hb1 hrv hsb
      obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ y vs _ _ _ hR3 hE3 htr2
      obtain ⟨-, hS4⟩ := tr_src _ _ _ _ _ _ hR3 hM3 hS3 htr2
      have P := let_outer (r := r) (ew := ew) hxl htv hsl hel hfr
      have mF1 : Mono F v1.1 := hM1.trans m2
      have mG : Mono v1.1 F' := hM3.trans m4
      have S1 := let_src1 (σ := σ) hR2 hS2 hv12 r2 hxl hsK htv hsl hel mF1 mG
      have hCh1' := hCh1.weak m2
      have hev : ev cx (ParSpec.Nd.letE s w v b) env = .ok (.inl y) := by
        simp only [ev, evv, val, bind, Except.bind]; rw [if_pos hxl]; simp only [hss]; exact evb
      refine ⟨σ2, y, hev, hA2, resI_restrict P hR4 (fun e he => by have := r4 e he; omega),
        envI_restrict P (hE3.mono m4) hel hE.ty, ?_, mF1.trans mG, h83, hb3, ?_, fun z hz => .inl (r4 z hz), hG1.trans hG3⟩
      · intro a ha hn
        have e1 : σ1 a = σ a := hCh1' a ha fun t l kt ct et => hn t l kt ⟨ct.1, mG t ct.2⟩ et
        rw [← e1]
        refine hCh3 a (by rw [e1]; exact ha) fun t l kt ct et hq => ?_
        obtain ⟨j, l', kj, cj, ej, wj⟩ := S1 t l kt et (by rw [hq]; exact ha) ⟨ct.1, m4 t ct.2⟩
        exact hn j l' kj cj ej (by rw [wj]; exact hq)
      · refine Src.imp (fun u hu H => ?_) hS4
        by_cases hx : ∃ j l', Kn Γ j ∧ Cons F v1.1 j ∧ env[j]? = some (.b l') ∧ (ew j).toNat = u.toNat
        · obtain ⟨j, l', a, c, d, e⟩ := hx; exact ⟨j, l', a, ⟨c.1, mG j c.2⟩, d, UInt64.toNat_inj.1 e⟩
        · have e2 := hCh1' _ hu fun t l' kt ct et hq => hx ⟨t, l', kt, ct, et, hq⟩
          obtain ⟨j, l', kj, cj, ej, wj⟩ := H (by rw [e2]; exact hu)
          obtain ⟨j', l'', a, c, d, e⟩ := S1 j l' kj ej (by rw [wj]; exact hu) cj
          exact ⟨j', l'', a, c, d, by rw [e, wj]⟩
    · cases hc

end NanoMain

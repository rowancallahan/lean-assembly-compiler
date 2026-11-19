/- Nano/V2Self/Proof/MainBridge6: the Sem ⇐ sv bridge — two word operands (shared by BIN / IF), branch joins, IF. -/
import Nano.V2Self.Proof.MainBridge5

namespace NanoMain
open Templates

/-- two word operands (`OwnSpec.two`) evaluated by `pairS 1 (sv a) (sv b)` -/
theorem operands2 {cx : Ctx} {K : SC} {oc : OwnSpec.Cx} {D : List Sig} {a b : ParSpec.Nd}
    (iha : NodeOK cx K oc D a) (ihb : NodeOK cx K oc D b) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2)
    {Γ : List (Option Kd)} {F : List Bool} {env : List W} {ew : Env} {σ : AH} {sp : Nat} {H : Hp}
    (ta : TyN D Γ none a [.w]) (tb : TyN D Γ none b [.w]) {a0 b0 y : List Bool × List Nat}
    (hca : OwnSpec.chk oc a F = some a0) (hcb : OwnSpec.chk oc b a0.1 = some b0) (hy : OwnSpec.two a0 b0 = some y)
    (hE : EnvI σ oc.K F Γ env ew) (hA : AHeap K.hb K.κ H σ) (h8 : H.top % 8 = 0) (hhb : K.hb ≤ H.top)
    {u : List UInt64} {H2 : Hp} (hs : pairS 1 (sv K a) (sv K b) ew sp H = some (u, H2)) :
    ∃ σ2 x1 x2, ev cx a env = .ok (.inl [.w x1]) ∧ ev cx b env = .ok (.inl [.w x2]) ∧ u = [x1, x2] ∧
      AHeap K.hb K.κ H2 σ2 ∧ EnvI σ2 oc.K y.1 Γ env ew ∧ Ch σ σ2 Γ F y.1 env ew ∧ Mono F y.1 ∧
      H2.top % 8 = 0 ∧ K.hb ≤ H2.top := by
  simp only [pairS, Option.bind_eq_some_iff] at hs
  obtain ⟨⟨ua, H1⟩, hsa, ⟨ub, H2'⟩, hsb, hpe⟩ := hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hpe; obtain ⟨rfl, rfl⟩ := hpe
  obtain ⟨σ1, v1, eva, hA1, hR1, hE1, hCh1, hM1, h81, hb1, -⟩ := iha hC hK2 Γ _ F _ _ env ew σ sp H ua H1 ta hca hE hA h8 hhb hsa
  obtain ⟨σ2, v2, evb, hA2, hR2, hE2, hCh2, hM2, h82, hb2, -⟩ :=
    ihb hC hK2 Γ _ _ _ _ env ew σ1 _ H1 ub H2' tb hcb hE1 hA1 h81 hb1 hsb
  obtain ⟨y1, hlen, wa, wb⟩ := two_spec hy
  obtain ⟨-, ka, -⟩ := ev_ok hC ta env hE.ty
  obtain ⟨-, kb, -⟩ := ev_ok hC tb env hE.ty
  obtain ⟨x1, rfl⟩ := kw1 (ka v1 eva)
  obtain ⟨x2, rfl⟩ := kw1 (kb v2 evb)
  have la : a0.2.length = 1 := by rw [hR1.len.1]; rfl
  have lb : b0.2.length = 1 := by rw [hR2.len.1]; rfl
  obtain ⟨ea, hea⟩ : ∃ ea, a0.2 = [ea] := List.length_eq_one_iff.1 la
  obtain ⟨eb, heb⟩ : ∃ eb, b0.2 = [eb] := List.length_eq_one_iff.1 lb
  rw [hea] at hR1 wa; rw [heb] at hR2 wb
  obtain ⟨z1, hz1, rfl⟩ := word_of hR1 hE1 (wa ea (by simp))
  obtain ⟨z2, hz2, rfl⟩ := word_of hR2 hE2 (wb eb (by simp))
  cases hz1; cases hz2
  rw [y1]
  exact ⟨σ2, x1, x2, eva, evb, rfl, hA2, hE2, Ch.trans hCh1 hCh2 hM1 hM2, hM1.trans hM2, h82, hb2⟩

/-! ## branch joins -/

theorem dead_orF (a b : List Bool) (s : Nat) :
    OwnSpec.dead (OwnSpec.orF a b) s = (OwnSpec.dead a s || OwnSpec.dead b s) := by
  simp only [OwnSpec.dead, OwnSpec.orF, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases ha : a[s]? <;> cases hb : b[s]? <;> simp

theorem mono_orF_l (a b : List Bool) : Mono a (OwnSpec.orF a b) := fun s h => by rw [dead_orF, h]; rfl
theorem mono_orF_r (a b : List Bool) : Mono b (OwnSpec.orF a b) := fun s h => by rw [dead_orF, h]; simp

theorem Ch.weak {σ σ' : AH} {Γ : List (Option Kd)} {F F1 F2 : List Bool} {env : List W} {ew : Env}
    (h : Ch σ σ' Γ F F1 env ew) (m : Mono F1 F2) : Ch σ σ' Γ F F2 env ew :=
  fun a ha hn => h a ha fun s l hk hc hl => hn s l hk ⟨hc.1, m s hc.2⟩ hl

theorem ownFree_max {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {u : UInt64} : ∀ {t e : List Nat} {v : List W} {vs : List UInt64}, ResI σ Kk F Γ env ew t v vs →
      (∀ x ∈ t, x ≤ 1) → (∀ x ∈ e, x ≤ 1) → OwnFree t v vs u → OwnFree (List.zipWith max t e) v vs u
  | [], _, _, _, _, _, _, _ => by simp [OwnFree]
  | _ :: _, [], _, _, _, _, _, _ => by simp [OwnFree]
  | ti :: t, ei :: e, x :: v, u' :: vs, ⟨_, c2, _, _, cR⟩, h1, h2, ⟨o1, oT⟩ => by
    have ht := h1 ti (by simp); have he := h2 ei (by simp)
    simp only [List.zipWith_cons_cons]
    refine ⟨fun hk l hl => ?_, ownFree_max cR (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) oT⟩
    rcases Nat.lt_or_ge ti 1 with h0 | h0
    · obtain ⟨y, rfl⟩ := c2 (by omega); cases hl
    · exact o1 (by omega) l hl
  | _ :: _, _ :: _, [], _, h, _, _, _ | _ :: _, _ :: _, _ :: _, [], h, _, _, _ => by simp [ResI] at h

/-- joining a branch's entries with the other branch's (max): the result invariant survives (entries ≤ 1) -/
theorem resI_max {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env} :
    ∀ {t e : List Nat} {v : List W} {vs : List UInt64}, ResI σ Kk F Γ env ew t v vs → (∀ x ∈ t, x ≤ 1) →
      (∀ x ∈ e, x ≤ 1) → t.length = e.length → ResI σ Kk F Γ env ew (List.zipWith max t e) v vs
  | [], [], [], [], _, _, _, _ => trivial
  | ti :: t, ei :: e, x :: v, u :: vs, ⟨c1, c2, c3, c4, cR⟩, h1, h2, hl => by
    have ht := h1 ti (by simp); have he := h2 ei (by simp)
    simp only [List.zipWith_cons_cons]
    refine ⟨fun _ => c1 (by omega), fun h0 => c2 (by omega), fun hk l hl' => ?_, fun h4 => absurd h4 (by omega),
      resI_max cR (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) (by simpa using hl)⟩
    rcases Nat.lt_or_ge ti 1 with h0 | h0
    · obtain ⟨y, rfl⟩ := c2 (by omega); cases hl'
    · obtain ⟨n1, n2⟩ := c3 (by omega) l hl'
      exact ⟨n1, ownFree_max cR (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) n2⟩
  | [], _ :: _, _, _, _, _, _, hl | _ :: _, [], _, _, _, _, _, hl => by simp at hl
  | [], [], _ :: _, _, h, _, _, _ | [], [], [], _ :: _, h, _, _, _ | _ :: _, _ :: _, [], _, h, _, _, _
  | _ :: _, _ :: _, _ :: _, [], h, _, _, _ => by simp [ResI] at h

theorem max_le1 : ∀ (t e : List Nat), (∀ x ∈ t, x ≤ 1) → (∀ x ∈ e, x ≤ 1) → ∀ x ∈ List.zipWith max t e, x ≤ 1
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: t, b :: e, h1, h2 => by
    intro x hx
    simp only [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := h1 a (by simp); have := h2 b (by simp); omega
    · exact max_le1 t e (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) x hx

theorem resI_join {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {t e k : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew t v vs) (h1 : ∀ x ∈ t, x ≤ 1)
    (h2 : ∀ x ∈ e, x ≤ 1) (hl : t.length = e.length) (hj : OwnSpec.join t e = some k) :
    ResI σ Kk F Γ env ew k v vs ∧ ∀ x ∈ k, x ≤ 1 := by
  unfold OwnSpec.join at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst_vars; simp at hl
    rw [List.length_eq_zero_iff.1 hl.symm]; exact ⟨by simpa using hR, by simp⟩
  · split at hj
    · simp only [Option.some.injEq] at hj; subst_vars; exact ⟨hR, h1⟩
    · simp only [Option.some.injEq] at hj; subst hj
      exact ⟨resI_max hR h1 h2 hl, max_le1 _ _ h1 h2⟩

theorem resI_join_r {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {t e k : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew e v vs) (h1 : ∀ x ∈ t, x ≤ 1)
    (h2 : ∀ x ∈ e, x ≤ 1) (hl : t.length = e.length) (hj : OwnSpec.join t e = some k) :
    ResI σ Kk F Γ env ew k v vs ∧ ∀ x ∈ k, x ≤ 1 := by
  have hj' : OwnSpec.join e t = some k := by
    unfold OwnSpec.join at hj ⊢
    by_cases ht : t = [] <;> by_cases he : e = [] <;> simp_all
    rw [← hj, List.zipWith_comm_of_comm (fun a b => Nat.max_comm a b)]
  exact resI_join hR h2 h1 hl.symm hj'

theorem tr_le1 : ∀ (F : List Bool) (es : List Nat) (F1 : List Bool) (es1 : List Nat),
    OwnSpec.tr F es = some (F1, es1) → ∀ x ∈ es1, x ≤ 1
  | F, [], F1, es1, h => by simp only [OwnSpec.tr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  | F, e :: r, F1, es1, h => by
    simp only [OwnSpec.tr] at h
    split at h
    · split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨⟨a, b⟩, h', he⟩ := h; simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he; intro x hx; simp at hx; rcases hx with rfl | hx; omega; exact tr_le1 _ _ _ _ h' x hx
      · cases h
    · split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨⟨a, b⟩, h', he⟩ := h; simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he; intro x hx; simp at hx; rcases hx with rfl | hx; omega; exact tr_le1 _ _ _ _ h' x hx
      · split at h
        · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h; obtain ⟨F2, -, ⟨a, b⟩, h', he⟩ := h
          simp only [Prod.mk.injEq] at he
          obtain ⟨-, rfl⟩ := he; intro x hx; simp at hx; rcases hx with rfl | hx; omega; exact tr_le1 _ _ _ _ h' x hx
        · cases h

theorem tr_src {σ : AH} {Kk : List Nat} {Γ : List (Option Kd)} {env : List W} {ew : Env} {F0 : List Bool} :
    ∀ (es : List Nat) (v : List W) (vs : List UInt64) (F F1 : List Bool) (es1 : List Nat) {σr : AH} {Fr : List Bool},
    ResI σr Kk Fr Γ env ew es v vs → Mono F0 F → Src σ Γ F0 F env ew es v vs → OwnSpec.tr F es = some (F1, es1) →
    Mono F F1 ∧ Src σ Γ F0 F1 env ew es1 v vs
  | [], [], [], F, F1, es1, _, _, _, _, _, h => by
    simp only [OwnSpec.tr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨Mono.refl _, trivial⟩
  | e :: es, x :: v, u0 :: vs, F, F1, es1, _, _, hR, m0, ⟨s1, sR⟩, h => by
    obtain ⟨c1, c2, c3, c4, cR⟩ := hR
    simp only [OwnSpec.tr] at h
    split at h
    · split at h
      · obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨m, sT⟩ := tr_src es v vs F F2 es2 cR m0 sR ht
        refine ⟨m, fun h1 l hl hs => ?_, sT⟩
        obtain ⟨j, l', a, b, c, d⟩ := s1 h1 l hl hs; exact ⟨j, l', a, ⟨b.1, m j b.2⟩, c, d⟩
      · cases h
    · split at h
      · obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨m, sT⟩ := tr_src es v vs F F2 es2 cR m0 sR ht
        exact ⟨m, fun h1 => absurd h1 (by omega), sT⟩
      · split at h
        · obtain ⟨Fh, hc, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          obtain ⟨d0, d1, mh, -⟩ := consume_spec hc
          obtain ⟨m, sT⟩ := tr_src es v vs Fh F2 es2 cR (m0.trans mh) (Src.mono mh sR) ht
          obtain ⟨e1, e2, -, hk⟩ := c4 (by omega)
          refine ⟨mh.trans m, fun _ l hl _ => ⟨e / 4 - 1, l, hk, ⟨live_of_mono m0 d0, m _ d1⟩, by rw [e2, hl], e1.symm⟩, sT⟩
        · cases h
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _ | [], [], _ :: _, _, _, _, _, _, h, _, _, _
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _ | _ :: _, _ :: _, [], _, _, _, _, _, h, _, _, _ => by simp [ResI] at h

theorem src_max {σ : AH} {Γ : List (Option Kd)} {F F' : List Bool} {env : List W} {ew : Env} {σr : AH} {Kk : List Nat}
    {Fr : List Bool} : ∀ {t e : List Nat} {v : List W} {vs : List UInt64}, ResI σr Kk Fr Γ env ew t v vs →
    Src σ Γ F F' env ew t v vs → (∀ x ∈ t, x ≤ 1) → (∀ x ∈ e, x ≤ 1) → Src σ Γ F F' env ew (List.zipWith max t e) v vs
  | [], _, _, _, _, _, _, _ => by simp [Src]
  | _ :: _, [], _, _, _, _, _, _ => by simp [Src]
  | _ :: _, _ :: _, [], _, _, _, _, _ => by simp [Src]
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _ => by simp [Src]
  | ti :: t, ei :: e, x :: v, u :: vs, ⟨_, c2, _, _, cR⟩, ⟨s1, sR⟩, h1, h2 => by
    refine ⟨fun hm l hl hs => ?_, src_max cR sR (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz]))⟩
    have := h1 ti (by simp); have := h2 ei (by simp)
    rcases Nat.lt_or_ge ti 1 with h0 | h0
    · obtain ⟨y, rfl⟩ := c2 (by omega); cases hl
    · exact s1 (by omega) l hl hs

theorem src_join {σ : AH} {Γ : List (Option Kd)} {F F' : List Bool} {env : List W} {ew : Env} {σr : AH} {Kk : List Nat}
    {Fr : List Bool} {t e k : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σr Kk Fr Γ env ew t v vs)
    (hS : Src σ Γ F F' env ew t v vs) (h1 : ∀ x ∈ t, x ≤ 1) (h2 : ∀ x ∈ e, x ≤ 1) (hj : OwnSpec.join t e = some k) :
    Src σ Γ F F' env ew k v vs := by
  unfold OwnSpec.join at hj
  split at hj
  · simp only [Option.some.injEq] at hj; subst_vars
    have := hR.len; cases v <;> cases vs <;> simp_all [Src]
  · split at hj
    · simp only [Option.some.injEq] at hj; subst_vars; exact hS
    · split at hj
      · simp only [Option.some.injEq] at hj; subst hj; exact src_max hR hS h1 h2
      · cases hj

theorem src_join_r {σ : AH} {Γ : List (Option Kd)} {F F' : List Bool} {env : List W} {ew : Env} {σr : AH} {Kk : List Nat}
    {Fr : List Bool} {t e k : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σr Kk Fr Γ env ew e v vs)
    (hS : Src σ Γ F F' env ew e v vs) (h1 : ∀ x ∈ t, x ≤ 1) (h2 : ∀ x ∈ e, x ≤ 1) (hj : OwnSpec.join t e = some k) :
    Src σ Γ F F' env ew k v vs := by
  have hj' : OwnSpec.join e t = some k := by
    unfold OwnSpec.join at hj ⊢
    by_cases ht : t = [] <;> by_cases he : e = [] <;> simp_all
    obtain ⟨hl, rfl⟩ := hj
    exact List.zipWith_comm_of_comm (fun a b => Nat.max_comm a b)
  exact src_join hR hS h2 h1 hj'

theorem cmpF_iff (c : Nat) (hc : c = 1 ∨ c = 2) (x y : UInt64) :
    cmpF c x y ↔ (if c = 1 then x = y else x < y) := by
  rcases hc with rfl | rfl <;> simp [cmpF, UInt64.lt_iff_toNat_lt]

theorem node_ite (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (c : Nat)
    (a b t e : ParSpec.Nd) (iha : NodeOK cx K oc D a) (ihb : NodeOK cx K oc D b) (iht : NodeOK cx K oc D t)
    (ihe : NodeOK cx K oc D e) : NodeOK cx K oc D (ParSpec.Nd.ite c a b t e) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hs
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    simp only [Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
    simp only [sv, ifS, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨u, H2⟩, hp, hrest⟩ := hs
    obtain ⟨σ2, x1, x2, eva, evb, rfl, hA2, hE2, hCh2, hM2, h82, hb2⟩ :=
      operands2 iha ihb hC hK2 ta tb hca hcb hy hE hA h8 hhb hp
    have lt := tr_len _ _ _ _ h2
    have le := tr_len _ _ _ _ h4
    have ct := chk_len hRs tt rfl _ _ _ h1
    have ce := chk_len hRs te rfl _ _ _ h3
    have hev : ev cx (ParSpec.Nd.ite c a b t e) env =
        (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
      rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
    simp only at hrest
    by_cases hcmp : cmpF c x1 x2
    · rw [if_pos hcmp] at hrest
      obtain ⟨σ3, v, evt, hA3, hR3, hE3, hCh3, hM3, h83, hb3, hS3⟩ := iht hC hK2 Γ ks _ _ _ env ew σ2 sp H2 vs H' tt h1 hE2 hA2 h82 hb2 hrest
      obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR3 hE3 h2
      obtain ⟨hRk, -⟩ := resI_join hR4 r4 (tr_le1 _ _ _ _ h4) (by omega) hj
      have mo := mono_orF_l t1.1 e1.1
      have sk := src_join hR4 (tr_src _ _ _ _ _ _ hR3 hM3 hS3 h2).2 r4 (tr_le1 _ _ _ _ h4) hj
      exact ⟨σ3, v, by rw [hev, if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)]; exact evt, hA3, ResI.mono mo hRk,
        (hE3.mono m4).mono mo, (Ch.trans hCh2 hCh3 hM2 hM3).weak (m4.trans mo),
        ((hM2.trans hM3).trans m4).trans mo, h83, hb3, Src.pre hCh2 hM2 ((hM3.trans m4).trans mo) (Src.mono mo sk)⟩
    · rw [if_neg hcmp] at hrest
      obtain ⟨σ3, v, evt, hA3, hR3, hE3, hCh3, hM3, h83, hb3, hS3⟩ := ihe hC hK2 Γ ks _ _ _ env ew σ2 sp H2 vs H' te h3 hE2 hA2 h82 hb2 hrest
      obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR3 hE3 h4
      obtain ⟨hRk, -⟩ := resI_join_r hR4 (tr_le1 _ _ _ _ h2) r4 (by omega) hj
      have mo := mono_orF_r t1.1 e1.1
      have sk := src_join_r hR4 (tr_src _ _ _ _ _ _ hR3 hM3 hS3 h4).2 (tr_le1 _ _ _ _ h2) r4 hj
      exact ⟨σ3, v, by rw [hev, if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))]; exact evt, hA3, ResI.mono mo hRk,
        (hE3.mono m4).mono mo, (Ch.trans hCh2 hCh3 hM2 hM3).weak (m4.trans mo),
        ((hM2.trans hM3).trans m4).trans mo, h83, hb3, Src.pre hCh2 hM2 ((hM3.trans m4).trans mo) (Src.mono mo sk)⟩

end NanoMain

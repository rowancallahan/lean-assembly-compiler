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
  obtain ⟨σ1, v1, eva, hA1, hR1, hE1, hCh1, hM1, h81, hb1⟩ := iha hC hK2 Γ _ F _ _ env ew σ sp H ua H1 ta hca hE hA h8 hhb hsa
  obtain ⟨σ2, v2, evb, hA2, hR2, hE2, hCh2, hM2, h82, hb2⟩ :=
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

end NanoMain

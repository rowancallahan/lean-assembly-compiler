/- Nano/V2Self/Proof/Bridge/MainBridge8: the Sem ⇐ sv bridge — argument lists (`lstA` / `svL` / `evL`). -/
import Nano.V2Self.Proof.Bridge.MainBridge7

namespace NanoMain
open Templates

/-- results survive a later step: their blocks are not consumed slots' blocks -/
theorem ResI.ch {σ1 σ2 : AH} {Kk : List Nat} {F1 F2 : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    (hCh : Ch σ1 σ2 Γ F1 F2 env ew) (hE : EnvI σ1 Kk F1 Γ env ew) (m : Mono F1 F2) :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, (∀ x ∈ es, x ≤ 1 ∨ 4 ≤ x) →
    ResI σ1 Kk F1 Γ env ew es v vs → ResI σ2 Kk F2 Γ env ew es v vs
  | [], [], [], _, _ => trivial
  | e :: es, x :: v, u :: vs, hsh, ⟨c1, c2, c3, c4, cR⟩ => by
    refine ⟨fun h4 => ?_, c2, fun h1 l hl => ⟨fun s ls k1 k2 d hs => (c3 h1 l hl).1 s ls k1 k2 (live_of_mono m d) hs,
      (c3 h1 l hl).2⟩, c4, ResI.ch hCh hE m (fun z hz => hsh z (by simp [hz])) cR⟩
    have v1 := c1 h4
    cases x with
    | w y => exact v1
    | b l =>
      have e1 : e = 1 := by
        rcases hsh e (by simp) with h | h
        · rcases Nat.lt_or_ge e 1 with h0 | h0
          · obtain ⟨y, hy⟩ := c2 (by omega); cases hy
          · omega
        · omega
      have hn := (c3 e1 l rfl).1
      show σ2 u.toNat = some l
      rw [hCh u.toNat (by simp only [VR] at v1; rw [v1]; rfl) fun s ls ks cs es hq => ?_]
      · exact v1
      · have k0 : Kk.getD s 0 ≠ 0 := by
          intro k0
          obtain ⟨y, hy, -, wd⟩ := hE.val s ks (.inl k0)
          rw [es] at hy; cases hy; obtain ⟨_, h⟩ := wd k0; cases h
        exact hn s ls ks k0 cs.1 es (UInt64.toNat_inj.1 hq)
  | [], _ :: _, _, _, h | [], [], _ :: _, _, h | _ :: _, [], _, _, h | _ :: _, _ :: _, [], _, h => by simp [ResI] at h

theorem ownFree_append : ∀ {es0 : List Nat} {v0 : List W} {u0 : List UInt64} {es1 : List Nat} {v1 : List W}
    {u1 : List UInt64} {u : UInt64}, es0.length = v0.length → v0.length = u0.length →
    OwnFree es0 v0 u0 u → OwnFree es1 v1 u1 u → OwnFree (es0 ++ es1) (v0 ++ v1) (u0 ++ u1) u
  | [], [], [], _, _, _, _, _, _, _, h => h
  | _ :: _, _ :: _, _ :: _, _, _, _, _, l1, l2, ⟨h, t⟩, h1 => ⟨h, ownFree_append (by simpa using l1) (by simpa using l2) t h1⟩
  | [], _ :: _, _, _, _, _, _, l1, _, _, _ | _ :: _, [], _, _, _, _, _, l1, _, _, _ => by simp at l1
  | [], [], _ :: _, _, _, _, _, _, l2, _, _ | _ :: _, _ :: _, [], _, _, _, _, _, l2, _, _ => by simp at l2

theorem resI_append {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env} :
    ∀ {es0 : List Nat} {v0 : List W} {u0 : List UInt64} {es1 : List Nat} {v1 : List W} {u1 : List UInt64},
    ResI σ Kk F Γ env ew es0 v0 u0 → ResI σ Kk F Γ env ew es1 v1 u1 →
    (∀ (i : Nat) (l : List UInt64) (u : UInt64), es0[i]? = some 1 → v0[i]? = some (W.b l) → u0[i]? = some u → OwnFree es1 v1 u1 u) →
    ResI σ Kk F Γ env ew (es0 ++ es1) (v0 ++ v1) (u0 ++ u1)
  | [], [], [], _, _, _, _, h1, _ => h1
  | e :: es0, x :: v0, u :: u0, _, _, _, ⟨c1, c2, c3, c4, cR⟩, h1, hx => by
    have ln := cR.len
    refine ⟨c1, c2, fun e1 l hl => ⟨(c3 e1 l hl).1, ownFree_append ln.1 ln.2 (c3 e1 l hl).2 (hx 0 l u (by simp [e1])
      (by simp [hl]) rfl)⟩, c4, resI_append cR h1 fun i l u' a b c => hx (i + 1) l u' a b c⟩
  | [], _ :: _, _, _, _, _, h, _, _ | [], [], _ :: _, _, _, _, h, _, _ | _ :: _, [], _, _, _, _, h, _, _
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [ResI] at h

theorem src_append {σ : AH} {Γ : List (Option Kd)} {F F' : List Bool} {env : List W} {ew : Env} :
    ∀ {es0 : List Nat} {v0 : List W} {u0 : List UInt64} {es1 : List Nat} {v1 : List W} {u1 : List UInt64},
    es0.length = v0.length → v0.length = u0.length →
    Src σ Γ F F' env ew es0 v0 u0 → Src σ Γ F F' env ew es1 v1 u1 → Src σ Γ F F' env ew (es0 ++ es1) (v0 ++ v1) (u0 ++ u1)
  | [], [], [], _, _, _, _, _, _, h => h
  | _ :: _, _ :: _, _ :: _, _, _, _, l1, l2, ⟨h, t⟩, h1 => ⟨h, src_append (by simpa using l1) (by simpa using l2) t h1⟩
  | [], _ :: _, _, _, _, _, l1, _, _, _ | _ :: _, [], _, _, _, _, l1, _, _, _ => by simp at l1
  | [], [], _ :: _, _, _, _, _, l2, _, _ | _ :: _, _ :: _, [], _, _, _, _, l2, _, _ => by simp at l2

/-- a later owned result is not an earlier owned block: fresh, or a consumed slot's block -/
theorem ownFree_of_src {σ : AH} {Kk : List Nat} {F F' : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    (hE : EnvI σ Kk F Γ env ew) {u : UInt64} {l0 : List UInt64} (hu : σ u.toNat = some l0)
    (hn : ∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ u) :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, Src σ Γ F F' env ew es v vs → OwnFree es v vs u
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ => by simp [OwnFree]
  | _ :: _, _ :: _, u' :: _, ⟨h, t⟩ => ⟨fun e1 l hl q => by
      subst q
      obtain ⟨j, l', kj, cj, ej, wj⟩ := h e1 l hl (by rw [hu]; rfl)
      have k0 : Kk.getD j 0 ≠ 0 := by
        intro k0
        obtain ⟨y, hy, -, wd⟩ := hE.val j kj (.inl k0)
        rw [ej] at hy; cases hy; obtain ⟨_, h⟩ := wd k0; cases h
      exact hn j l' kj k0 cj.1 ej wj, ownFree_of_src hE hu hn t⟩

theorem okAll_idx {ds : Option (List Nat)} {F : List Bool} : ∀ {o : Nat} {es : List Nat}, OwnSpec.okAll ds F o es = true →
    ∀ i e, es[i]? = some e → OwnSpec.ok1 F e (OwnSpec.dest ds (o + i)) = true
  | _, [], _, i, e, h => by simp at h
  | o, x :: r, h, 0, e, he => by
    simp only [OwnSpec.okAll, Bool.and_eq_true] at h; simp at he; subst he; simpa using h.1
  | o, x :: r, h, i + 1, e, he => by
    simp only [OwnSpec.okAll, Bool.and_eq_true] at h; simp at he
    have := okAll_idx h.2 i e he; rwa [show o + 1 + i = o + (i + 1) by omega] at this

/-- **argument lists**: the list analogue of `NodeOK`, with the destination checks each entry passed -/
theorem lst_ok (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2)
    (hW : RsW oc) :
    ∀ (cs : List ParSpec.Nd), (∀ n ∈ cs, NodeOK cx K oc D n) →
    ∀ {Γ ks ds F F1 es0 esA env ew σ sp H vs H'}, TyL D Γ cs ks → OwnSpec.lstA oc cs ds F es0 = some (F1, esA) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → R2 oc.K F →
    svL K cs ew sp H = some (vs, H') →
    ∃ σ' v esN, esA = es0 ++ esN ∧ evL cx cs env = .ok v ∧ AHeap K.hb K.κ H' σ' ∧ ResI σ' oc.K F1 Γ env ew esN v vs ∧
      EnvI σ' oc.K F1 Γ env ew ∧ Ch σ σ' Γ F F1 env ew ∧ Mono F F1 ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top ∧
      Src σ Γ F F1 env ew esN v vs ∧ (∀ x ∈ esN, x ≤ 1 ∨ 4 ≤ x) ∧ Grow σ σ' ∧
      ∀ i e, esN[i]? = some e → ∃ G, OwnSpec.ok1 G e (OwnSpec.dest ds (es0.length + i)) = true
  | [], _, Γ, ks, ds, F, F1, es0, esA, env, ew, σ, sp, H, vs, H', _, hl, hE, hA, h8, hb, _, hs => by
    simp only [OwnSpec.lstA, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    simp only [svL, nilS, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨σ, [], [], by simp, rfl, hA, trivial, hE, Ch.refl _ _ _ _ _, Mono.refl _, h8, hb, trivial, by simp, Grow.refl _, by simp⟩
  | n :: r, hN, Γ, ks, ds, F, F1, es0, esA, env, ew, σ, sp, H, vs, H', hT, hl, hE, hA, h8, hb, hr, hs => by
    cases hT with
    | cons tn tr =>
      simp only [OwnSpec.lstA, Option.bind_eq_some_iff] at hl
      obtain ⟨x, hcn, hl⟩ := hl
      split at hl
      · rename_i hok
        simp only [svL, pairS, Option.bind_eq_some_iff] at hs
        obtain ⟨⟨u1, H1⟩, hs1, ⟨u2, H2⟩, hs2, he⟩ := hs
        simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨σ1, v1, evn, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, hsh1, hG1⟩ :=
          hN n (by simp) hC hK2 Γ _ F _ _ env ew σ sp H u1 H1 tn hcn hE hA h8 hb hr hs1
        obtain ⟨σ2, v2, esR, hesA, evr, hA2, hR2, hE2, hCh2, hM2, h82, hb2, hS2, hsh2, hG2, hok2⟩ :=
          lst_ok cx K oc D hC hK2 hW r (fun m hm => hN m (by simp [hm])) tr hl hE1 hA1 h81 hb1
            (hr.keep (chk_keep hK2 hW tn rfl _ _ _ hcn).1) hs2
        have ln1 := hR1.len
        refine ⟨σ2, v1 ++ v2, x.2 ++ esR, by rw [hesA, List.append_assoc], ?_, hA2, ?_, hE2,
          Ch.trans hCh1 hCh2 hM1 hM2, hM1.trans hM2, h82, hb2, ?_, ?_, hG1.trans hG2, ?_⟩
        · simp [evL, evn, evr, val, bind, Except.bind, pure, Except.pure]
        · refine resI_append (ResI.ch hCh2 hE1 hM2 hsh1 hR1) hR2 fun i l u a b c => ?_
          obtain ⟨c1, -, c3⟩ := resI_idx i hR1 a b c
          exact ownFree_of_src hE1 (c1 (by omega)) (c3 rfl l rfl) hS2
        · exact src_append ln1.1 ln1.2 (Src.mono hM2 hS1) (Src.pre hCh1 hM1 hM2 hS2)
        · intro z hz; rcases List.mem_append.1 hz with hz | hz; exact hsh1 z hz; exact hsh2 z hz
        · intro i e he
          rcases Nat.lt_or_ge i x.2.length with hi | hi
          · rw [List.getElem?_append_left hi] at he; exact ⟨_, okAll_idx hok i e he⟩
          · rw [List.getElem?_append_right hi] at he
            obtain ⟨G, hG⟩ := hok2 _ e he
            refine ⟨G, ?_⟩; rwa [List.length_append, Nat.add_assoc, Nat.add_sub_cancel' hi] at hG
      · cases hl

/-! ## PAIR: `fin none` is the transfer `tr` -/

theorem ok1_one {G : List Bool} {e : Nat} (h : OwnSpec.ok1 G e 1 = true) : (e < 4 → e ≤ 1) ∧ (4 ≤ e → e % 4 ≤ 1) := by
  unfold OwnSpec.ok1 at h
  split at h
  · simp at h; omega
  · split at h
    · omega
    · split at h
      · omega
      · split at h <;> simp at h

theorem finB_none (F : List Bool) : ∀ (o : Nat) (es : List Nat), OwnSpec.finB none F o es = true
  | _, [] => rfl
  | o, e :: r => by simp [OwnSpec.finB, OwnSpec.dest, finB_none F (o + 1) r]

theorem tr_finC : ∀ (es : List Nat) (F : List Bool) (o : Nat), (∀ e ∈ es, (e < 4 → e ≤ 1) ∧ (4 ≤ e → e % 4 ≤ 1)) →
    OwnSpec.tr F es = (OwnSpec.finC none F o es).map fun F2 => (F2, OwnSpec.strip es)
  | [], F, o, _ => rfl
  | e :: r, F, o, h => by
    have ih := fun F => tr_finC r F (o + 1) fun z hz => h z (by simp [hz])
    have he := h e (by simp)
    simp only [OwnSpec.tr, OwnSpec.finC, OwnSpec.strip, List.map_cons, OwnSpec.own, OwnSpec.dest]
    by_cases h4 : e < 4
    · rw [if_pos h4, if_pos (he.1 h4), ih]
      simp only [show (4 ≤ e) = False by simp; omega, decide_false, Bool.false_and, if_false, Option.map_map]
      rw [if_pos h4]; rfl
    · rw [if_neg h4]
      by_cases h0 : e % 4 = 0
      · rw [if_pos h0, ih]
        simp only [h0, Option.map_map, show ((0 : Nat) == 1) = false from rfl, Bool.and_false, if_false]
        rw [if_neg h4]; rfl
      · have h1 : e % 4 = 1 := by have := he.2 (by omega); omega
        rw [if_neg h0, if_pos h1]
        simp only [h1, show 4 ≤ e by omega, decide_true, Bool.true_and, beq_self_eq_true, if_true]
        cases hc : OwnSpec.consume1 F (e / 4 - 1) with
        | none => rfl
        | some F1 => simp only [Option.bind_some, ih, Option.map_map]; rw [if_neg h4]; rfl

theorem fin_none_tr {F F2 : List Bool} {es es2 : List Nat} (h : ∀ e ∈ es, (e < 4 → e ≤ 1) ∧ (4 ≤ e → e % 4 ≤ 1))
    (hf : OwnSpec.fin none F es = some (F2, es2)) : OwnSpec.tr F es = some (F2, es2) := by
  simp only [OwnSpec.fin, if_true, Option.bind_eq_some_iff, finB_none] at hf
  obtain ⟨F3, h3, he⟩ := hf
  simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  rw [tr_finC es F 0 h, h3]; rfl

theorem node_pair (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (cs : List ParSpec.Nd)
    (hN : ∀ n ∈ cs, NodeOK cx K oc D n) : NodeOK cx K oc D (ParSpec.Nd.pair cs) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | pair tl =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨x, hl, hf⟩ := hc
    simp only [sv] at hs
    obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hG1, hok⟩ :=
      lst_ok cx K oc D hC hK2 hW cs hN tl hl hE hA h8 hhb hr hs
    simp only [List.nil_append] at hesA
    have hsh : ∀ e ∈ x.2, (e < 4 → e ≤ 1) ∧ (4 ≤ e → e % 4 ≤ 1) := by
      intro e he
      obtain ⟨i, hi⟩ := List.getElem?_of_mem he
      rw [hesA] at hi
      obtain ⟨G, hG⟩ := hok i e hi
      exact ok1_one (by simpa [OwnSpec.dest] using hG)
    have ht := fin_none_tr hsh hf
    rw [hesA] at ht
    obtain ⟨m2, hR2, r2, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR1 hE1 ht
    obtain ⟨-, hS2⟩ := tr_src _ _ _ _ _ _ hR1 hM1 hS1 ht
    have hev : ev cx (ParSpec.Nd.pair cs) env = .ok (.inl v) := by
      simp [ev, evl, bind, Except.bind, pure, Except.pure]
    exact ⟨σ1, v, hev, hA1, hR2, hE1.mono m2, hCh1.weak m2, hM1.trans m2, h81, hb1, hS2, fun z hz => .inl (r2 z hz), hG1⟩

end NanoMain

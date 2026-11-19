/- Nano/V2Self/Proof/MainBridge4: the Sem ⇐ sv bridge, layer 4 — the node cases.  `NodeOK` = the value-mode claim
for one node: E's `sv` succeeding implies `ev` succeeding with related results, invariants kept. -/
import Nano.V2Self.Proof.MainKeep

namespace NanoMain
open Templates

/-- **source of owned results**: an owned result whose block already existed in `σ` is the block of a slot consumed
between `F` and `F'` (so a LET that binds it and later consumes it changes only blocks its own scope accounts for) -/
def Src (σ : AH) (Γ : List (Option Kd)) (F F' : List Bool) (env : List W) (ew : Env) :
    List Nat → List W → List UInt64 → Prop
  | e :: es, x :: v, u :: vs => (e = 1 → ∀ l, x = .b l → (σ u.toNat).isSome →
      ∃ j l', Kn Γ j ∧ Cons F F' j ∧ env[j]? = some (.b l') ∧ ew j = u) ∧ Src σ Γ F F' env ew es v vs
  | _, _, _ => True

theorem src_ne1 {σ Γ F F' env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64}, (∀ e ∈ es, e ≠ 1) →
    Src σ Γ F F' env ew es v vs
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ => by simp [Src]
  | e :: es, _ :: _, _ :: _, h => ⟨fun h1 => absurd h1 (h e (by simp)), src_ne1 fun z hz => h z (by simp [hz])⟩

theorem Src.mono {σ Γ F F1 F2 env ew} (m : Mono F1 F2) : ∀ {es : List Nat} {v : List W} {vs : List UInt64},
    Src σ Γ F F1 env ew es v vs → Src σ Γ F F2 env ew es v vs
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ => by simp [Src]
  | _ :: _, _ :: _, _ :: _, ⟨h, t⟩ => ⟨fun h1 l hl hs => by
      obtain ⟨j, l', a, b, c, d⟩ := h h1 l hl hs; exact ⟨j, l', a, ⟨b.1, m j b.2⟩, c, d⟩, Src.mono m t⟩

/-- move the start of a `Src` back over a step that changed `σ` only at consumed slots -/
theorem Src.pre {σ σ2 Γ F F2 F' env ew} (hCh : Ch σ σ2 Γ F F2 env ew) (m1 : Mono F F2) (m2 : Mono F2 F') :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, Src σ2 Γ F2 F' env ew es v vs → Src σ Γ F F' env ew es v vs
  | [], _, _, _ | _ :: _, [], _, _ | _ :: _, _ :: _, [], _ => by simp [Src]
  | _ :: _, _ :: _, u :: _, ⟨h, t⟩ => ⟨fun h1 l hl hs => by
      by_cases hx : ∃ j l', Kn Γ j ∧ Cons F F2 j ∧ env[j]? = some (.b l') ∧ (ew j).toNat = u.toNat
      · obtain ⟨j, l', a, b, c, d⟩ := hx; exact ⟨j, l', a, ⟨b.1, m2 j b.2⟩, c, UInt64.toNat_inj.1 d⟩
      · have e2 := hCh _ hs fun s l' hk hc hl' hq => hx ⟨s, l', hk, hc, hl', hq⟩
        obtain ⟨j, l', a, b, c, d⟩ := h h1 l hl (by rw [e2]; exact hs)
        exact ⟨j, l', a, ⟨live_of_mono m1 b.1, b.2⟩, c, d⟩, Src.pre hCh m1 m2 t⟩

/-- the value-mode claim for node `e` in a frame (`Kk` = O's slot kinds, `oc` = O's def context) -/
def NodeOK (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ sp H vs H', TyN D Γ none e ks → OwnSpec.chk oc e F = some (F', es) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → R2 oc.K F →
    sv K e ew sp H = some (vs, H') →
    ∃ σ' v, ev cx e env = .ok (.inl v) ∧ AHeap K.hb K.κ H' σ' ∧ ResI σ' oc.K F' Γ env ew es v vs ∧
      EnvI σ' oc.K F' Γ env ew ∧ Ch σ σ' Γ F F' env ew ∧ Mono F F' ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top ∧
      Src σ Γ F F' env ew es v vs ∧ ∀ x ∈ es, x ≤ 1 ∨ 4 ≤ x

theorem node_const (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) : NodeOK cx K oc D (ParSpec.Nd.const c) := by
  intro _ _ Γ ks F F' es env ew σ sp H vs H' _ hc hE hA h8 hb _ hs
  simp only [OwnSpec.chk, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := leafS_some hs
  exact ⟨σ, [.w c], rfl, hA, by simp [ResI, VR], hE, Ch.refl _ _ _ _ _, Mono.refl _, h8, hb, by simp [Src], by simp⟩

theorem locE_succ (Kk : List Nat) (s w : Nat) :
    OwnSpec.locE Kk s (w + 1) = (Kk.getD s 0 + 4 * (s + 1)) :: OwnSpec.locE Kk (s + 1) w := by
  simp only [OwnSpec.locE, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1; apply List.map_congr_left; intro j _; simp only [Function.comp]
  rw [show s + 1 + j = s + (j + 1) by omega]

theorem resI_loc {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    (hK2 : ∀ s, Kk.getD s 0 ≤ 2) : ∀ (w s : Nat), s + w ≤ env.length → (∀ j, s ≤ j → j < s + w → Kn Γ j) →
    ResI σ Kk F Γ env ew (OwnSpec.locE Kk s w) ((env.drop s).take w) ((List.range w).map fun j => ew (s + j))
  | 0, s, _, _ => by simp [OwnSpec.locE, ResI]
  | w + 1, s, hl, hk => by
    rw [locE_succ, List.range_succ_eq_map]
    have hd : (env.drop s).take (w + 1) = env[s]'(by omega) :: (env.drop (s + 1)).take w := by
      rw [List.drop_eq_getElem_cons (show s < env.length by omega), List.take_succ_cons]
    rw [hd]
    simp only [List.map_cons, List.map_map]
    have := hK2 s
    have e1 : (Kk.getD s 0 + 4 * (s + 1)) / 4 - 1 = s := by omega
    refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ?_, ?_⟩
    · rw [e1]; refine ⟨by simp, by simp [List.getElem?_eq_getElem (show s < env.length by omega)], by omega,
        hk s (Nat.le_refl _) (by omega)⟩
    · have := resI_loc (σ := σ) (F := F) (env := env) (ew := ew) hK2 w (s + 1) (by omega)
        (fun j h1 h2 => hk j (by omega) (by omega))
      simpa [Function.comp, Nat.add_assoc, Nat.add_comm 1] using this

theorem node_loc (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) :
    NodeOK cx K oc D (ParSpec.Nd.loc s w) := by
  intro _ hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hb _ hs
  simp only [OwnSpec.chk] at hc; split at hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
    simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := localS_some w s hs
    cases hT with
    | loc hk =>
      have hk1 := hk.1
      have hl := hE.len
      have he : ev cx (ParSpec.Nd.loc s w) env = .ok (.inl ((env.drop s).take w)) := by simp [ev, hl, hk1]
      exact ⟨σ, _, he, hA, resI_loc hK2 w s (by omega) (fun j h1 h2 => known_get hk j h1 h2), hE,
        Ch.refl _ _ _ _ _, Mono.refl _, h8, hb, src_ne1 fun z hz => by
          simp only [OwnSpec.locE, List.mem_map] at hz; obtain ⟨j, -, rfl⟩ := hz; omega, fun z hz => by
          simp only [OwnSpec.locE, List.mem_map] at hz; obtain ⟨j, -, rfl⟩ := hz; omega⟩
  · cases hc

/-! ## word operands -/

theorem ok1_word {F : List Bool} {e : Nat} (h : OwnSpec.ok1 F e 0 = true) : e = 0 ∨ (4 ≤ e ∧ e % 4 = 0) := by
  unfold OwnSpec.ok1 at h
  split at h
  · simp at h; omega
  · split at h
    · right; constructor <;> omega
    · split at h <;> (try split at h) <;> simp at h

theorem finC_nocons (F : List Bool) : ∀ (o : Nat) (es : List Nat), (∀ k, o ≤ k → OwnSpec.dest (some [0, 0]) k ≠ 1) →
    OwnSpec.finC (some [0, 0]) F o es = some F
  | _, [], _ => rfl
  | o, e :: r, h => by
    simp only [OwnSpec.finC]
    rw [if_neg (by simp only [Bool.and_eq_true, beq_iff_eq, not_and]; intro _; exact h o (Nat.le_refl _))]
    exact finC_nocons F (o + 1) r fun k hk => h k (by omega)

theorem dest00 (k : Nat) : OwnSpec.dest (some [0, 0]) k ≠ 1 := by
  simp only [OwnSpec.dest]; rcases k with _ | _ | k <;> simp

theorem two_spec {a0 b0 y : List Bool × List Nat} (h : OwnSpec.two a0 b0 = some y) :
    y.1 = b0.1 ∧ (a0.2 ++ b0.2).length = 2 ∧ (∀ e ∈ a0.2, e = 0 ∨ (4 ≤ e ∧ e % 4 = 0)) ∧
      (∀ e ∈ b0.2, e = 0 ∨ (4 ≤ e ∧ e % 4 = 0)) := by
  unfold OwnSpec.two at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    have okw : ∀ (F : List Bool) (o : Nat) (es : List Nat), OwnSpec.okAll (some [0, 0]) F o es = true →
        o + es.length ≤ 2 → ∀ e ∈ es, e = 0 ∨ (4 ≤ e ∧ e % 4 = 0) := by
      intro F o es
      induction es generalizing o with
      | nil => simp
      | cons e r ih =>
        intro hh hl x hx
        simp only [OwnSpec.okAll, Bool.and_eq_true] at hh
        rcases List.mem_cons.1 hx with rfl | hx
        · have : OwnSpec.dest (some [0, 0]) o = 0 := by
            simp only [OwnSpec.dest]; rcases o with _ | _ | o <;> simp at hl ⊢; omega
          rw [this] at hh; exact ok1_word hh.1
        · exact ih (o + 1) hh.2 (by simp at hl; omega) x hx
    simp only [OwnSpec.fin, List.length_cons, List.length_nil] at h
    split at h
    · rename_i hlen
      simp only [beq_iff_eq] at hlen
      rw [finC_nocons _ 0 _ fun k _ => dest00 k] at h
      simp only [Option.bind_some] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact ⟨rfl, hlen, okw _ 0 _ hok.1 (by simp at hlen; omega), okw _ _ _ hok.2 (by simp at hlen ⊢; omega)⟩
      · cases h
    · cases h
  · cases h

/-- a one-word operand that the walk accepts at a word destination is a word on both sides -/
theorem word_of {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {e : Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew [e] v vs) (hE : EnvI σ Kk F Γ env ew)
    (he : e = 0 ∨ (4 ≤ e ∧ e % 4 = 0)) : ∃ x, v = [.w x] ∧ vs = [x] := by
  obtain ⟨l1, l2⟩ := hR.len
  obtain ⟨v0, rfl⟩ := List.length_eq_one_iff.1 l1.symm
  obtain ⟨u0, rfl⟩ := List.length_eq_one_iff.1 l2.symm
  · obtain ⟨c1, c2, -, c4, -⟩ := hR
    rcases he with rfl | ⟨h4, h0⟩
    · obtain ⟨x, rfl⟩ := c2 rfl; have := c1 (by omega); simp only [VR] at this; exact ⟨x, rfl, by rw [this]⟩
    · obtain ⟨e1, e2, e3, hk⟩ := c4 h4
      obtain ⟨w0, ew0, vr, wd⟩ := hE.val _ hk (.inl (by omega))
      rw [e2] at ew0; cases ew0
      obtain ⟨x, rfl⟩ := wd (by omega)
      simp only [VR] at vr
      exact ⟨x, rfl, by rw [e1, vr]⟩

theorem binop_aluf (op : Nat) (x y : UInt64) (h1 : 1 ≤ op) (h2 : op ≤ 8) : binop op x y = .ok (CallProbe.aluf op x y) := by
  unfold binop CallProbe.aluf
  rcases op with _ | _ | _ | _ | _ | _ | _ | _ | _ | op <;> simp_all <;> omega

theorem node_bin (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (op : Nat) (a b : ParSpec.Nd)
    (iha : NodeOK cx K oc D a) (ihb : NodeOK cx K oc D b) : NodeOK cx K oc D (ParSpec.Nd.bin op a b) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | bin o1 o2 ta tb =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, he⟩ := hc
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [sv, fin2S, pairS, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨u, Hu⟩, ⟨⟨ua, H1⟩, hsa, ⟨ub, H2⟩, hsb, hpe⟩, hfin⟩ := hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hpe; obtain ⟨rfl, rfl⟩ := hpe
    obtain ⟨σ1, v1, eva, hA1, hR1, hE1, hCh1, hM1, h81, hb1, -, -⟩ := iha hC hK2 Γ _ F _ _ env ew σ sp H ua H1 ta hca hE hA h8 hhb hr hsa
    obtain ⟨σ2, v2, evb, hA2, hR2, hE2, hCh2, hM2, h82, hb2, -, -⟩ :=
      ihb hC hK2 Γ _ _ _ _ env ew σ1 _ H1 ub H2 tb hcb hE1 hA1 h81 hb1 (hr.keep (chk_keep hK2 hW ta rfl _ _ _ hca).1) hsb
    obtain ⟨y1, hlen, wa, wb⟩ := two_spec hy
    obtain ⟨-, ka, -⟩ := ev_ok hC ta env hE.ty
    obtain ⟨-, kb, -⟩ := ev_ok hC tb env hE.ty
    obtain ⟨x1, rfl⟩ := kw1 (ka v1 eva)
    obtain ⟨x2, rfl⟩ := kw1 (kb v2 evb)
    have la : a0.2.length = 1 := by rw [hR1.len.1]; rfl
    have lb : b0.2.length = 1 := by rw [hR2.len.1]; rfl
    obtain ⟨ea, hea⟩ : ∃ ea, a0.2 = [ea] := by
      match h : a0.2, la with | [ea], _ => exact ⟨ea, rfl⟩
    obtain ⟨eb, heb⟩ : ∃ eb, b0.2 = [eb] := by
      match h : b0.2, lb with | [eb], _ => exact ⟨eb, rfl⟩
    rw [hea] at hR1 wa; rw [heb] at hR2 wb
    obtain ⟨z1, hz1, rfl⟩ := word_of hR1 hE1 (wa ea (by simp))
    obtain ⟨z2, hz2, rfl⟩ := word_of hR2 hE2 (wb eb (by simp))
    cases hz1; cases hz2
    simp only [List.cons_append, List.nil_append, Option.map_eq_some_iff, aluF2] at hfin
    obtain ⟨⟨r, Hr⟩, hr, hre⟩ := hfin
    simp only [Option.some.injEq, Prod.mk.injEq] at hr hre; obtain ⟨rfl, rfl⟩ := hr; obtain ⟨rfl, rfl⟩ := hre
    have hev : ev cx (ParSpec.Nd.bin op a b) env = .ok (.inl [.w (CallProbe.aluf op x1 x2)]) := by
      simp [ev, eva, evb, val, binop_aluf op x1 x2 o1 o2, bind, Except.bind, pure, Except.pure]
    rw [y1]
    refine ⟨σ2, _, hev, hA2, ?_, hE2, Ch.trans hCh1 hCh2 hM1 hM2, hM1.trans hM2, h82, hb2, ?_, ?_⟩
    · simp [ResI, VR]
    · simp [Src]
    · simp

end NanoMain

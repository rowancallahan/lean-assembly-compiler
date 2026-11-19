/- Nano/V2Self/Proof/MainBridge4: the Sem ⇐ sv bridge, layer 4 — the node cases.  `NodeOK` = the value-mode claim
for one node: E's `sv` succeeding implies `ev` succeeding with related results, invariants kept. -/
import Nano.V2Self.Proof.MainBridge3
import Nano.V2Self.Proof.MainOk

namespace NanoMain
open Templates

/-- the value-mode claim for node `e` in a frame (`Kk` = O's slot kinds, `oc` = O's def context) -/
def NodeOK (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ sp H vs H', TyN D Γ none e ks → OwnSpec.chk oc e F = some (F', es) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → sv K e ew sp H = some (vs, H') →
    ∃ σ' v, ev cx e env = .ok (.inl v) ∧ AHeap K.hb K.κ H' σ' ∧ ResI σ' oc.K F' Γ env ew es v vs ∧
      EnvI σ' oc.K F' Γ env ew ∧ Ch σ σ' Γ F F' env ew ∧ Mono F F' ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top

theorem node_const (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) : NodeOK cx K oc D (ParSpec.Nd.const c) := by
  intro _ _ Γ ks F F' es env ew σ sp H vs H' _ hc hE hA h8 hb hs
  simp only [OwnSpec.chk, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := leafS_some hs
  refine ⟨σ, [.w c], rfl, hA, ⟨rfl, rfl, fun i h1 h2 h3 => ?_⟩, hE, Ch.refl _ _ _ _ _, Mono.refl _, h8, hb⟩
  simp at h1; subst h1; simp [VR]

theorem node_loc (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) : NodeOK cx K oc D (ParSpec.Nd.loc s w) := by
  intro _ hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hb hs
  simp only [OwnSpec.chk] at hc; split at hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
    simp only [sv] at hs; obtain ⟨rfl, rfl⟩ := localS_some w s hs
    cases hT with
    | loc hk =>
      have hk1 := hk.1
      have hl := hE.len
      have he : ev cx (ParSpec.Nd.loc s w) env = .ok (.inl ((env.drop s).take w)) := by simp [ev, hl, hk1]
      refine ⟨σ, _, he, hA, ⟨by simp [OwnSpec.locE]; omega, by simp; omega, fun i h1 h2 h3 => ?_⟩, hE,
        Ch.refl _ _ _ _ _, Mono.refl _, h8, hb⟩
      simp only [OwnSpec.locE, List.length_map, List.length_range] at h1
      simp only [OwnSpec.locE, List.getElem_map, List.getElem_range]
      refine ⟨fun h => by omega, fun h => by omega, fun h => by omega, fun _ => ?_⟩
      have := hK2 (s + i)
      have e1 : (oc.K.getD (s + i) 0 + 4 * (s + i + 1)) / 4 - 1 = s + i := by omega
      rw [e1]; simp only [List.getElem_take, List.getElem_drop]
      refine ⟨by simp, by rw [List.getElem?_eq_getElem (by omega)], by omega, ?_⟩
      exact known_get hk (s + i) (by omega) (by omega)
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
  obtain ⟨l1, l2, hr⟩ := hR
  match v, vs, l1, l2 with
  | [v0], [u0], _, _ =>
    obtain ⟨c1, c2, -, c4⟩ := hr 0 (by simp) (by simp) (by simp)
    simp only [List.getElem_cons_zero] at c1 c2 c4
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

theorem node_bin (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (op : Nat) (a b : ParSpec.Nd)
    (iha : NodeOK cx K oc D a) (ihb : NodeOK cx K oc D b) : NodeOK cx K oc D (ParSpec.Nd.bin op a b) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hs
  cases hT with
  | bin o1 o2 ta tb =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, he⟩ := hc
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [sv, fin2S, pairS, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨u, Hu⟩, ⟨⟨ua, H1⟩, hsa, ⟨ub, H2⟩, hsb, hpe⟩, hfin⟩ := hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hpe; obtain ⟨rfl, rfl⟩ := hpe
    obtain ⟨σ1, v1, eva, hA1, hR1, hE1, hCh1, hM1, h81, hb1⟩ := iha hC hK2 Γ _ F _ _ env ew σ sp H ua H1 ta hca hE hA h8 hhb hsa
    obtain ⟨σ2, v2, evb, hA2, hR2, hE2, hCh2, hM2, h82, hb2⟩ :=
      ihb hC hK2 Γ _ _ _ _ env ew σ1 _ H1 ub H2 tb hcb hE1 hA1 h81 hb1 hsb
    obtain ⟨y1, hlen, wa, wb⟩ := two_spec hy
    obtain ⟨-, ka, -⟩ := ev_ok hC ta env hE.ty
    obtain ⟨-, kb, -⟩ := ev_ok hC tb env hE.ty
    obtain ⟨x1, rfl⟩ := kw1 (ka v1 eva)
    obtain ⟨x2, rfl⟩ := kw1 (kb v2 evb)
    have la : a0.2.length = 1 := by rw [hR1.1]; rfl
    have lb : b0.2.length = 1 := by rw [hR2.1]; rfl
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
    refine ⟨σ2, _, hev, hA2, ⟨rfl, rfl, fun i h1 h2 h3 => ?_⟩, hE2, Ch.trans hCh1 hCh2 hM1 hM2, hM1.trans hM2, h82, hb2⟩
    simp at h1; subst h1; simp [VR]

end NanoMain

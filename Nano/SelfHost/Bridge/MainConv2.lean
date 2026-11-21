/- Nano/SelfHost/Bridge/MainConv2: the converse bridge, layer 2 — existence: when `Sem` succeeds, E's semantics succeeds
given enough stack room above the heap top.  (The relations then come from `NodeOK`.) -/
import Nano.SelfHost.Bridge.MainConv1

namespace NanoMain
open Templates

/-- `S` succeeds once the room above the heap top is at least some `N` -/
def Ex {α : Type} (S : Nat → Hp → Option α) (H : Hp) : Prop :=
  ∃ N, ∀ sp, H.top + N ≤ sp → sp < 2 ^ 62 → ∃ r, S sp H = some r

/-- sequencing: first `S`, then `T` on its result at `sp − c` -/
theorem ex_seq {α β : Type} {S : Nat → Hp → Option α} {T : α → Nat → Hp → Option β} {H : Hp} (c : Nat)
    (getH : α → Hp) (hS : Ex S H) (hM : Mo S)
    (hT : ∀ sp r1, sp < 2 ^ 62 → S sp H = some r1 → Ex (fun sp' (_ : Hp) => T r1 sp' (getH r1)) (getH r1)) :
    Ex (fun sp H => (S sp H).bind fun r1 => T r1 (sp - c) (getH r1)) H := by
  obtain ⟨Na, ha⟩ := hS
  by_cases h0 : H.top + Na < 2 ^ 62
  · obtain ⟨r1, h1⟩ := ha (H.top + Na) (Nat.le_refl _) h0
    obtain ⟨Nb, hb⟩ := hT _ r1 h0 h1
    refine ⟨Na + ((getH r1).top + Nb + c), fun sp hs hs' => ?_⟩
    have e1 := hM _ sp H r1 h1 (by omega) hs'
    obtain ⟨r2, h2⟩ := hb (sp - c) (by omega) (by omega)
    exact ⟨r2, by simp only [e1, Option.bind_some]; exact h2⟩
  · exact ⟨Na, fun sp hs hs' => absurd (Nat.lt_of_le_of_lt hs hs') h0⟩

theorem ex_of_eq {α : Type} {S S' : Nat → Hp → Option α} {H : Hp} (e : ∀ sp, S sp H = S' sp H) (h : Ex S H) : Ex S' H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by rw [← e]; exact hN sp a b⟩

theorem ex_map {α β : Type} {S : Nat → Hp → Option α} {H : Hp} (f : α → β) (h : Ex S H) :
    Ex (fun sp H => (S sp H).map f) H := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun sp a b => by obtain ⟨r, hr⟩ := hN sp a b; exact ⟨f r, by simp [hr]⟩⟩

theorem ex_const {α : Type} {H : Hp} (x : α) : Ex (fun (_ : Nat) (_ : Hp) => some x) H := ⟨0, fun _ _ _ => ⟨x, rfl⟩⟩

theorem leafS_ex (V : Env → UInt64) (env : Env) (H : Hp) : Ex (leafS V env) H :=
  ⟨8, fun sp a _ => ⟨([V env], H), by simp [leafS, show H.top + 8 ≤ sp by omega]⟩⟩

theorem pairS_ex {wa : Nat} {SA SB : SemW} {env : Env} {H : Hp} (hA : Ex (SA env) H) (hM : Mo (SA env))
    (hB : ∀ sp r1, sp < 2 ^ 62 → SA env sp H = some r1 → Ex (SB env) r1.2) : Ex (pairS wa SA SB env) H := by
  have := ex_seq (T := fun r1 sp' H' => (SB env sp' H').bind fun r2 => some (r1.1 ++ r2.1, r2.2)) (8 * wa) Prod.snd hA hM
    (fun sp r1 h0 h1 => by
      obtain ⟨N, hN⟩ := hB sp r1 h0 h1
      exact ⟨N, fun sp' a b => by obtain ⟨r, hr⟩ := hN sp' a b; exact ⟨(r1.1 ++ r.1, r.2), by simp [hr]⟩⟩)
  exact ex_of_eq (fun sp => rfl) this

theorem localS_ex : ∀ (w k : Nat) (env : Env) (H : Hp), Ex (localS k w env) H
  | 0, k, env, H => ⟨0, fun _ _ _ => ⟨_, rfl⟩⟩
  | w + 1, k, env, H => pairS_ex (leafS_ex _ env H) (leafS_mo _ env) (fun sp r1 _ h1 => by
      unfold leafS at h1; split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact localS_ex w (k + 1) env H
      · cases h1)

/-- the value-mode existence claim -/
def NodeEx (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ H v, TyN D Γ none e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → ev cx e env = .ok (.inl v) → Ex (sv K e ew) H

theorem ex_nconst (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) : NodeEx cx K oc D (.const c) := by
  intro _ _ Γ ks F F' es env ew σ H v _ _ _ _ _ _ _ _
  simp only [sv]; exact leafS_ex _ _ H

theorem ex_loc (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) : NodeEx cx K oc D (.loc s w) := by
  intro _ _ Γ ks F F' es env ew σ H v _ _ _ _ _ _ _ _
  simp only [sv]; exact localS_ex w s ew H

theorem val_ok_of {r : Out} {v : List W} (h : val r = .ok v) : r = .ok (.inl v) := by
  unfold val at h; split at h <;> simp_all

/-- an operand pair evaluates when the whole BIN / IF head does -/
theorem operands_ex {cx : Ctx} {K : SC} {oc : OwnSpec.Cx} {D : List Sig} {a b : ParSpec.Nd}
    (hNa : NodeOK cx K oc D a) (hEa : NodeEx cx K oc D a) (hEb : NodeEx cx K oc D b) (hC : CtxOK cx D)
    (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    {Γ : List (Option Kd)} {F : List Bool} {env : List W} {ew : Env} {σ : AH} {H : Hp}
    (ta : TyN D Γ none a [.w]) (tb : TyN D Γ none b [.w]) {a0 b0 : List Bool × List Nat}
    (hca : OwnSpec.chk oc a F = some a0) (hcb : OwnSpec.chk oc b a0.1 = some b0)
    (hE : EnvI σ oc.K F Γ env ew) (hA : AHeap K.hb K.κ H σ) (h8 : H.top % 8 = 0) (hhb : K.hb ≤ H.top) (hr : R2 oc.K F)
    {va vb : List W} (eva : ev cx a env = .ok (.inl va)) (evb : ev cx b env = .ok (.inl vb)) :
    Ex (pairS 1 (sv K a) (sv K b) ew) H := by
  refine pairS_ex (hEa hC hK2 Γ _ F _ _ env ew σ H va ta hca hE hA h8 hhb hr eva) (sv_mo K hFM a ew)
    fun sp r1 _ h1 => ?_
  obtain ⟨σ1, v1, -, hA1, -, hE1, -, -, h81, hb1, -, -, -⟩ := hNa hC hK2 Γ _ F _ _ env ew σ sp H r1.1 r1.2 ta hca hE hA h8 hhb hr h1
  exact hEb hC hK2 Γ _ _ _ _ env ew σ1 r1.2 vb tb hcb hE1 hA1 h81 hb1
    (hr.keep (chk_keep hK2 hW ta rfl _ _ _ hca).1) evb

theorem ex_bin (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (op : Nat) (a b : ParSpec.Nd) (hNa : NodeOK cx K oc D a) (hNb : NodeOK cx K oc D b) (hEa : NodeEx cx K oc D a)
    (hEb : NodeEx cx K oc D b) : NodeEx cx K oc D (.bin op a b) := by
  intro hC hK2 Γ ks F F' es env ew σ H v hT hc hE hA h8 hhb hr hev
  cases hT with
  | bin o1 o2 ta tb =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, -⟩ := hc
    simp only [ev, bind, Except.bind] at hev
    cases ea : val (ev cx a env) with
    | error e => rw [ea] at hev; cases hev
    | ok va =>
      cases eb : val (ev cx b env) with
      | error e => rw [ea, eb] at hev; cases hev
      | ok vb =>
        have hp := operands_ex hNa hEa hEb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (val_ok_of ea) (val_ok_of eb)
        have := ex_seq (T := fun r1 sp' H' => match r1.1 with
            | [x, y] => (aluF2 op x y (sp' - 16) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd hp
          (pairS_mo (sv_mo K hFM a) (sv_mo K hFM b) ew) (fun sp r1 _ h1 => by
            obtain ⟨σ2, x1, x2, -, -, hu, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy hE hA h8 hhb hr
              (show pairS 1 (sv K a) (sv K b) ew sp H = some (r1.1, r1.2) from h1)
            exact ⟨0, fun sp' _ _ => ⟨([CallProbe.aluf op x1 x2], r1.2), by simp [hu, aluF2]⟩⟩)
        simp only [sv, fin2S]
        exact ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this

theorem ex_ite (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (c : Nat) (a b t e : ParSpec.Nd) (hNa : NodeOK cx K oc D a) (hNb : NodeOK cx K oc D b) (hEa : NodeEx cx K oc D a)
    (hEb : NodeEx cx K oc D b) (hEt : NodeEx cx K oc D t) (hEe : NodeEx cx K oc D e) :
    NodeEx cx K oc D (.ite c a b t e) := by
  intro hC hK2 Γ ks F F' es env ew σ H v hT hc hE hA h8 hhb hr hev
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    have hry : R2 oc.K y.1 := by
      obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ hca
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hcb
      exact hr.keep ((ka.trans kb).trans (two_keep ta' tb' hy))
    have hev0 := hev
    simp only [ev, bind, Except.bind] at hev
    cases ea : val (ev cx a env) with
    | error e' => rw [ea] at hev; cases hev
    | ok va =>
      cases eb : val (ev cx b env) with
      | error e' => rw [ea, eb] at hev; cases hev
      | ok vb =>
        have hp := operands_ex hNa hEa hEb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (val_ok_of ea) (val_ok_of eb)
        have := ex_seq (T := fun r1 sp' H' => match r1.1 with
            | [x, z] => if cmpF c x z then sv K t ew sp' H' else sv K e ew sp' H' | _ => none) 0 Prod.snd hp
          (pairS_mo (sv_mo K hFM a) (sv_mo K hFM b) ew) (fun sp r1 _ hr1 => by
            obtain ⟨σ2, x1, x2, eva, evb, hu, hA2, hE2, -, -, h82, hb2, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy
              hE hA h8 hhb hr (show pairS 1 (sv K a) (sv K b) ew sp H = some (r1.1, r1.2) from hr1)
            have hev' : ev cx (ParSpec.Nd.ite c a b t e) env =
                (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
              rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
            rw [hev'] at hev0
            simp only [hu]
            by_cases hcmp : cmpF c x1 x2
            · rw [if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)] at hev0
              obtain ⟨N, hN⟩ := hEt hC hK2 Γ ks _ _ _ env ew σ2 r1.2 v tt h1 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_true]; exact hN sp' a b⟩
            · rw [if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))] at hev0
              obtain ⟨N, hN⟩ := hEe hC hK2 Γ ks _ _ _ env ew σ2 r1.2 v te h3 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_false]; exact hN sp' a b⟩)
        simp only [sv, ifS]
        exact ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this

theorem ex_let (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (s w : Nat) (v b : ParSpec.Nd) (hNv : NodeOK cx K oc D v) (hEv : NodeEx cx K oc D v) (hEb : NodeEx cx K oc D b) :
    NodeEx cx K oc D (.letE s w v b) := by
  intro hC hK2 Γ ks F F' es env ew σ H vv hT hc hE hA h8 hhb hr hev
  cases hT with
  | letE hv htv hsl hfr hb =>
    rename_i tv
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨v0, hcv, v1, htr, hc⟩ := hc
    split at hc
    · rename_i hcond
      obtain ⟨-, hsK, hv12, -⟩ := hcond
      obtain ⟨b0, hcb, htr2⟩ := Option.bind_eq_some_iff.1 hc
      have hev0 := hev
      simp only [ev, bind, Except.bind] at hev
      cases ea : val (ev cx v env) with
      | error e' => rw [ea] at hev; cases hev
      | ok x0 =>
        have evx := val_ok_of ea
        have := ex_seq (T := fun r1 sp' H' => sv K b (setW ew s w r1.1) sp' H') 0 Prod.snd
          (hEv hC hK2 Γ tv F _ _ env ew σ H x0 hv hcv hE hA h8 hhb hr evx) (sv_mo K hFM v ew) (fun sp r1 _ hs1 => by
            obtain ⟨σ1, x, evv, hA1, hR1, hE1, -, hM1, h81, hb1, -, -, -⟩ :=
              hNv hC hK2 Γ tv F _ _ env ew σ sp H r1.1 r1.2 hv hcv hE hA h8 hhb hr hs1
            rw [evx] at evv
            have hx0 : x0 = x := by simpa using evv
            subst x0
            obtain ⟨m2, hR2, r2, -, -⟩ := tr_spec hK2 _ x r1.1 _ _ _ hR1 hE1 htr
            obtain ⟨-, kv, -⟩ := ev_ok hC hv env hE.ty
            have hk := kv x evx
            have hxl : x.length = w := by rw [← kOf_length, hk, htv]
            have hel := hE.len
            have hss : setSlots env s x = .ok (env.take s ++ x ++ env.drop (s + x.length)) := by
              simp only [setSlots]; rw [if_pos (by omega)]
            obtain ⟨env1, e1, he1⟩ := setSlots_ok (vs := x) (s := s) hE.ty (by omega)
            rw [hss] at e1; cases e1
            rw [hk] at he1
            have hrv : R2 oc.K v1.1 := by
              obtain ⟨kv', tv'⟩ := chk_keep hK2 hW hv rfl _ _ _ hcv
              exact hr.keep (kv'.trans (tr_keep _ _ _ _ tv' htr).1)
            have hEb' := let_envI (r := r1.1) (hE1.mono m2) hR2 hv12 r2 hxl hsK htv hsl hfr he1
            have hle : ev cx (ParSpec.Nd.letE s w v b) env = ev cx b (env.take s ++ x ++ env.drop (s + x.length)) := by
              simp only [ev, evx, val, bind, Except.bind]; rw [if_pos hxl]; simp only [hss]
            rw [hle] at hev0
            exact hEb hC hK2 _ ks _ _ _ _ _ σ1 r1.2 vv hb hcb hEb' hA1 h81 hb1 hrv hev0)
        simp only [sv, letS]
        exact ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this
    · cases hc

/-- argument lists -/
theorem lst_ex (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2)
    (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) :
    ∀ (cs : List ParSpec.Nd), (∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeEx cx K oc D n) →
    ∀ {Γ ks ds F F1 es0 esA env ew σ H v}, TyL D Γ cs ks → OwnSpec.lstA oc cs ds F es0 = some (F1, esA) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → R2 oc.K F →
    evL cx cs env = .ok v → Ex (svL K cs ew) H
  | [], _, _, _, _, _, _, _, _, _, _, _, H, _, _, _, _, _, _, _, _, _ => ⟨0, fun _ _ _ => ⟨([], H), by simp [svL, nilS]⟩⟩
  | n :: r, hN, Γ, ks, ds, F, F1, es0, esA, env, ew, σ, H, v, hT, hl, hE, hA, h8, hb, hr, hev => by
    cases hT with
    | cons tn tr =>
      simp only [OwnSpec.lstA, Option.bind_eq_some_iff] at hl
      obtain ⟨x, hcn, hl⟩ := hl
      split at hl
      · simp only [evL, bind, Except.bind] at hev
        cases en : val (ev cx n env) with
        | error e => rw [en] at hev; cases hev
        | ok vn =>
          cases er : evL cx r env with
          | error e => rw [en, er] at hev; cases hev
          | ok vr =>
            simp only [svL]
            refine pairS_ex ((hN n (by simp)).2 hC hK2 Γ _ F _ _ env ew σ H vn tn hcn hE hA h8 hb hr (val_ok_of en))
              (sv_mo K hFM n ew) fun sp r1 _ h1 => ?_
            obtain ⟨σ1, v1, -, hA1, -, hE1, -, -, h81, hb1, -, -, -⟩ :=
              (hN n (by simp)).1 hC hK2 Γ _ F _ _ env ew σ sp H r1.1 r1.2 tn hcn hE hA h8 hb hr h1
            exact lst_ex cx K oc D hC hK2 hW hFM r (fun m hm => hN m (by simp [hm])) tr hl hE1 hA1 h81 hb1
              (hr.keep (chk_keep hK2 hW tn rfl _ _ _ hcn).1) er
      · cases hl

theorem ex_pair (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (cs : List ParSpec.Nd) (hN : ∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeEx cx K oc D n) : NodeEx cx K oc D (.pair cs) := by
  intro hC hK2 Γ ks F F' es env ew σ H v hT hc hE hA h8 hhb hr hev
  cases hT with
  | pair tl =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, -⟩ := hc
    simp only [ev, bind, Except.bind] at hev
    cases el : evL cx cs env with
    | error e => rw [el] at hev; cases hev
    | ok vl =>
      simp only [sv]
      exact lst_ex cx K oc D hC hK2 hW hFM cs hN tl hl hE hA h8 hhb hr el

end NanoMain

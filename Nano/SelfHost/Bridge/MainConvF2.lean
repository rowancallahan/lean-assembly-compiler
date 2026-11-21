/- Nano/SelfHost/Bridge/MainConvF2: the failure kinds, forward — at ANY stack room, if E's kinded semantics fails, the
failure is `room`, or it is `cap` and `Sem` stops with `cap` there too.  Never `stuck`.  The successful prefix of a run
is the forward bridge (`NodeOK`); the failing step is checked per node. -/
import Nano.SelfHost.Bridge.MainConvX7

namespace NanoMain
open Templates

/-- an E failure is a room failure, or a capacity stop matching `Sem`'s -/
def FailOK {α : Type} (f : Fail) (r : Except Stop α) : Prop := f = .room ∨ (f = .cap ∧ r = .error .cap)

theorem bind_err {α β : Type} {x : Except Fail α} {g : α → Except Fail β} {f : Fail} (h : x.bind g = .error f) :
    x = .error f ∨ ∃ r, x = .ok r ∧ g r = .error f := by
  cases x with
  | error e => left; cases h; rfl
  | ok r => right; exact ⟨r, rfl, h⟩

theorem map_err {α β : Type} {x : Except Fail α} {g : α → β} {f : Fail} (h : x.map g = .error f) : x = .error f := by
  cases x with
  | error e => cases h; rfl
  | ok r => cases h

/-- the value-mode failure claim -/
def NodeFail (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ sp H f, TyN D Γ none e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → svF K fsX e ew sp H = .error f → FailOK f (ev cx e env)

theorem fail_const (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) :
    NodeFail cx K fsX oc D (.const c) := by
  intro _ _ Γ ks F F' es env ew σ sp H f _ _ _ _ _ _ _ h
  simp only [svF, leafF] at h; split at h
  · cases h
  · cases h; exact .inl rfl

theorem localF_fail : ∀ (w k : Nat) (env : Env) (sp : Nat) (H : Hp) (f : Fail), localF k w env sp H = .error f → f = .room
  | 0, _, _, _, _, _, h => by simp [localF, nilF] at h
  | w + 1, k, env, sp, H, f, h => by
    simp only [localF, pairF] at h
    rcases bind_err h with h1 | ⟨r1, h1, h2⟩
    · simp only [leafF] at h1; split at h1
      · cases h1
      · cases h1; rfl
    · rcases bind_err h2 with h3 | ⟨r2, -, h4⟩
      · exact localF_fail w (k + 1) env _ _ f h3
      · cases h4

theorem fail_loc (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) :
    NodeFail cx K fsX oc D (.loc s w) := by
  intro _ _ Γ ks F F' es env ew σ sp H f _ _ _ _ _ _ _ h
  simp only [svF] at h
  exact .inl (localF_fail w s ew sp H f h)

theorem pairF_fail {wa : Nat} {SA SB : SemWX} {env : Env} {sp : Nat} {H : Hp} {f : Fail}
    (h : pairF wa SA SB env sp H = .error f) :
    SA env sp H = .error f ∨ ∃ r1, SA env sp H = .ok r1 ∧ SB env (sp - 8 * wa) r1.2 = .error f := by
  simp only [pairF] at h
  rcases bind_err h with h1 | ⟨r1, h1, h2⟩
  · exact .inl h1
  · rcases bind_err h2 with h3 | ⟨r2, -, h4⟩
    · exact .inr ⟨r1, h1, h3⟩
    · cases h4

/-- the operand pair of BIN / IF fails only as one of its operands does -/
theorem operands_fail {cx : Ctx} {K : SC} {fsX : Nat → SemDX} (hf : ∀ n, K.fs n = oD (fsX n)) {oc : OwnSpec.Cx}
    {D : List Sig} {a b : ParSpec.Nd}
    (hNa : NodeOK cx K oc D a) (hFa : NodeFail cx K fsX oc D a) (hFb : NodeFail cx K fsX oc D b)
    (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc)
    {Γ : List (Option Kd)} {F : List Bool} {env : List W} {ew : Env} {σ : AH} {sp : Nat} {H : Hp} {f : Fail}
    (ta : TyN D Γ none a [.w]) (tb : TyN D Γ none b [.w]) {a0 b0 : List Bool × List Nat}
    (hca : OwnSpec.chk oc a F = some a0) (hcb : OwnSpec.chk oc b a0.1 = some b0)
    (hE : EnvI σ oc.K F Γ env ew) (hA : AHeap K.hb K.κ H σ) (h8 : H.top % 8 = 0) (hhb : K.hb ≤ H.top) (hr : R2 oc.K F)
    (h : pairF 1 (svF K fsX a) (svF K fsX b) ew sp H = .error f) :
    f = .room ∨ (f = .cap ∧ (val (ev cx a env) = .error .cap ∨
      ∃ va, val (ev cx a env) = .ok va ∧ val (ev cx b env) = .error .cap)) := by
  rcases pairF_fail h with h1 | ⟨r1, h1, h2⟩
  · rcases hFa hC hK2 Γ _ F _ _ env ew σ sp H f ta hca hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
    · exact .inl h
    · exact .inr ⟨rfl, .inl (by rw [he]; rfl)⟩
  · have h1' : sv K a ew sp H = some r1 := by rw [← svF_eq K fsX hf, h1]; rfl
    obtain ⟨σ1, v1, eva, hA1, -, hE1, -, -, h81, hb1, -, -, -⟩ :=
      hNa hC hK2 Γ _ F _ _ env ew σ sp H r1.1 r1.2 ta hca hE hA h8 hhb hr h1'
    rcases hFb hC hK2 Γ _ _ _ _ env ew σ1 _ r1.2 f tb hcb hE1 hA1 h81 hb1
        (hr.keep (chk_keep hK2 hW ta rfl _ _ _ hca).1) h2 with h | ⟨rfl, he⟩
    · exact .inl h
    · exact .inr ⟨rfl, .inr ⟨v1, by rw [eva]; rfl, by rw [he]; rfl⟩⟩

theorem fail_bin (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (op : Nat) (a b : ParSpec.Nd) (hNa : NodeOK cx K oc D a) (hNb : NodeOK cx K oc D b)
    (hFa : NodeFail cx K fsX oc D a) (hFb : NodeFail cx K fsX oc D b) : NodeFail cx K fsX oc D (.bin op a b) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | bin o1 o2 ta tb =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, -⟩ := hc
    simp only [svF, fin2F] at h
    rcases bind_err h with h1 | ⟨r, h1, h2⟩
    · rcases operands_fail hf hNa hFa hFb hC hK2 hW ta tb hca hcb hE hA h8 hhb hr h1 with h | ⟨rfl, ea | ⟨va, ea, eb⟩⟩
      · exact .inl h
      · exact .inr ⟨rfl, by simp [ev, ea, bind, Except.bind]⟩
      · exact .inr ⟨rfl, by simp [ev, ea, eb, bind, Except.bind]⟩
    · have h1' : pairS 1 (sv K a) (sv K b) ew sp H = some (r.1, r.2) := by rw [← pairF_eq K fsX hf, h1]; rfl
      obtain ⟨σ2, x1, x2, -, -, hu, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy hE hA h8 hhb hr h1'
      rw [hu] at h2
      simp [aluF2, ofO] at h2; cases h2

theorem fail_ite (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (c : Nat) (a b t e : ParSpec.Nd) (hNa : NodeOK cx K oc D a) (hNb : NodeOK cx K oc D b)
    (hFa : NodeFail cx K fsX oc D a) (hFb : NodeFail cx K fsX oc D b) (hFt : NodeFail cx K fsX oc D t)
    (hFe : NodeFail cx K fsX oc D e) : NodeFail cx K fsX oc D (.ite c a b t e) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    have hry : R2 oc.K y.1 := by
      obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ hca
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hcb
      exact hr.keep ((ka.trans kb).trans (two_keep ta' tb' hy))
    simp only [svF, ifF] at h
    rcases bind_err h with hp | ⟨r, hp, hq⟩
    · rcases operands_fail hf hNa hFa hFb hC hK2 hW ta tb hca hcb hE hA h8 hhb hr hp with h | ⟨rfl, ea | ⟨va, ea, eb⟩⟩
      · exact .inl h
      · exact .inr ⟨rfl, by simp [ev, ea, bind, Except.bind]⟩
      · exact .inr ⟨rfl, by simp [ev, ea, eb, bind, Except.bind]⟩
    · have hp' : pairS 1 (sv K a) (sv K b) ew sp H = some (r.1, r.2) := by rw [← pairF_eq K fsX hf, hp]; rfl
      obtain ⟨σ2, x1, x2, eva, evb, hu, hA2, hE2, -, -, h82, hb2, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy
        hE hA h8 hhb hr hp'
      have hev' : ev cx (ParSpec.Nd.ite c a b t e) env =
          (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
        rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
      rw [hev']
      rw [hu] at hq
      simp only at hq
      by_cases hcmp : cmpF c x1 x2
      · rw [if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)]
        simp only [hcmp, if_true] at hq
        exact hFt hC hK2 Γ ks _ _ _ env ew σ2 sp r.2 f tt h1 hE2 hA2 h82 hb2 hry hq
      · rw [if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))]
        simp only [hcmp] at hq
        exact hFe hC hK2 Γ ks _ _ _ env ew σ2 sp r.2 f te h3 hE2 hA2 h82 hb2 hry hq

theorem fail_let (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (s w : Nat) (v b : ParSpec.Nd) (hNv : NodeOK cx K oc D v) (hFv : NodeFail cx K fsX oc D v)
    (hFb : NodeFail cx K fsX oc D b) : NodeFail cx K fsX oc D (.letE s w v b) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | letE hv htv hsl hfr hb =>
    rename_i tv
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨v0, hcv, v1, htr, hc⟩ := hc
    split at hc
    · rename_i hcond
      obtain ⟨-, hsK, hv12, -⟩ := hcond
      obtain ⟨b0, hcb, htr2⟩ := Option.bind_eq_some_iff.1 hc
      simp only [svF, letF] at h
      rcases bind_err h with h1 | ⟨r1, hs1, h2⟩
      · rcases hFv hC hK2 Γ tv F _ _ env ew σ sp H f hv hcv hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, val, bind, Except.bind]⟩
      · have hs1' : sv K v ew sp H = some r1 := by rw [← svF_eq K fsX hf, hs1]; rfl
        obtain ⟨σ1, x, evx, hA1, hR1, hE1, -, hM1, h81, hb1, -, -, -⟩ :=
          hNv hC hK2 Γ tv F _ _ env ew σ sp H r1.1 r1.2 hv hcv hE hA h8 hhb hr hs1'
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
        rw [hle]
        exact hFb hC hK2 _ ks _ _ _ _ _ σ1 sp r1.2 f hb hcb hEb' hA1 h81 hb1 hrv h2
    · cases hc

/-- argument lists -/
theorem lst_fail (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) :
    ∀ (cs : List ParSpec.Nd), (∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n) →
    ∀ {Γ ks ds F F1 es0 esA env ew σ sp H f}, TyL D Γ cs ks → OwnSpec.lstA oc cs ds F es0 = some (F1, esA) →
    EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top → R2 oc.K F →
    svLF K fsX cs ew sp H = .error f → FailOK f (evL cx cs env)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [svLF, nilF] at h
  | n :: r, hN, Γ, ks, ds, F, F1, es0, esA, env, ew, σ, sp, H, f, hT, hl, hE, hA, h8, hb, hr, h => by
    cases hT with
    | cons tn tr =>
      simp only [OwnSpec.lstA, Option.bind_eq_some_iff] at hl
      obtain ⟨x, hcn, hl⟩ := hl
      split at hl
      · simp only [svLF] at h
        rcases pairF_fail h with h1 | ⟨r1, h1, h2⟩
        · rcases (hN n (by simp)).2 hC hK2 Γ _ F _ _ env ew σ sp H f tn hcn hE hA h8 hb hr h1 with h | ⟨rfl, he⟩
          · exact .inl h
          · exact .inr ⟨rfl, by simp [evL, he, val, bind, Except.bind]⟩
        · have h1' : sv K n ew sp H = some r1 := by rw [← svF_eq K fsX hf, h1]; rfl
          obtain ⟨σ1, v1, evn, hA1, -, hE1, -, -, h81, hb1, -, -, -⟩ :=
            (hN n (by simp)).1 hC hK2 Γ _ F _ _ env ew σ sp H r1.1 r1.2 tn hcn hE hA h8 hb hr h1'
          rcases lst_fail cx K fsX hf oc D hC hK2 hW r (fun m hm => hN m (by simp [hm])) tr hl hE1 hA1 h81 hb1
              (hr.keep (chk_keep hK2 hW tn rfl _ _ _ hcn).1) h2 with h | ⟨rfl, he⟩
          · exact .inl h
          · exact .inr ⟨rfl, by simp [evL, evn, he, val, bind, Except.bind]⟩
      · cases hl

theorem fail_pair (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (cs : List ParSpec.Nd) (hN : ∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n) :
    NodeFail cx K fsX oc D (.pair cs) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | pair tl =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, -⟩ := hc
    simp only [svF] at h
    rcases lst_fail cx K fsX hf oc D hC hK2 hW cs hN tl hl hE hA h8 hhb hr h with h | ⟨rfl, he⟩
    · exact .inl h
    · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩

end NanoMain

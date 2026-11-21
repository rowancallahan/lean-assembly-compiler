/- Nano/SelfHost/Bridge/MainConvF4: the failure kinds forward — tail mode (loop arms). -/
import Nano.SelfHost.Bridge.MainConvF3

namespace NanoMain
open Templates

def TailFail (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ sk ks F F' es env ew σ sp H f, TyN D Γ (some sk) e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → stF K fsX e ew sp H = .error f → FailOK f (ev cx e env)

theorem tfail_exit {cx : Ctx} {K : SC} {fsX : Nat → SemDX} {oc : OwnSpec.Cx} {D : List Sig} {e : ParSpec.Nd}
    (hN : NodeFail cx K fsX oc D e) (hT' : ∀ Γ sk ks, TyN D Γ (some sk) e ks → TyN D Γ none e ks)
    (hst : ∀ env sp H, stF K fsX e env sp H = exitF (svF K fsX e) env sp H) : TailFail cx K fsX oc D e := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  rw [hst] at h
  exact hN hC hK2 Γ ks F F' es env ew σ sp H f (hT' Γ sk ks hT) hc hE hA h8 hhb hr (map_err h)

theorem tfail_cont {cx : Ctx} {K : SC} {fsX : Nat → SemDX} (hf : ∀ n, K.fs n = oD (fsX n)) {oc : OwnSpec.Cx}
    {D : List Sig} (hW : RsW oc)
    (hAll : ∀ n, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n) (e : ParSpec.Nd) : TailFail cx K fsX oc D (.cont e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | cont te =>
    simp only [stF, contF] at h
    have h' := map_err h
    unfold OwnSpec.chk at hc
    split at hc
    · rename_i cs
      cases te with
      | pair tl =>
        obtain ⟨⟨x1, x2⟩, hl, -⟩ := Option.bind_eq_some_iff.1 hc
        simp only [svF] at h'
        rcases lst_fail cx K fsX hf oc D hC hK2 hW cs (fun n _ => hAll n) tl hl hE hA h8 hhb hr h' with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, val, bind, Except.bind]⟩
    · obtain ⟨⟨x1, x2⟩, hcx, -⟩ := Option.bind_eq_some_iff.1 hc
      rcases (hAll e).2 hC hK2 Γ sk F x1 x2 env ew σ sp H f te hcx hE hA h8 hhb hr h' with h | ⟨rfl, he⟩
      · exact .inl h
      · exact .inr ⟨rfl, by simp [ev, he, val, bind, Except.bind]⟩

theorem tfail_ite (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (c : Nat) (a b t e : ParSpec.Nd) (hNa : NodeOK cx K oc D a) (hNb : NodeOK cx K oc D b)
    (hFa : NodeFail cx K fsX oc D a) (hFb : NodeFail cx K fsX oc D b) (hFt : TailFail cx K fsX oc D t)
    (hFe : TailFail cx K fsX oc D e) : TailFail cx K fsX oc D (.ite c a b t e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    have hry : R2 oc.K y.1 := by
      obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ hca
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hcb
      exact hr.keep ((ka.trans kb).trans (two_keep ta' tb' hy))
    simp only [stF, ifTF] at h
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
        exact hFt hC hK2 Γ sk ks _ _ _ env ew σ2 sp r.2 f tt h1 hE2 hA2 h82 hb2 hry hq
      · rw [if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))]
        simp only [hcmp] at hq
        exact hFe hC hK2 Γ sk ks _ _ _ env ew σ2 sp r.2 f te h3 hE2 hA2 h82 hb2 hry hq

theorem tfail_let (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (s w : Nat) (v b : ParSpec.Nd) (hNv : NodeOK cx K oc D v) (hFv : NodeFail cx K fsX oc D v)
    (hFb : TailFail cx K fsX oc D b) : TailFail cx K fsX oc D (.letE s w v b) := by
  intro hC hK2 Γ sk ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | letE hv htv hsl hfr hb =>
    rename_i tv
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at hc
    obtain ⟨v0, hcv, v1, htr, hc⟩ := hc
    split at hc
    · rename_i hcond
      obtain ⟨-, hsK, hv12, -⟩ := hcond
      obtain ⟨b0, hcb, htr2⟩ := Option.bind_eq_some_iff.1 hc
      simp only [stF, letTF] at h
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
        exact hFb hC hK2 _ sk ks _ _ _ _ _ σ1 sp r1.2 f hb hcb hEb' hA1 h81 hb1 hrv h2
    · cases hc

/-- **tail mode, every node** -/
theorem tfail_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCF : CallFail cx K fsX oc D) :
    ∀ e : ParSpec.Nd, TailFail cx K fsX oc D e
  | .ite c a b t e => tfail_ite cx K fsX hf oc D hW c a b t e (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF a) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF b)
      (tfail_all cx K fsX hf oc D hRs hW hX hCR hCF t) (tfail_all cx K fsX hf oc D hRs hW hX hCR hCF e)
  | .letE s w v b => tfail_let cx K fsX hf oc D hW s w v b (node_all cx K oc D hRs hW hX hCR v) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF v) (tfail_all cx K fsX hf oc D hRs hW hX hCR hCF b)
  | .cont e => tfail_cont hf hW (fun n => ⟨node_all cx K oc D hRs hW hX hCR n, fail_all cx K fsX hf oc D hRs hW hX hCR hCF n⟩) e
  | .loop z s => fun _ _ Γ sk ks F F' es env ew σ sp H f _ hc => by simp [OwnSpec.chk] at hc
  | .const v => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _) (fun _ _ _ h => by cases h; exact .const) (fun _ _ _ => by simp only [stF])
  | .loc s w => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _)
      (fun _ _ _ h => by cases h with | loc hk => exact .loc hk) (fun _ _ _ => by simp only [stF])
  | .bin op a b => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _)
      (fun _ _ _ h => by cases h with | bin o1 o2 ta tb => exact .bin o1 o2 ta tb) (fun _ _ _ => by simp only [stF])
  | .pair cs => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _)
      (fun _ _ _ h => by cases h with | pair tl => exact .pair tl) (fun _ _ _ => by simp only [stF])
  | .call i as => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _)
      (fun _ _ _ h => by cases h with | call tl hd => exact .call tl hd) (fun _ _ _ => by simp only [stF])
  | .prim p as => tfail_exit (fail_all cx K fsX hf oc D hRs hW hX hCR hCF _)
      (fun _ _ _ h => by cases h with | prim tl hp hn => exact .prim tl hp hn) (fun _ _ _ => by simp only [stF])

end NanoMain

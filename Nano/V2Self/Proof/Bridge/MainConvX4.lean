/- Nano/V2Self/Proof/Bridge/MainConvX4: the cap half — tail mode (loop arms). -/
import Nano.V2Self.Proof.Bridge.MainConvX3

namespace NanoMain
open Templates

def TailExC (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ sk ks F F' es env ew σ H, TyN D Γ (some sk) e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → ev cx e env = .error .cap → ExC (stF K fsX e ew) H

theorem texc_exit {cx : Ctx} {K : SC} {fsX : Nat → SemDX} {oc : OwnSpec.Cx} {D : List Sig} {e : ParSpec.Nd}
    (hN : NodeExC cx K fsX oc D e) (hT' : ∀ Γ sk ks, TyN D Γ (some sk) e ks → TyN D Γ none e ks)
    (hst : ∀ env sp H, stF K fsX e env sp H = exitF (svF K fsX e) env sp H) : TailExC cx K fsX oc D e := by
  intro hC hK2 Γ sk ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  exact exc_of_eq (fun sp => (hst ew sp H).symm) (exc_map (hN hC hK2 Γ ks F F' es env ew σ H (hT' Γ sk ks hT) hc hE hA
    h8 hhb hr hev))

theorem texc_cont {cx : Ctx} {K : SC} {fsX : Nat → SemDX} (hf : ∀ n, K.fs n = oD (fsX n)) {oc : OwnSpec.Cx}
    {D : List Sig} (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (hAll : ∀ n, NodeOK cx K oc D n ∧ NodeEx cx K oc D n ∧ NodeExC cx K fsX oc D n) (e : ParSpec.Nd) :
    TailExC cx K fsX oc D (.cont e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  cases hT with
  | cont te =>
    simp only [ev, bind, Except.bind] at hev
    cases ee : val (ev cx e env) with
    | ok x => rw [ee] at hev; cases hev
    | error x =>
    rw [ee] at hev; cases hev
    have eve := val_cap ee
    simp only [stF]
    refine exc_map (f := fun (r : List UInt64 × Hp) => ((Sum.inr r.1 : TRes), r.2)) ?_
    unfold OwnSpec.chk at hc
    split at hc
    · rename_i cs
      cases te with
      | pair tl =>
        obtain ⟨⟨x1, x2⟩, hl, -⟩ := Option.bind_eq_some_iff.1 hc
        simp only [ev, bind, Except.bind] at eve
        cases el : evL cx cs env with
        | ok vl => rw [el] at eve; cases eve
        | error x =>
          rw [el] at eve; cases eve
          simp only [svF]
          exact lst_exc cx K fsX hf oc D hC hK2 hW hFM cs (fun n _ => hAll n) tl hl hE hA h8 hhb hr el
    · obtain ⟨⟨x1, x2⟩, hcx, -⟩ := Option.bind_eq_some_iff.1 hc
      exact (hAll e).2.2 hC hK2 Γ sk F x1 x2 env ew σ H te hcx hE hA h8 hhb hr eve

theorem texc_ite (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) (c : Nat) (a b t e : ParSpec.Nd) (hNa : NodeOK cx K oc D a)
    (hNb : NodeOK cx K oc D b) (hEa : NodeEx cx K oc D a) (hEb : NodeEx cx K oc D b) (hCa : NodeExC cx K fsX oc D a)
    (hCb : NodeExC cx K fsX oc D b) (hCt : TailExC cx K fsX oc D t) (hCe : TailExC cx K fsX oc D e) :
    TailExC cx K fsX oc D (.ite c a b t e) := by
  intro hC hK2 Γ sk ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
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
    simp only [stF]
    cases ea : val (ev cx a env) with
    | error e' =>
      rw [ea] at hev; cases hev
      exact exc_bind_of (operands_exc hf hNa hEa hCa hCb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (Or.inl ea))
        (fun sp => rfl)
    | ok va =>
      cases eb : val (ev cx b env) with
      | error e' =>
        rw [ea, eb] at hev; cases hev
        exact exc_bind_of (operands_exc hf hNa hEa hCa hCb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr
          (Or.inr ⟨va, ea, eb⟩)) (fun sp => rfl)
      | ok vb =>
        have hp := operands_ex hNa hEa hEb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (val_ok_of ea) (val_ok_of eb)
        have := exc_seq (T := fun r1 sp' H' => match r1.1 with
            | [x, z] => if cmpF c x z then stF K fsX t ew sp' H' else stF K fsX e ew sp' H' | _ => .error .stuck) 0
          Prod.snd (pairF_ex K fsX hf hp) (pairF_mo' K fsX hf hFM a b ew) (fun sp r1 _ hr1 => by
            have hr1' : pairS 1 (sv K a) (sv K b) ew sp H = some (r1.1, r1.2) := by
              rw [← pairF_eq K fsX hf, hr1]; rfl
            obtain ⟨σ2, x1, x2, eva, evb, hu, hA2, hE2, -, -, h82, hb2, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy
              hE hA h8 hhb hr hr1'
            have hev' : ev cx (ParSpec.Nd.ite c a b t e) env =
                (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
              rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
            rw [hev'] at hev0
            simp only [hu]
            by_cases hcmp : cmpF c x1 x2
            · rw [if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)] at hev0
              obtain ⟨N, hN⟩ := hCt hC hK2 Γ sk ks _ _ _ env ew σ2 r1.2 tt h1 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_true]; exact hN sp' a b⟩
            · rw [if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))] at hev0
              obtain ⟨N, hN⟩ := hCe hC hK2 Γ sk ks _ _ _ env ew σ2 r1.2 te h3 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_false]; exact hN sp' a b⟩)
        exact exc_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this

theorem texc_let (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) (s w : Nat) (v b : ParSpec.Nd) (hNv : NodeOK cx K oc D v)
    (hEv : NodeEx cx K oc D v) (hCv : NodeExC cx K fsX oc D v) (hCb : TailExC cx K fsX oc D b) :
    TailExC cx K fsX oc D (.letE s w v b) := by
  intro hC hK2 Γ sk ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
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
      simp only [stF]
      cases ea : val (ev cx v env) with
      | error e' =>
        rw [ea] at hev; cases hev
        exact exc_bind_of (hCv hC hK2 Γ tv F _ _ env ew σ H hv hcv hE hA h8 hhb hr (val_cap ea)) (fun sp => rfl)
      | ok x0 =>
        have evx := val_ok_of ea
        have := exc_seq (T := fun r1 sp' H' => stF K fsX b (setW ew s w r1.1) sp' H') 0 Prod.snd
          (svF_ex K fsX hf (hEv hC hK2 Γ tv F _ _ env ew σ H x0 hv hcv hE hA h8 hhb hr evx)) (svF_mo' K fsX hf hFM v ew)
          (fun sp r1 _ hs1 => by
            have hs1' : sv K v ew sp H = some r1 := by rw [← svF_eq K fsX hf, hs1]; rfl
            obtain ⟨σ1, x, evv, hA1, hR1, hE1, -, hM1, h81, hb1, -, -, -⟩ :=
              hNv hC hK2 Γ tv F _ _ env ew σ sp H r1.1 r1.2 hv hcv hE hA h8 hhb hr hs1'
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
            exact hCb hC hK2 _ sk ks _ _ _ _ _ σ1 r1.2 hb hcb hEb' hA1 h81 hb1 hrv hev0)
        exact exc_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this
    · cases hc

/-- **tail mode, every node** -/
theorem texc_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D)
    (hCC : CallExC cx K fsX oc D) (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) :
    ∀ e : ParSpec.Nd, TailExC cx K fsX oc D e
  | .ite c a b t e => texc_ite cx K fsX hf oc D hW hFM c a b t e (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ a) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ b)
      (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ a) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ b) (texc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ t) (texc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ e)
  | .letE s w v b => texc_let cx K fsX hf oc D hW hFM s w v b (node_all cx K oc D hRs hW hX hCR v) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ v) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ v) (texc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ b)
  | .cont e => texc_cont hf hW hFM (fun n => ⟨node_all cx K oc D hRs hW hX hCR n, ex_all cx K oc D hRs hW hX hCR hCE hFM hκ n, exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ n⟩) e
  | .loop z s => fun _ _ Γ sk ks F F' es env ew σ H _ hc => by simp [OwnSpec.chk] at hc
  | .const v => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _) (fun _ _ _ h => by cases h; exact .const) (fun _ _ _ => by simp only [stF])
  | .loc s w => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _)
      (fun _ _ _ h => by cases h with | loc hk => exact .loc hk) (fun _ _ _ => by simp only [stF])
  | .bin op a b => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _)
      (fun _ _ _ h => by cases h with | bin o1 o2 ta tb => exact .bin o1 o2 ta tb) (fun _ _ _ => by simp only [stF])
  | .pair cs => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _)
      (fun _ _ _ h => by cases h with | pair tl => exact .pair tl) (fun _ _ _ => by simp only [stF])
  | .call i as => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _)
      (fun _ _ _ h => by cases h with | call tl hd => exact .call tl hd) (fun _ _ _ => by simp only [stF])
  | .prim p as => texc_exit (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ _)
      (fun _ _ _ h => by cases h with | prim tl hp hn => exact .prim tl hp hn) (fun _ _ _ => by simp only [stF])

end NanoMain

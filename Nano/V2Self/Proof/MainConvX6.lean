/- Nano/V2Self/Proof/MainConvX6: the cap half — a def. -/
import Nano.V2Self.Proof.MainConvX5

namespace NanoMain
open Templates

theorem defSF_exc {p nl : Nat} {Sb : SemWX} {ws : List UInt64} {H : Hp} (h : ExC (Sb (argEnv p ws)) H) :
    ExC (defSF p nl Sb ws) H := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 16 + 8 * (nl - p), fun sp a b => ?_⟩
  simp only [defSF]; rw [if_pos (by omega)]; exact hN _ (by omega) (by omega)

theorem def_exc (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf' : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D) (hCC : CallExC cx K fsX oc D) (hFM : ∀ i args, Mo (K.fs i args))
    (hκ : K.κ < 2 ^ 40)
    (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (d : ParSpec.DefA) (sg : Sig) (R : List Nat)
    (hTy : TyDef D d sg) (hdo : OwnSpec.defOk oc.ps oc.rs oc.K d = some R) (hnpw : oc.npw = d.npw) (hp : K.p = d.npw) :
    DefExC K.hb K.κ sg.1 (oc.K.take d.npw) (defMean cx.inp cx.κ cx.defs d) (defSF d.npw d.nslots (svF K fsX d.body)) := by
  intro σ args ws H hA h8 hhb hk hArgs hf
  obtain ⟨t1, t2, t3, t4⟩ := hTy
  have hoc : (⟨oc.ps, oc.rs, oc.K, d.npw⟩ : OwnSpec.Cx) = oc := by rw [← hnpw]
  unfold OwnSpec.defOk at hdo
  split at hdo
  · rename_i hcond
    obtain ⟨hKl, -⟩ := hcond
    simp only [hoc] at hdo
    obtain ⟨k, hr, hk2⟩ := Option.bind_eq_some_iff.1 hdo
    have hal : args.length = d.npw := by rw [← kOf_length, hk, t1]
    have hpk : sg.1.length = d.npw := t1.symm
    have hE0 := def_envI (F := List.replicate d.nslots false) (n := d.nslots - d.npw) hk
      (by rw [hpk]; exact hArgs) (by rw [hKl, hpk]; omega)
    rw [hpk] at hE0
    have hr0 := r2_init (Kk := oc.K) hKl
    refine defSF_exc ?_
    have hdm : defMean cx.inp cx.κ cx.defs d = fun ps =>
        if ps.length = d.npw ∧ d.npw ≤ d.nslots then do
          let v ← val (ev ⟨cx.inp, cx.κ, cx.defs⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))
          if v.length = d.nres then pure v else .error .stuck
        else .error .stuck := rfl
    rw [hdm] at hf
    simp only [hal, t2, and_self, if_true, bind, Except.bind] at hf
    cases evb : val (ev ⟨cx.inp, cx.κ, cx.defs⟩ d.body (args ++ List.replicate (d.nslots - d.npw) (.w 0))) with
    | ok v => rw [evb] at hf; simp only at hf; split at hf <;> cases hf
    | error e =>
    rw [evb] at hf; cases hf
    have evb' := val_cap evb
    generalize hbd : d.body = body at t4 hr evb' ⊢
    cases t4 with
    | plain tb =>
      split at hr
      · cases tb
      · obtain ⟨⟨x1, x2⟩, hx, -⟩ := Option.bind_eq_some_iff.1 hr
        exact exc_all cx K fsX hf' oc D hRs hW hX hCR hCE hCC hFM hκ _ hC hK2 _ sg.2 _ _ _ _ _ σ H tb hx hE0 hA h8 hhb hr0 evb'
    | loop hΓ tz ts =>
      rename_i z s sk n'
      obtain ⟨hsg, hn'⟩ := map_some_inj _ (Kd.w :: sk) _ _ (by simpa using hΓ)
      have hnp : d.npw = 1 + sk.length := by rw [← hpk, hsg]; simp; omega
      have hns : d.nslots = 1 + sk.length + n' := by omega
      have hOs : OwnSt σ (fun u => ∃ (j : Nat) (l : List UInt64), (oc.K.take d.npw)[j]? = some 1 ∧
          args[j]? = some (W.b l) ∧ ws[j]? = some u) oc.K (sg.1.map some ++ List.replicate (d.nslots - d.npw) none)
          (args ++ List.replicate (d.nslots - d.npw) (.w 0)) (argEnv d.npw ws) := by
        intro j l kj k1 ej
        have hj : j < d.npw := by
          obtain ⟨kd, h⟩ := kj
          refine Nat.lt_of_not_le fun hj => ?_
          rw [List.getElem?_append_right (by simp; omega)] at h; simp [List.getElem?_replicate] at h
        right
        refine ⟨j, l, ?_, by rw [← List.getElem?_append_left (show j < args.length by omega)]; exact ej, ?_⟩
        · rw [List.getElem?_take_of_lt hj, ← k1, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (show j < oc.K.length by omega)]; rfl
        · have hw : ws.length = d.npw := by rw [hArgs.2.1]; simp; omega
          rw [argEnv_get _ _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ws.length by omega)]
          rfl
      rw [hΓ] at hE0 hOs tz ts
      have hF : List.replicate d.nslots false = List.replicate (1 + sk.length + n') false := by rw [hns]
      rw [hF] at hE0 hr
      obtain ⟨z0, hz0, h⟩ := Option.bind_eq_some_iff.1 hr
      obtain ⟨z1, hz1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨s0, hs0, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨s1, hs1, hj⟩ := Option.bind_eq_some_iff.1 h
      rw [hsg] at hk
      obtain ⟨x0, rest, rfl⟩ : ∃ x0 rest, args = x0 :: rest := by
        cases args with | nil => simp [kOf] at hk | cons x0 rest => exact ⟨x0, rest, rfl⟩
      obtain ⟨n0, rfl⟩ : ∃ n0, x0 = .w n0 := by
        cases x0 with
        | w n0 => exact ⟨n0, rfl⟩
        | b l => simp [kOf, W.k] at hk
      have hw0 : argEnv d.npw ws 0 = n0 := by
        have := hArgs.2.2.1 0 (.w n0) (ws.getD 0 0) rfl (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < ws.length by
            rw [hArgs.2.1]; simp; omega)]; rfl)
        rw [argEnv_get _ _ _ (by omega)]; simp only [VR] at this; exact this
      have hLI : LI σ (fun u => ∃ (j : Nat) (l : List UInt64), (oc.K.take d.npw)[j]? = some 1 ∧
          (W.w n0 :: rest)[j]? = some (W.b l) ∧ ws[j]? = some u) oc.K
          (some Kd.w :: sk.map some ++ List.replicate n' none) (List.replicate (1 + sk.length + n') false) K.hb K.κ
          σ H (W.w n0 :: rest ++ List.replicate (d.nslots - d.npw) (.w 0)) (argEnv d.npw ws) :=
        ⟨hE0, hA, h8, hhb, Grow.refl σ, fun a _ _ => rfl, hOs⟩
      simp only [ev, List.cons_append, bind, Except.bind] at evb'
      cases hlr : loopRun (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ z e) (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ s e) n0.toNat
          (W.w n0 :: (rest ++ List.replicate (d.nslots - d.npw) (W.w 0))) with
      | ok v' => rw [hlr] at evb'; cases evb'
      | error e =>
      rw [hlr] at evb'; cases evb'
      have E := loop_exc cx K fsX hf' oc D hRs hW hX hCR hCE hCC hFM hκ hC hK2 (by omega) (by omega) (by omega) tz ts hz0
        hs0 σ _ n0.toNat σ H _ _ hLI (by rw [hw0]) (by simp [hw0]) hlr
      simp only [svF]
      exact exc_of_eq (fun sp => by simp only [loopF, hw0]) E
  · cases hdo

end NanoMain

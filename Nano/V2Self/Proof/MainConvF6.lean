/- Nano/V2Self/Proof/MainConvF6: the failure kinds forward — a def. -/
import Nano.V2Self.Proof.MainConvF5

namespace NanoMain
open Templates

theorem def_fail (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf' : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) (hCF : CallFail cx K fsX oc D)
    (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (d : ParSpec.DefA) (sg : Sig) (R : List Nat)
    (hTy : TyDef D d sg) (hdo : OwnSpec.defOk oc.ps oc.rs oc.K d = some R) (hnpw : oc.npw = d.npw) (hp : K.p = d.npw) :
    DefFail K.hb K.κ sg.1 (oc.K.take d.npw) (defMean cx.inp cx.κ cx.defs d) (defSF d.npw d.nslots (svF K fsX d.body)) := by
  intro σ args ws sp H fl hA h8 hhb hk hArgs hx
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
    simp only [defSF] at hx
    by_cases hfr : fl = .room
    · exact .inl hfr
    have hroom : H.top + 16 + 8 * (d.nslots - d.npw) ≤ sp :=
      Classical.byContradiction fun c => by rw [if_neg c] at hx; cases hx; exact hfr rfl
    rw [if_pos hroom] at hx
    have hdm : defMean cx.inp cx.κ cx.defs d = fun ps =>
        if ps.length = d.npw ∧ d.npw ≤ d.nslots then do
          let v ← val (ev ⟨cx.inp, cx.κ, cx.defs⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))
          if v.length = d.nres then pure v else .error .stuck
        else .error .stuck := rfl
    rw [hdm]
    simp only [hal, t2, and_self, if_true, bind, Except.bind]
    suffices hO : FailOK fl (ev ⟨cx.inp, cx.κ, cx.defs⟩ d.body (args ++ List.replicate (d.nslots - d.npw) (.w 0))) by
      rcases hO with h' | ⟨h1, h2⟩
      · exact .inl h'
      · exact .inr ⟨h1, by rw [h2]; rfl⟩
    generalize hbd : d.body = body at t4 hr hx ⊢
    cases t4 with
    | plain tb =>
      split at hr
      · cases tb
      · obtain ⟨⟨x1, x2⟩, hcx, -⟩ := Option.bind_eq_some_iff.1 hr
        exact fail_all cx K fsX hf' oc D hRs hW hX hCR hCF _ hC hK2 _ sg.2 _ _ _ _ _ σ _ H fl tb hcx hE0 hA h8 hhb hr0 hx
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
      simp only [svF, loopF] at hx
      have hF := loop_fail cx K fsX hf' oc D hRs hW hX hCR hCF hC hK2 (by omega) (by omega) (by omega) tz ts hz0
        hs0 σ _ n0.toNat σ H _ _ _ fl hLI (by rw [hw0]) (by simp [hw0]) (by rw [hw0] at hx; exact hx)
      simp only [ev, List.cons_append, bind, Except.bind]
      rcases hF with h' | ⟨h1, h2⟩
      · exact .inl h'
      · refine .inr ⟨h1, ?_⟩
        have e : loopRun (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ z e) (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ s e) n0.toNat
            (W.w n0 :: (rest ++ List.replicate (d.nslots - d.npw) (W.w 0))) = .error .cap := h2
        rw [e]
  · cases hdo

end NanoMain

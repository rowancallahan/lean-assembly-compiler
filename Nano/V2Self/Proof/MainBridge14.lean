/- Nano/V2Self/Proof/MainBridge14: the Sem ⇐ sv bridge — one def meets the callee contract (`def_ok`). -/
import Nano.V2Self.Proof.MainBridge13

namespace NanoMain
open Templates

theorem argEnv_get (p : Nat) (ws : List UInt64) (k : Nat) (hk : k < p) : argEnv p ws k = ws.getD k 0 := by
  simp [argEnv, hk]

/-- the frame invariant at a def's entry: parameters from related arguments, locals unknown -/
theorem def_envI {σ : AH} {Kk : List Nat} {F : List Bool} {pk : List Kd} {n : Nat} {args : List W} {ws : List UInt64}
    (hk : kOf args = pk) (hA : ArgsR σ (Kk.take pk.length) args ws) (hKl : Kk.length = pk.length + n) :
    EnvI σ Kk F (pk.map some ++ List.replicate n none) (args ++ List.replicate n (.w 0)) (argEnv pk.length ws) := by
  have ha : args.length = pk.length := by rw [← hk, kOf_length]
  have hw : ws.length = pk.length := by rw [hA.2.1]; simp; omega
  have hKn : ∀ k, Kn (pk.map some ++ List.replicate n none) k → k < pk.length := by
    intro k ⟨kd, h⟩
    refine Nat.lt_of_not_le fun hk => ?_
    rw [List.getElem?_append_right (by simpa using hk)] at h
    simp [List.getElem?_replicate] at h
  have hP : ∀ k, k < pk.length → (Kk.take pk.length)[k]? = some (Kk.getD k 0) := by
    intro k hk'
    rw [List.getElem?_take_of_lt hk', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have hv : ∀ k, k < pk.length → (args ++ List.replicate n (W.w 0))[k]? = args[k]? := fun k hk' =>
    List.getElem?_append_left (by omega)
  have hu : ∀ k, k < pk.length → ws[k]? = some (argEnv pk.length ws k) := by
    intro k hk'
    rw [argEnv_get _ _ _ hk', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ws.length by omega)]; rfl
  refine ⟨by simp; omega, by rw [← hk]; exact (f2_kOf args).append (envOK_rep n), fun k kn hr => ?_,
    fun a b la lb hab ka kb k1 k0 da db ea eb => ?_⟩
  · have hk' := hKn k kn
    obtain ⟨x, hx⟩ : ∃ x, args[k]? = some x := ⟨args[k]'(by omega), List.getElem?_eq_getElem _⟩
    refine ⟨x, by rw [hv k hk', hx], hA.2.2.1 k x _ hx (hu k hk'), fun h0 => hA.2.2.2.1 k x ?_ hx⟩
    rw [hP k hk', h0]
  · have ha' := hKn a ka
    have hb' := hKn b kb
    rw [hv a ha'] at ea; rw [hv b hb'] at eb
    exact hA.2.2.2.2 a b la lb _ _ hab (by rw [hP a ha', k1]) ea eb (hu a ha') (hu b hb')

theorem map_some_inj {α : Type} : ∀ (xs ys : List α) (a b : Nat),
    xs.map some ++ List.replicate a none = ys.map some ++ List.replicate b none → xs = ys ∧ a = b
  | [], [], a, b, h => by simp at h; exact ⟨rfl, h⟩
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
    obtain ⟨e, r⟩ := map_some_inj xs ys a b h.2; exact ⟨by rw [h.1, e], r⟩
  | [], y :: ys, a, b, h => by
    cases a with
    | zero => simp at h
    | succ a => simp [List.replicate_succ] at h
  | x :: xs, [], a, b, h => by
    cases b with
    | zero => simp at h
    | succ b => simp [List.replicate_succ] at h

/-- turning the loop/body results into the callee contract -/
theorem defR_of {σ σ' : AH} {P R : List Nat} {args : List W} {ws rs : List UInt64} {v : List W}
    (hRR : ResR σ σ' (fun u => ∃ (j : Nat) (l : List UInt64), P[j]? = some 1 ∧ args[j]? = some (W.b l) ∧ ws[j]? = some u)
      R v rs)
    (hFr : Frame0 σ σ' (fun u => ∃ (j : Nat) (l : List UInt64), P[j]? = some 1 ∧ args[j]? = some (W.b l) ∧ ws[j]? = some u)) :
    v.length = R.length ∧ rs.length = R.length ∧
    (∀ (j e : Nat) (x : W) (u : UInt64), R[j]? = some e → v[j]? = some x → rs[j]? = some u → VR σ' x u ∧
      (e = 0 → ∃ y, x = .w y) ∧ (e = 1 → ∀ l, x = .b l → σ u.toNat = none ∨
        ∃ (j' : Nat) (l' : List UInt64), P[j']? = some 1 ∧ args[j']? = some (W.b l') ∧ ws[j']? = some u)) ∧
    (∀ (j j' : Nat) (l l' : List UInt64) (u u' : UInt64), j ≠ j' → R[j]? = some 1 → R[j']? = some 1 →
      v[j]? = some (W.b l) → v[j']? = some (W.b l') → rs[j]? = some u → rs[j']? = some u' → u ≠ u') ∧
    (∀ a, (σ a).isSome → (∀ (j : Nat) (l : List UInt64) (u : UInt64), P[j]? = some 1 → args[j]? = some (W.b l) →
      ws[j]? = some u → u.toNat ≠ a) → σ' a = σ a) :=
  ⟨hRR.1, hRR.2.1, hRR.2.2.1, hRR.2.2.2, fun a ha hn => hFr a ha fun u ⟨j, l, x, y, z⟩ => hn j l u x y z⟩

/-- **one def meets its contract**: E's `defS` of the body's template ↔ `Sem`'s `defMean` -/
theorem def_ok (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (d : ParSpec.DefA) (sg : Sig) (R : List Nat)
    (hTy : TyDef D d sg) (hdo : OwnSpec.defOk oc.ps oc.rs oc.K d = some R) (hnpw : oc.npw = d.npw) (hp : K.p = d.npw) :
    DefR K.hb K.κ sg.1 (oc.K.take d.npw) R (defMean cx.inp cx.κ cx.defs d) (defS d.npw d.nslots (sv K d.body)) := by
  intro σ args ws sp H rs H' hA h8 hhb hk hArgs hs
  obtain ⟨t1, t2, t3, t4⟩ := hTy
  have hoc : (⟨oc.ps, oc.rs, oc.K, d.npw⟩ : OwnSpec.Cx) = oc := by rw [← hnpw]
  unfold OwnSpec.defOk at hdo
  split at hdo
  · rename_i hcond
    obtain ⟨hKl, -⟩ := hcond
    simp only [hoc] at hdo
    obtain ⟨k, hr, hk2⟩ := Option.bind_eq_some_iff.1 hdo
    split at hk2
    · rename_i hkl
      simp only [Option.some.injEq] at hk2; subst hk2
      unfold defS at hs
      split at hs
      · have hal : args.length = d.npw := by rw [← kOf_length, hk, t1]
        have hpk : sg.1.length = d.npw := t1.symm
        have hcx : (⟨cx.inp, cx.κ, cx.defs⟩ : Ctx) = cx := rfl
        have hE0 := def_envI (F := List.replicate d.nslots false) (n := d.nslots - d.npw) hk
          (by rw [hpk]; exact hArgs) (by rw [hKl, hpk]; omega)
        rw [hpk] at hE0
        have hr0 := r2_init (Kk := oc.K) hKl
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
        have hdm : defMean cx.inp cx.κ cx.defs d = fun ps =>
            if ps.length = d.npw ∧ d.npw ≤ d.nslots then do
              let v ← val (ev ⟨cx.inp, cx.κ, cx.defs⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))
              if v.length = d.nres then pure v else .error .stuck
            else .error .stuck := rfl
        rw [hdm]
        generalize hbd : d.body = body at t4 hr hs ⊢
        cases t4 with
        | plain tb =>
          split at hr
          · cases tb
          · obtain ⟨⟨x1, x2⟩, hx, hy⟩ := Option.bind_eq_some_iff.1 hr
            obtain ⟨⟨y1, y2⟩, hy', he⟩ := Option.map_eq_some_iff.1 hy
            simp only at he; subst he
            obtain ⟨σ', v, evb, hA', hR, hE', hCh, hM, h8', hb', hS, -, hG⟩ :=
              node_all cx K oc D hRs hW hX hCR _ hC hK2 _ sg.2 _ _ _ _ _ σ _ H rs H' tb hx hE0 hA h8 hhb hr0 hs
            obtain ⟨m2, hR2, r2, -, -⟩ := tr_spec hK2 _ v rs _ _ _ hR hE' hy'
            obtain ⟨-, hS2⟩ := tr_src _ _ _ _ _ _ hR hM hS hy'
            obtain ⟨kx, tx⟩ := chk_keep hK2 hW tb rfl _ _ _ hx
            have kp := kx.trans (tr_keep _ _ _ _ tx hy').1
            have hRR := res_step hR2 r2 hS2 kp hOs (Grow.refl σ)
            have hFr := frame_step (fun a _ _ => rfl) (hCh.weak m2) kp hOs
            obtain ⟨l1, l2, c1, c2, c3⟩ := defR_of hRR hFr
            refine ⟨σ', v, ?_, hA', h8', hb', l1, l2, c1, c2, c3, hG⟩
            simp only [hal, t2, and_self, if_true, evb, val, bind, Except.bind, pure, Except.pure]
            rw [if_pos (by rw [l1]; exact hkl)]
        | loop hΓ tz ts =>
          rename_i sk n'
          obtain ⟨hsg, hn'⟩ := map_some_inj _ (Kd.w :: sk) _ _ (by simpa using hΓ)
          have hnp : d.npw = 1 + sk.length := by rw [← hpk, hsg]; simp; omega
          have hns : d.nslots = 1 + sk.length + n' := by omega
          rw [hΓ] at hE0 hOs tz ts
          have hF : List.replicate d.nslots false = List.replicate (1 + sk.length + n') false := by rw [hns]
          rw [hF] at hE0 hr
          have hr0' := r2_init (Kk := oc.K) (n := 1 + sk.length + n') (by omega)
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
          simp only [sv, loopS] at hs
          have hLI : LI σ (fun u => ∃ (j : Nat) (l : List UInt64), (oc.K.take d.npw)[j]? = some 1 ∧
              (W.w n0 :: rest)[j]? = some (W.b l) ∧ ws[j]? = some u) oc.K
              (some Kd.w :: sk.map some ++ List.replicate n' none) (List.replicate (1 + sk.length + n') false) K.hb K.κ
              σ H (W.w n0 :: rest ++ List.replicate (d.nslots - d.npw) (.w 0)) (argEnv d.npw ws) :=
            ⟨hE0, hA, h8, hhb, Grow.refl σ, fun a _ _ => rfl, hOs⟩
          obtain ⟨σ', v, hlr, hA', h8', hb', hG', hFr', hRR⟩ :=
            loop_run cx K oc D hRs hW hX hCR hC hK2 (by omega) (by omega) (by omega) tz ts hz0 hz1 hs0 hs1 hj σ _ _ rs H'
              _ σ H _ _ hLI rfl (by simp [hw0]) hs
          obtain ⟨l1, l2, c1, c2, c3⟩ := defR_of hRR hFr'
          refine ⟨σ', v, ?_, hA', h8', hb', l1, l2, c1, c2, c3, hG'⟩
          rw [hw0] at hlr
          have hlr' : loopRun (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ _ e) (fun e => ev ⟨cx.inp, cx.κ, cx.defs⟩ _ e)
              n0.toNat (W.w n0 :: (rest ++ List.replicate (d.nslots - d.npw) (W.w 0))) = .ok v := hlr
          simp only [hal, t2, and_self, if_true, ev, List.cons_append, val, bind, Except.bind, pure,
            Except.pure, hlr']
          rw [if_pos (by rw [l1]; exact hkl)]
      · cases hs
    · cases hk2
  · cases hdo

end NanoMain

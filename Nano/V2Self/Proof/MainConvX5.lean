/- Nano/V2Self/Proof/MainConvX5: the cap half — the fuel loop. -/
import Nano.V2Self.Proof.MainConvX4

namespace NanoMain
open Templates

/-- a value-mode expression's kinded tail semantics is its value semantics, exiting -/
theorem stF_none (K : SC) (fsX : Nat → SemDX) {D : List Sig} : ∀ {Γ S e ks}, TyN D Γ S e ks → S = none →
    ∀ env sp H, stF K fsX e env sp H = exitF (svF K fsX e) env sp H
  | _, _, _, _, .const, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .loc _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .bin _ _ _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .pair _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .call _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .prim _ _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .cont _, hS, _, _, _ => by cases hS
  | _, _, _, _, .ite (c := c) (a := a) (b := b) (t := t) (e := e) _ _ _ tt te, hS, env, sp, H => by
    simp only [stF, svF, ifTF, ifF, exitF]
    cases h : pairF 1 (svF K fsX a) (svF K fsX b) env sp H with
    | error x => rfl
    | ok r =>
      simp only [Except.bind]
      split
      · split
        · rw [stF_none K fsX tt hS env sp]; rfl
        · rw [stF_none K fsX te hS env sp]; rfl
      · rfl
  | _, _, _, _, .letE (s := s) (w := w) (v := v) (b := b) _ _ _ _ tb, hS, env, sp, H => by
    simp only [stF, svF, letTF, letF, exitF]
    cases h : svF K fsX v env sp H with
    | error x => rfl
    | ok r => simp only [Except.bind]; rw [stF_none K fsX tb hS _ sp]; rfl

theorem stF_eq (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (e : ParSpec.Nd) (env : Env) (sp : Nat)
    (H : Hp) : toO (stF K fsX e env sp H) = st K e env sp H :=
  congrFun (congrFun (congrFun (oT_st K fsX hf e) env) sp) H

theorem loop_exc (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc)
    (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D) (hCC : CallExC cx K fsX oc D)
    (hFM : ∀ i args, Mo (K.fs i args))
    (hκ : K.κ < 2 ^ 40) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2)
    {sk : List Kd} {m : Nat} {ks : List Kd} {z s : ParSpec.Nd} {z0 s0 : List Bool × List Nat}
    (hlen : oc.K.length = 1 + sk.length + m) (hp : K.p = 1 + sk.length) (hnpw : oc.npw = 1 + sk.length)
    (tz : TyN D (some Kd.w :: sk.map some ++ List.replicate m none) none z ks)
    (ts : TyN D (some Kd.w :: sk.map some ++ List.replicate m none) (some sk) s ks)
    (hz0 : OwnSpec.chk oc z (List.replicate (1 + sk.length + m) false) = some z0)
    (hs0 : OwnSpec.chk oc s (List.replicate (1 + sk.length + m) false) = some s0) (σ0 : AH) (OA : UInt64 → Prop) :
    ∀ N σ H env ew, LI σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none)
      (List.replicate (1 + sk.length + m) false) K.hb K.κ σ H env ew → (ew 0).toNat = N → env[0]? = some (.w (ew 0)) →
      loopRun (ev cx z) (ev cx s) N env = .error .cap →
      ExC (fun sp H => loopGoF K.p (stF K fsX z) (stF K fsX s) sp N ew H) H := by
  have hr0 := r2_init (Kk := oc.K) hlen
  obtain ⟨ks0, ts0⟩ := chk_keep_tail hK2 hW ts _ _ _ hs0
  intro N
  induction N with
  | zero =>
    intro σ H env ew hI h0 he0 hrun
    have hz : ew 0 = 0 := UInt64.toNat_inj.1 (by simpa using h0)
    simp only [loopRun] at hrun
    have E := exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ z hC hK2 _ ks _ _ _ env ew σ H tz hz0 hI.E hI.A hI.t8
      hI.tb hr0 (val_cap hrun)
    obtain ⟨N0, hN0⟩ := E
    refine ⟨N0, fun sp a b => ?_⟩
    unfold loopGoF; dsimp only; rw [if_pos hz, stF_none K fsX tz rfl]
    simp only [exitF, hN0 sp a b]; rfl
  | succ N ih =>
    intro σ H env ew hI h0 he0 hrun
    have hnz : ew 0 ≠ 0 := fun q => by rw [q] at h0; simp at h0
    obtain ⟨x0, tl, rfl⟩ : ∃ x0 tl, env = x0 :: tl := by
      cases env with | nil => simp at he0 | cons x0 tl => exact ⟨x0, tl, rfl⟩
    have hdec : decE ew 0 = UInt64.ofNat N := by simp only [decE, if_true]; exact dec_word h0
    have hE1 := envI_slot0 (y := UInt64.ofNat N) hI.E (by simp) hdec (fun k hk => by simp [decE, hk])
    have hO1 : OwnSt σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none) (.w (UInt64.ofNat N) :: tl)
        (decE ew) := by
      intro j l kj k1 ej
      rcases j with _ | j
      · cases ej
      · have := hI.Os (j + 1) l kj k1 ej; simpa [decE] using this
    have hss1 : setSlots (x0 :: tl) 0 [.w (UInt64.ofNat N)] = .ok (.w (UInt64.ofNat N) :: tl) := by
      simp [setSlots]
    simp only [loopRun, hss1, bind, Except.bind] at hrun
    cases evo : ev cx s (.w (UInt64.ofNat N) :: tl) with
    | error e =>
      rw [evo] at hrun; cases hrun
      have EC := texc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ s hC hK2 _ sk ks _ _ _ _ _ σ H ts hs0 hE1 hI.A
        hI.t8 hI.tb hr0 evo
      exact exc_bind_of EC (fun sp => by unfold loopGoF; rw [if_neg hnz])
    | ok out0 =>
    rw [evo] at hrun
    have ES := tex_all cx K oc D hRs hW hX hCR hCE hFM hκ s hC hK2 _ sk ks _ _ _ _ _ σ H out0 ts hs0 hE1 hI.A hI.t8
      hI.tb hr0 evo
    have ESF : Ex (fun sp H => toO (stF K fsX s (decE ew) sp H)) H :=
      ex_of_eq (fun sp => (stF_eq K fsX hf s _ sp H).symm) ES
    have MSF : Mo (fun sp H => toO (stF K fsX s (decE ew) sp H)) := by
      intro sp sp' H r h h1 h2; dsimp only at h ⊢; rw [stF_eq K fsX hf] at h ⊢; exact st_mo K hFM s _ sp sp' H r h h1 h2
    refine exc_of_eq (fun sp => ?_) (exc_seq (T := fun (r1 : TRes × Hp) sp' H' => match r1.1 with
        | .inl vs => .ok (vs, H')
        | .inr st' => loopGoF K.p (stF K fsX z) (stF K fsX s) sp' N (setW (decE ew) 1 (K.p - 1) st') H') 0 Prod.snd ESF
      MSF fun sp r1 _ hssF => ?_)
    · conv => rhs; rw [loopGoF.eq_def]
      dsimp only; rw [if_neg hnz]; simp only [Nat.sub_zero]; rfl
    have hss : st K s (decE ew) sp H = some r1 := by rw [← stF_eq K fsX hf, hssF]; rfl
    obtain ⟨σ2, out, evs, hA2, hE2, hCh2, hM2, h82, hb2, hG2, hout⟩ :=
      tail_all cx K oc D hRs hW hX hCR s hC hK2 _ sk ks _ _ _ _ _ σ sp H r1.1 r1.2 ts hs0 hE1 hI.A hI.t8 hI.tb hr0 hss
    rw [evo] at evs; cases evs
    have hFr := frame_step hI.Fr hCh2 ks0 hO1
    rcases hout with ⟨v', vs', rfl, hr1, -⟩ | ⟨st', ws, rfl, hr1, hst⟩
    · simp only at hrun; cases hrun
    · simp only at hrun
      simp only [hr1]
      have kst := (ev_ok hC ts _ hE1.ty).2.2 st' evo
      obtain ⟨sk', hsk, kst⟩ := kst
      cases hsk
      have hst_len : st'.length = sk.length := by rw [← kst, kOf_length]
      have hl1 := hE1.len
      simp only [List.length_cons, List.length_append, List.length_map, List.length_replicate] at hl1
      have hss2 : setSlots (.w (UInt64.ofNat N) :: tl) 1 st' =
          .ok ((.w (UInt64.ofNat N) :: tl).take 1 ++ st' ++ (.w (UInt64.ofNat N) :: tl).drop (1 + st'.length)) := by
        simp only [setSlots]; rw [if_pos (by simp; omega)]
      have hA' : ArgsR σ2 (OwnSpec.stD oc.K (1 + sk.length)) st' ws := by rw [← hnpw]; exact hst.1
      have hEn := envI_cont (F := List.replicate (1 + sk.length + m) false) (ew1 := decE ew) hlen hE1.ty
        (by simp [hdec]) kst hA'
      rw [show K.p - 1 = sk.length by omega]
      have hw0 : setW (decE ew) 1 sk.length ws 0 = UInt64.ofNat N := by rw [setW_out _ _ _ _ _ (by omega), hdec]
      have hIn : LI σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none)
          (List.replicate (1 + sk.length + m) false) K.hb K.κ σ2 r1.2
          ((.w (UInt64.ofNat N) :: tl).take 1 ++ st' ++ (.w (UInt64.ofNat N) :: tl).drop (1 + st'.length))
          (setW (decE ew) 1 sk.length ws) := by
        refine ⟨hEn, hA2, h82, hb2, hI.G.trans hG2, hFr, fun j l kj k1 ej => ?_⟩
        have hj1 : j < 1 + sk.length := by
          obtain ⟨kd, h⟩ := kj
          rw [loopΓ_get] at h
          by_cases a : j = 0
          · omega
          · rw [if_neg a] at h
            by_cases b : j < 1 + sk.length
            · exact b
            · rw [if_neg b] at h; split at h <;> simp at h
        rcases j with _ | i
        · simp at ej
        · have hi : i < sk.length := by omega
          have es' : st'[i]? = some (.b l) := by
            rw [show i + 1 = 1 + i by omega, ss_in (by simp; omega) (by omega)] at ej; exact ej
          have hw : ws.length = sk.length := by
            have := hA'.2.1; rw [this]; simp [OwnSpec.stD]; omega
          have wi : setW (decE ew) 1 sk.length ws (i + 1) = ws[i]'(by omega) := by
            rw [show i + 1 = 1 + i by omega, setW_in _ _ _ _ _ hi, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show i < ws.length by omega)]; rfl
          rw [wi]
          have pi := stD_get (Kk := oc.K) (npw := 1 + sk.length) (i := i) (by omega) (by omega)
          rw [show 1 + i = i + 1 by omega, k1] at pi
          simp only [show (1 : Nat) ≠ 2 by decide, if_false] at pi
          by_cases hs : (σ (ws[i]'(by omega)).toNat).isSome
          · obtain ⟨j', l', kj', cj', ej', wj'⟩ := hst.2.1 i l _ (by rw [← hnpw] at pi; exact pi) es'
              (List.getElem?_eq_getElem _) hs
            rw [← wj']
            exact hO1 j' l' kj' (cons_owned ks0 cj') ej'
          · left
            cases h0 : σ0 (ws[i]'(by omega)).toNat with
            | none => rfl
            | some _ => exact absurd (hI.G _ (by rw [h0]; rfl)) hs
      rw [hss2] at hrun
      exact ih σ2 r1.2 _ _ hIn (by rw [hw0]; exact toNat_ofNat_lt (by have := (ew 0).toNat_lt; omega))
          (by simp [hw0]) hrun

end NanoMain

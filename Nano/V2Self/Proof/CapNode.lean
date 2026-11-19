/- Opus box E: the node theorem at the capacity exit (`runVCap` / `runTCap` / `runLCap`): for every node Gen compiles,
the kinded semantics failing with `cap` means the node's code reaches the cap stub (word 6) with `IG`. -/
import Nano.V2Self.Proof.RoomRun
import Nano.V2Self.Proof.EVSRun
namespace Templates
open CallProbe SimW SafeRun ParSpec

theorem leafF_ne {fk : Fail} (hr : fk ≠ .room) (V : Env → UInt64) (env : Env) (sp : Nat) (H : Hp) :
    leafF V env sp H ≠ .error fk := by
  unfold leafF; split <;> simp; exact fun e => hr e.symm

theorem localF_ne {fk : Fail} (hr : fk ≠ .room) : ∀ (w k : Nat) (env : Env) (sp : Nat) (H : Hp), localF k w env sp H ≠ .error fk
  | 0, k, env, sp, H => by simp [localF, nilF]
  | w + 1, k, env, sp, H => by
    simp only [localF, pairF]
    intro h
    rcases bind_cap h with h1 | ⟨r, _, h2⟩
    · exact leafF_ne hr _ _ _ _ h1
    rcases bind_cap h2 with h3 | ⟨_, _, h4⟩
    · exact localF_ne hr w (k + 1) env _ _ h3
    · simp at h4

theorem localF_stable : ∀ (w k : Nat) (env env' : Env) (sp : Nat) (H : Hp), (∀ j, k ≤ j ∧ j < k + w → env j = env' j) →
    localF k w env sp H = localF k w env' sp H
  | 0, k, env, env', sp, H, _ => rfl
  | w + 1, k, env, env', sp, H, h => by
    simp only [localF, pairF, leafF]
    rw [h k ⟨Nat.le_refl _, by omega⟩]
    split
    · simp only [Except.bind]
      rw [localF_stable w (k + 1) env env' _ _ (fun j hj => h j ⟨by omega, by omega⟩)]
    · rfl

/-- BPUSH for any kind: `cap` is its full-buffer exit (word 6), it never fails with `room` -/
theorem fin2_bpushK {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {q : Nat} {Inv G : St → Prop} {hb E0 pI : Nat}
    (hk : fk ≠ .stuck) (t6 : fk = .cap → tg = 6) (hI : InvOKH hb pI Inv) (hG : ∀ s, Inv s → G s)
    (hC : At C q (bpushT 6 q)) (h6 : 6 < C.length) (hC18 : C.length < 2 ^ 18) (he : E0 < 2 ^ 62) :
    Fin2CapS fk tg KL C q Inv G hb E0 (bpushFF hb) := by
  cases fk with
  | cap => rw [t6 rfl]; exact fin2Cap_bpush hI hG hC h6 hC18 he
  | stuck => exact absurd rfl hk
  | room =>
    intro s2 H2 _ _ _ _ _ _ h
    exfalso; revert h; unfold bpushFF; split
    · simp
    · split
      · exact ofO_ne_cap (by decide) _
      · simp

/-- the capacity side of the global facts: callees' kinded semantics and their cap contracts -/
structure CapCx (fk : Fail) (tg : Nat) (K : SC) (C : List J) (IG : St → Prop) (E0 : Nat) (fsX : Nat → SemDX) (KL : LayW) : Prop where
  hf : ∀ n, K.fs n = oD (fsX n)
  defs : ∀ id, id < K.nd → CapD fk tg KL C (K.T id) (K.npwOf id) IG K.hb E0 (fsX id)
  h6 : 6 < C.length
  hk : fk ≠ .stuck
  t1 : fk = .room → tg = 1
  kap : K.κ < 2 ^ 40
  hb2k : 2048 ≤ K.hb
  t6 : fk = .cap → tg = 6

section runCap
variable {K : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW} {fsX : Nat → SemDX} {fk : Fail}
  {tg : Nat}

theorem ovS (Y : CapCx fk tg K C IG E0 fsX KL) (e : Nd) : oW (svF K fsX e) = sv K e := oW_sv K fsX Y.hf e
theorem otS (Y : CapCx fk tg K C IG E0 fsX KL) (e : Nd) : oT (stF K fsX e) = st K e := oT_st K fsX Y.hf e
theorem olS (Y : CapCx fk tg K C IG E0 fsX KL) (cs : List Nd) : oW (svLF K fsX cs) = svL K cs := oW_svL K fsX Y.hf cs

mutual
theorem runVCap (X : RunCxS K C IG E0 c28 KL) (Y : CapCx fk tg K C IG E0 fsX KL) :
    ∀ (e : Nd) (h : Nat), OkV K e → OpV e → At C h (tm K e h) → h + lnV K e < C.length →
    CapW fk tg KL C h K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rd e) (svF K fsX e)
  | .const v, h, _, _, hC, hl => by
    simp only [tm, lnV, rd, svF] at hC hl ⊢
    have h6 := Y.h6
    cases fk with
    | cap => exact noCap (leafF_ne (by decide) _) (fun _ _ _ _ _ => rfl)
    | stuck => exact absurd rfl Y.hk
    | room => rw [Y.t1 rfl]; exact constRoom X.hI (fun _ q => q.1) hC (by omega) X.c18 (by omega)
  | .loc s w, h, hok, _, hC, hl => by
    simp only [tm, lnV, rd, svF, OkV] at hok hC hl ⊢
    have h6 := Y.h6
    cases fk with
    | cap => exact noCap (localF_ne (by decide) w s) (fun env env' sp H hk => localF_stable w s env env' sp H hk)
    | stuck => exact absurd rfl Y.hk
    | room => rw [Y.t1 rfl]; exact localRoom X.hI (fun _ q => q.1) X.p20 X.nl251 (by omega) X.c18 w s h hok hC (by omega)
  | .bin op a b, h, hok, hop, hC, hl => by
    have hS := runVS X (.bin op a b) h hok hop hC hl
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl hS ⊢
    obtain ⟨oa, ob, wa, wb, sc⟩ := hok
    obtain ⟨op1, op2, pa, pb⟩ := hop
    obtain ⟨ca, cb, cu⟩ := At.mid hC
    rw [tm_len] at cb cu; rw [tm_len] at cu
    have hA := (runVS X a h oa pa ca (by omega)).wid wa
    have hB := (runVS X b _ ob pb cb (by omega)).wid wb
    have hP := (pairXS hA hB sc).wid (show 1 + 1 = 2 from rfl)
    rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
    rw [← ovS Y a] at hA
    have cP := pairCap hA (runVCap X Y a h oa pa ca (by omega)) (runVCap X Y b _ ob pb cb (by omega)) sc
    exact fin2Cap hP cP (fin2Cap_ofO Y.hk _)
  | .ite c a b t e, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, ob, ot, oe, wa, wb, we, sb, st', se⟩ := hok
    obtain ⟨pa, pb, pt, pe⟩ := hop
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cE
    have hA := (runVS X a h oa pa cA (by omega)).wid wa
    have hB := (runVS X b _ ob pb cB (by omega)).wid wb
    have hP := (pairXS hA hB sb).wid (show 1 + 1 = 2 from rfl)
    rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
    rw [← ovS Y a] at hA
    have cP := pairCap hA (runVCap X Y a h oa pa cA (by omega)) (runVCap X Y b _ ob pb cB (by omega)) sb
    have cT' := (runVCap X Y t _ ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega)).pcEq
      (show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega)
    have cE' := (runVCap X Y e _ oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnV K t by omega))
      (by omega)).pcEq (show h + lnV K a + lnV K b + 6 + lnV K t = h + (lnV K a + lnV K b) + 6 + lnV K t by omega)
    exact ifCap X.hI hP cP (At.cast cH (by omega)) cT' cE' st' se (by omega) X.c18
  | .letE s w v b, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have hv := (runVS X v h ov hop.1 cv (by omega)).wid wv
    rw [← ovS Y v] at hv
    exact letCap X.hI hv (runVCap X Y v h ov hop.1 cv (by omega)) cs (runVCap X Y b _ ob hop.2 cb (by omega))
      hk0 sc X.nl251
  | .pair cs, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢; exact runLCap X Y cs h hok hop hC hl
  | .call id as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, hid, wa⟩ := hok
    have hA := (runLS X as h oa hop hC.left (by omega)).wid wa
    rw [← olS Y as] at hA
    have hj := At.one hC.right
    rw [tmL_len] at hj
    exact callCap X.ig hA (runLCap X Y as h oa hop hC.left (by omega)) hj (by omega) (Y.defs id hid) X.e62
      (fun s hs => by have := X.cb s hs; omega) (X.tl id hid) X.c18
  | .prim pn as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, wa, h0⟩ := hok
    have hP := runLS X as h oa hop hC.left (by have := primT_len K pn 0; unfold primLen at hl; split at hl <;> omega)
    have cP := runLCap X Y as h oa hop hC.left (by have := primT_len K pn 0; unfold primLen at hl; split at hl <;> omega)
    rw [← olS Y as] at hP
    have hU := hC.right
    rw [tmL_len] at hU
    unfold primT at hU
    unfold arity at wa
    by_cases p13 : pn = 1 ∨ pn = 3
    · have := h0 (p13.elim Or.inl (fun q => Or.inr (Or.inl q))); subst this
      simp only [p13, if_true] at hU ⊢
      have h6 := Y.h6
      cases fk with
      | cap => exact noCap (leafF_ne (by decide) _) (fun _ _ _ _ _ => rfl)
      | stuck => exact absurd rfl Y.hk
      | room =>
        rw [Y.t1 rfl]
        exact lenRoom X.hI (fun _ q => q.1) (by simpa [lnL] using hU) (by omega) X.c18
          (by unfold primLen at hl; simp [lnL, p13] at hl ⊢; omega)
    simp only [p13, if_false] at hU ⊢
    by_cases p5 : pn = 5
    · have := h0 (Or.inr (Or.inr p5)); subst this
      simp only [p5, if_true] at hU ⊢
      have h6 := Y.h6
      cases fk with
      | cap =>
        refine noCap (fun env sp H => ?_) (fun _ _ _ _ _ => rfl)
        simp only [oneF, bnewF]; intro h; have := map_cap h; cases e : bnewS K.κ env sp H <;> simp [e, ofO] at this
      | stuck => exact absurd rfl Y.hk
      | room =>
        rw [Y.t1 rfl]
        exact bnewRoom X.hI (fun _ q => q.1) (by simpa [lnL] using hU) Y.kap X.e62 (by omega) X.c18
          (by
            have e := bnewT_len 1 0 K.κ; have e' := bnewT_len 1 h K.κ
            unfold primLen at hl; rw [if_neg (by omega), if_pos p5] at hl; simp only [lnL] at hl ⊢; omega)
    simp only [p5, if_false] at hU ⊢
    have n135 : ¬ (pn = 1 ∨ pn = 3 ∨ pn = 5) := by omega
    simp only [n135, if_false] at wa
    by_cases p26 : pn = 2 ∨ pn = 6
    · simp only [p26, if_true] at wa ⊢
      exact fin1Cap (hP.wid wa) cP Y.hk
    simp only [p26, if_false] at wa ⊢
    have n2 : pn ≠ 2 := by omega
    have n6 : pn ≠ 6 := by omega
    simp only [n2, n6, if_false] at hU ⊢
    by_cases p8 : pn = 8
    · simp only [p8, if_true] at wa hU ⊢
      exact fin3Cap (hP.wid wa) cP Y.hk
    simp only [p8, if_false] at wa hU ⊢
    unfold primF2F
    by_cases p7 : pn = 7
    · simp only [p7, if_true] at hU ⊢
      exact fin2Cap (hP.wid wa) cP (fin2Cap_ofO Y.hk _)
    · simp only [p7, if_false] at hU ⊢
      exact fin2Cap (hP.wid wa) cP (fin2_bpushK Y.hk Y.t6 X.hI (fun _ q => q.1) hU Y.h6 X.c18 X.e62)
  | .loop z s, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oz, os, hp, hpn, hWp, hsc⟩ := hok
    have cH := hC.left.left.left
    have cZ := hC.left.left.right
    have cD := hC.left.right
    have cS := hC.right
    simp only [List.length_append, tmT_len, loopHead, loopDec, List.length_cons, List.length_nil] at cZ cD cS
    have hS := runTS X s _ _ _ _ os hop.2 (At.cast cS (show _ = h + 3 + lnT K z + 2 by omega)) (by omega) (by omega)
      (by omega)
    rw [← otS Y s] at hS
    have cZ' := runTCap X Y z _ _ _ _ oz hop.1 (At.cast cZ (show _ = h + 3 by omega)) (by omega) (by omega) (by omega)
    have cS' := runTCap X Y s _ _ _ _ os hop.2 (At.cast cS (show _ = h + 3 + lnT K z + 2 by omega)) (by omega)
      (by omega) (by omega)
    exact loopWCap X.hI cH (At.cast cD (by omega)) hS cZ' cS' Y.hk hp hpn hWp hsc X.nl251 (by omega) (by omega) X.c18
  | .cont _, _, hok, _, _, _ => by simp only [OkV] at hok
termination_by e => 2 * sizeOf e
theorem runTCap (X : RunCxS K C IG E0 c28 KL) (Y : CapCx fk tg K C IG E0 fsX KL) :
    ∀ (e : Nd) (h Xt Hd w : Nat), OkT K e w → OpV e →
    At C h (tmT K e h Xt Hd) → h + lnT K e ≤ C.length → Xt < C.length → Hd < C.length →
    CapT fk tg KL C h K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rd e) (stF K fsX e)
  | .ite c a b t e, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨oa, ob, ot, oe, wa, wb, sb, st', se⟩ := hok
    obtain ⟨pa, pb, pt, pe⟩ := hop
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, tmT_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cE
    have l1 := lnT_pos K e
    have hA := (runVS X a h oa pa cA (by omega)).wid wa
    have hB := (runVS X b _ ob pb cB (by omega)).wid wb
    have hP := (pairXS hA hB sb).wid (show 1 + 1 = 2 from rfl)
    rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
    rw [← ovS Y a] at hA
    have cP := pairCap hA (runVCap X Y a h oa pa cA (by omega)) (runVCap X Y b _ ob pb cB (by omega)) sb
    have cT' := (runTCap X Y t _ Xt Hd w ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega)
      hX hH).pcEq (show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega)
    have cE' := (runTCap X Y e _ Xt Hd w oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnT K t by omega))
      (by omega) hX hH).pcEq (show h + lnV K a + lnV K b + 6 + lnT K t = h + (lnV K a + lnV K b) + 6 + lnT K t by omega)
    exact ifTCap X.hI hP cP (At.cast cH (by omega)) cT' cE' st' se (by omega) X.c18
  | .letE s w' v b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have l1 := lnT_pos K b
    have hv := (runVS X v h ov hop.1 cv (by omega)).wid wv
    rw [← ovS Y v] at hv
    exact letTCap X.hI hv (runVCap X Y v h ov hop.1 cv (by omega)) cs
      (runTCap X Y b _ Xt Hd w ob hop.2 cb (by omega) hX hH) hk0 sc X.nl251
  | .cont e, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨oe, we, hp, hpn⟩ := hok
    obtain ⟨ce, cs, cj⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cj
    exact contCap (runVCap X Y e h oe hop ce (by omega))
  | .const v, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .loc s' w', h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .bin op a b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .pair cs, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .call id as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .prim pn as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
  | .loop z s, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact exitCap (runVCap X Y _ h hok.1 hop hC.left (by omega))
termination_by e => 2 * sizeOf e + 1
theorem runLCap (X : RunCxS K C IG E0 c28 KL) (Y : CapCx fk tg K C IG E0 fsX KL) :
    ∀ (cs : List Nd) (h : Nat), OkL K cs → OpL cs → At C h (tmL K cs h) → h + lnL K cs < C.length →
    CapW fk tg KL C h K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rdL cs) (svLF K fsX cs)
  | [], h, _, _, _, _ => by
    simp only [rdL, svLF]; exact noCap (fun _ _ _ => by simp [nilF]) (fun _ _ _ _ _ => rfl)
  | c :: cs, h, hok, hop, hC, hl => by
    simp only [tmL, lnL, rdL, wrL, wdL, svLF, OkL, OpL] at hok hop hC hl ⊢
    obtain ⟨oc, ocs, sc⟩ := hok
    have h1 := runVS X c h oc hop.1 hC.left (by omega)
    rw [← ovS Y c] at h1
    exact pairCap h1 (runVCap X Y c h oc hop.1 hC.left (by omega))
      (runLCap X Y cs (h + lnV K c) ocs hop.2 (by have := hC.right; rwa [tm_len] at this) (by omega)) sc
termination_by cs => 2 * sizeOf cs
end

end runCap

end Templates

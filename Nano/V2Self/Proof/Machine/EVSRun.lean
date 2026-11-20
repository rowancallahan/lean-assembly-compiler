/- Safe retrofit (EVS) P6: the node theorem with SafeX runs (Opus box E): `runVS` / `runTS` / `runLS`, by induction
on the node, over the safe contracts (side conditions `OkV`/`OkT`/`OkL` from NdRun).  Extra per-node premises: `OpV` (Gen's BIN op range, exported from CG) and
"the node's code ends inside C" (the epilogue follows every body).  Global facts: `RunCxS`. -/
import Nano.V2Self.Proof.Machine.EVSCall
import Nano.V2Self.Proof.Machine.EVSLoop
import Nano.V2Self.Proof.Machine.NdRun
import Nano.V2Self.Proof.Machine.NdCG
namespace Templates
open CallProbe SimW SafeRun ParSpec

/-- the global facts of the safe node theorem -/
structure RunCxS (K : SC) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (KL : LayW) : Prop where
  ig : IGOK K.hb E0 IG
  e62 : E0 < 2 ^ 62
  cb : ∀ s, IG s → s.b + s.w * C.length < 2 ^ 64
  p20 : K.p < 2 ^ 20
  inp : InpOK IG c28 K.c29 K.inp
  inw : InpW KL IG
  nl251 : K.nl < 251
  c18 : C.length < 2 ^ 18
  defs : ∀ id, id < K.nd → DefXS KL C (K.T id) (K.npwOf id) (K.nresOf id) IG K.hb E0 (K.fs id)
  tl : ∀ id, id < K.nd → K.T id < C.length

theorem RunCxS.hI {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InvOKH K.hb K.p (IGp IG E0 K.p) :=
  invOKH_IGp h.ig K.p

theorem RunCxS.inpP {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InpOK (IGp IG E0 K.p) c28 K.c29 K.inp :=
  fun s hs => h.inp s hs.1

theorem RunCxS.inwP {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InpW KL (IGp IG E0 K.p) :=
  fun s hs => h.inw s hs.1

theorem lnT_pos (K : SC) : ∀ e : Nd, 1 ≤ lnT K e
  | .ite _ _ _ _ e => by have := lnT_pos K e; simp only [lnT]; omega
  | .letE _ _ _ b => by have := lnT_pos K b; simp only [lnT]; omega
  | .cont _ => by simp only [lnT]; omega
  | .const _ => by simp only [lnT]; omega
  | .loc _ _ => by simp only [lnT]; omega
  | .bin _ _ _ => by simp only [lnT]; omega
  | .pair _ => by simp only [lnT]; omega
  | .call _ _ => by simp only [lnT]; omega
  | .prim _ _ => by simp only [lnT]; omega
  | .loop _ _ => by simp only [lnT]; omega

section runS
variable {K : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW}

mutual
theorem runVS (X : RunCxS K C IG E0 c28 KL) : ∀ (e : Nd) (h : Nat), OkV K e → OpV e → At C h (tm K e h) →
    h + lnV K e < C.length →
    EVHwS KL C h (lnV K e) K.p K.nl (IGp IG E0 K.p) K.hb E0 (rd e) (wr K.p e) (wd K e) (sv K e)
  | .const v, h, _, _, hC, _ => by
    simp only [tm, lnV, rd, wr, wd, sv] at hC ⊢; exact constX X.hI hC
  | .loc s w, h, hok, _, hC, _ => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV] at hok hC ⊢; exact localX X.hI X.p20 X.nl251 w s h hok hC
  | .bin op a b, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, ob, wa, wb, sc⟩ := hok
    obtain ⟨op1, op2, pa, pb⟩ := hop
    obtain ⟨ca, cb, cu⟩ := At.mid hC
    rw [tm_len] at cb cu; rw [tm_len] at cu
    have hA := (runVS X a h oa pa ca (by omega)).wid wa
    have hB := (runVS X b _ ob pb cb (by omega)).wid wb
    have hP := (pairX hA hB sc).wid (show 1 + 1 = 2 from rfl)
    exact fin2X X.hI hP (fin2_alu (by rwa [← Nat.add_assoc]) ⟨op1, op2⟩)
  | .ite c a b t e, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, ob, ot, oe, wa, wb, we, sb, st', se⟩ := hok
    obtain ⟨pa, pb, pt, pe⟩ := hop
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cJ := At.one hC.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cJ cE
    have hA := (runVS X a h oa pa cA (by omega)).wid wa
    have hB := (runVS X b _ ob pb cB (by omega)).wid wb
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have hT := runVS X t _ ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega)
    have hE := (runVS X e _ oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnV K t by omega))
      (by omega)).wid we
    rw [show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega] at hT
    rw [show h + lnV K a + lnV K b + 6 + lnV K t = h + (lnV K a + lnV K b) + 6 + lnV K t by omega] at hE
    exact ifX X.hI hP (At.cast cH (by omega)) hT (by rw [← cJ]; congr 1; omega) hE st' se (by omega) X.c18
  | .letE s w v b, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have hv := (runVS X v h ov hop.1 cv (by omega)).wid wv
    have hb := runVS X b _ ob hop.2 cb (by omega)
    exact letX X.hI hv cs hb hk0 sc X.nl251
  | .pair cs, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢; exact runLS X cs h hok hop hC hl
  | .call id as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, hid, wa⟩ := hok
    have hA := (runLS X as h oa hop hC.left (by omega)).wid wa
    have hj := At.one hC.right
    rw [tmL_len] at hj
    exact callXS X.ig hA hj (by omega) (X.defs id hid) X.e62
      (fun s hs => by
        have := X.cb s hs; have := Nat.mul_le_mul_left s.w (show h + lnL K as + 1 ≤ C.length by omega); omega)
      (X.tl id hid) X.c18
  | .prim pn as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, wa, h0⟩ := hok
    have hP := runLS X as h oa hop hC.left (by have := primT_len K pn 0; unfold primLen at hl; split at hl <;> omega)
    have hU := hC.right
    rw [tmL_len] at hU
    unfold primT at hU; unfold primLen
    unfold arity at wa
    by_cases p13 : pn = 1 ∨ pn = 3
    · have := h0 (p13.elim Or.inl (fun q => Or.inr (Or.inl q))); subst this
      simp only [p13, if_true] at hU ⊢
      simp only [lnL, rdL, wrL]
      exact (lenX (R := fun _ => False) (W := fun _ => False) X.hI (fun s hs => (X.inpP s hs).2.1)
        (by simpa [lnL] using hU)).mono (fun _ q => q.elim) (fun _ q => q.elim)
    simp only [p13, if_false] at hU ⊢
    by_cases p5 : pn = 5
    · have := h0 (Or.inr (Or.inr p5)); subst this
      simp only [p5, if_true] at hU ⊢
      simp only [lnL, rdL, wrL]
      refine ((bnewX (R := fun _ => False) (W := fun _ => False) X.hI (by simpa [lnL] using hU)).mono
        (fun _ q => q.elim) (fun _ q => q.elim)).len ?_
      simp [bnewT_len]
    simp only [p5, if_false] at hU ⊢
    have n135 : ¬ (pn = 1 ∨ pn = 3 ∨ pn = 5) := by omega
    simp only [n135, if_false] at wa
    by_cases p26 : pn = 2 ∨ pn = 6
    · simp only [p26, if_true] at wa ⊢
      unfold primF1
      by_cases p2 : pn = 2
      · simp only [p2, if_true] at hU ⊢
        exact fin1X X.hI (hP.wid wa) (fin1_rd hU X.inpP X.inwP)
      · have p6 : pn = 6 := by omega
        simp only [p6, if_true] at hU ⊢
        exact fin1X X.hI (hP.wid wa) (fin1_bsize hU)
    simp only [p26, if_false] at wa ⊢
    have n2 : pn ≠ 2 := by omega
    have n6 : pn ≠ 6 := by omega
    simp only [n2, n6, if_false] at hU ⊢
    by_cases p8 : pn = 8
    · simp only [p8, if_true] at wa hU ⊢
      exact fin3X X.hI (hP.wid wa) (fin3_bset hU)
    simp only [p8, if_false] at wa hU ⊢
    unfold primF2
    by_cases p7 : pn = 7
    · simp only [p7, if_true] at hU ⊢
      exact fin2X X.hI (hP.wid wa) (fin2_bget hU)
    · simp only [p7, if_false] at hU ⊢
      exact fin2X X.hI (hP.wid wa) (fin2_bpush hU)
  | .loop z s, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oz, os, hp, hpn, hWp, hsc⟩ := hok
    have cH := hC.left.left.left
    have cZ := hC.left.left.right
    have cD := hC.left.right
    have cS := hC.right
    simp only [List.length_append, tmT_len, loopHead, loopDec, List.length_cons, List.length_nil] at cZ cD cS
    have hZ := runTS X z _ _ _ _ oz hop.1 (At.cast cZ (show _ = h + 3 by omega)) (by omega) (by omega) (by omega)
    have hS := runTS X s _ _ _ _ os hop.2 (At.cast cS (show _ = h + 3 + lnT K z + 2 by omega)) (by omega) (by omega)
      (by omega)
    exact (loopXS X.hI cH (At.cast cD (by omega)) hZ hS hp hpn hWp hsc X.nl251 (by omega) (by omega) X.c18).mono
      (fun _ q => q) (fun k q => by rcases q with q | q | q <;> simp_all)
  | .cont _, _, hok, _, _, _ => by simp only [OkV] at hok
termination_by e => 2 * sizeOf e
theorem runTS (X : RunCxS K C IG E0 c28 KL) : ∀ (e : Nd) (h Xt Hd w : Nat), OkT K e w → OpV e →
    At C h (tmT K e h Xt Hd) → h + lnT K e ≤ C.length → Xt < C.length → Hd < C.length →
    EVHtS KL C h K.p K.nl (IGp IG E0 K.p) K.hb E0 (rd e) (wr K.p e) w Xt Hd (st K e)
  | .ite c a b t e, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, OkT, OpV] at hok hop hC ⊢
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
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have hT := runTS X t _ Xt Hd w ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega) hX hH
    have hE := runTS X e _ Xt Hd w oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnT K t by omega))
      (by omega) hX hH
    rw [show h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 by omega] at hT
    rw [show h + lnV K a + lnV K b + 6 + lnT K t = h + (lnV K a + lnV K b) + 6 + lnT K t by omega] at hE
    exact ifT X.hI hP (At.cast cH (by omega)) hT hE st' se (by omega) X.c18
  | .letE s w' v b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have l1 := lnT_pos K b
    exact letT X.hI ((runVS X v h ov hop.1 cv (by omega)).wid wv) cs
      (runTS X b _ Xt Hd w ob hop.2 cb (by omega) hX hH) hk0 sc X.nl251
  | .cont e, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨oe, we, hp, hpn⟩ := hok
    obtain ⟨ce, cs, cj⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cj
    exact contT X.hI ((runVS X e h oe hop ce (by omega)).wid we) cs (At.one cj) hp hpn X.nl251 hH (by omega) X.c18
  | .const v, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .loc s' w', h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .bin op a b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .pair cs, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .call id as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .prim pn as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
  | .loop z s, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, OkT] at hok hC ⊢; simp only [lnT] at hl
    exact valT ((runVS X _ h hok.1 hop hC.left (by omega)).wid hok.2)
      (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18
termination_by e => 2 * sizeOf e + 1
theorem runLS (X : RunCxS K C IG E0 c28 KL) : ∀ (cs : List Nd) (h : Nat), OkL K cs → OpL cs → At C h (tmL K cs h) →
    h + lnL K cs < C.length →
    EVHwS KL C h (lnL K cs) K.p K.nl (IGp IG E0 K.p) K.hb E0 (rdL cs) (wrL K.p cs) (wdL K cs) (svL K cs)
  | [], h, _, _, _, _ => by
    simp only [lnL, rdL, wrL, wdL, svL]; exact nilX.mono (fun _ h => h.elim) (fun _ h => h.elim)
  | c :: cs, h, hok, hop, hC, hl => by
    simp only [tmL, lnL, rdL, wrL, wdL, svL, OkL, OpL] at hok hop hC hl ⊢
    obtain ⟨oc, ocs, sc⟩ := hok
    have h1 := runVS X c h oc hop.1 hC.left (by omega)
    have h2 := runLS X cs (h + lnV K c) ocs hop.2 (by have := hC.right; rwa [tm_len] at this) (by omega)
    exact pairX h1 h2 sc
termination_by cs => 2 * sizeOf cs
end

end runS

end Templates

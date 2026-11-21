/- The node theorem for ALL outcomes (`runVO` / `runTO` / `runLO`): for every node Gen compiles, its code meets the
success contract (`EVHwS` / `EVHtS`, for the Option semantics `sv` / `st`) and, for every failure kind of the kinded
semantics `svF` / `stF` (cap: stub word 6, room: stub word 1), reaches that kind's stub with `IG`.  The two halves are
packaged as `EVO` / `EVOt` / `DefO` (fields `ok`, `fail`); the fragment rules stay separate (EVS* for success, CapRun /
RoomRun for failure) and are combined here, in ONE induction on the node.  Global facts: `RunCxS` (EVSRun) and `OCx`. -/
import Nano.V2Self.Proof.Machine.RoomRun
import Nano.V2Self.Proof.Machine.EVSRun
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
    Fin2Cap fk tg KL C q Inv G hb E0 (bpushFF hb) := by
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

end runCap

/-! ## the outcome contracts: success and every failure kind of one fragment -/

/-- **a value fragment, all outcomes**: `ok` — the success contract for the Option semantics `S`; `fail` — for every
failure kind of the kinded semantics `SX` (cap, room), a safe run to that kind's stub word -/
structure EVO (KL : LayW) (C : List J) (pc len p nl : Nat) (Inv G : St → Prop) (hb E0 : Nat) (R W : Nat → Prop)
    (w : Nat) (S : SemW) (SX : SemWX) : Prop where
  ok : EVHwS KL C pc len p nl Inv hb E0 R W w S
  fail : ∀ fk, fk ≠ .stuck → CapW fk (stubW fk) KL C pc p nl Inv G hb E0 R SX

/-- a tail fragment, all outcomes -/
structure EVOt (KL : LayW) (C : List J) (pc p nl : Nat) (Inv G : St → Prop) (hb E0 : Nat) (R W : Nat → Prop)
    (w X Hd : Nat) (S : SemT) (SX : SemTX) : Prop where
  ok : EVHtS KL C pc p nl Inv hb E0 R W w X Hd S
  fail : ∀ fk, fk ≠ .stuck → CapT fk (stubW fk) KL C pc p nl Inv G hb E0 R SX

/-- a def, all outcomes -/
structure DefO (KL : LayW) (C : List J) (f p q : Nat) (IG : St → Prop) (hb E0 : Nat)
    (Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) (SdX : SemDX) : Prop where
  ok : DefXS KL C f p q IG hb E0 Sd
  fail : ∀ fk, fk ≠ .stuck → CapD fk (stubW fk) KL C f p IG hb E0 SdX

/-- the failure side of the global facts, for every kind: callees' kinded semantics and their failure contracts -/
structure OCx (K : SC) (C : List J) (IG : St → Prop) (E0 : Nat) (fsX : Nat → SemDX) (KL : LayW) : Prop where
  hf : ∀ n, K.fs n = oD (fsX n)
  defs : ∀ id, id < K.nd → ∀ fk, fk ≠ .stuck → CapD fk (stubW fk) KL C (K.T id) (K.npwOf id) IG K.hb E0 (fsX id)
  h6 : 6 < C.length
  kap : K.κ < 2 ^ 40
  hb2k : 2048 ≤ K.hb

theorem OCx.cx {K : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {fsX : Nat → SemDX} {KL : LayW}
    (Y : OCx K C IG E0 fsX KL) (fk : Fail) (hk : fk ≠ .stuck) : CapCx fk (stubW fk) K C IG E0 fsX KL :=
  ⟨Y.hf, fun id h => Y.defs id h fk hk, Y.h6, hk, fun e => by subst e; rfl, Y.kap, Y.hb2k, fun e => by subst e; rfl⟩

section runO
variable {K : SC} {C : List J} {IG : St → Prop} {E0 : Nat} {c28 : UInt64} {KL : LayW} {fsX : Nat → SemDX}

/- **The node theorem, all outcomes** (`runVO` / `runTO` / `runLO`): one induction on the node; each case derives the
node's side conditions once, then gives the success contract and, for every failure kind, the failure contract. -/
mutual
theorem runVO (X : RunCxS K C IG E0 c28 KL) (Y0 : OCx K C IG E0 fsX KL) :
    ∀ (e : Nd) (h : Nat), OkV K e → OpV e → At C h (tm K e h) → h + lnV K e < C.length →
    EVO KL C h (lnV K e) K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rd e) (wr K.p e) (wd K e) (sv K e) (svF K fsX e)
  | .const v, h, _, _, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF] at hC hl ⊢
    refine ⟨constX X.hI hC, fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    have h6 := Y.h6
    cases fk with
    | cap => exact noCap (leafF_ne (by decide) _) (fun _ _ _ _ _ => rfl)
    | stuck => exact absurd rfl Y.hk
    | room => rw [Y.t1 rfl]; exact constRoom X.hI (fun _ q => q.1) hC (by omega) X.c18 (by omega)
  | .loc s w, h, hok, _, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV] at hok hC hl ⊢
    refine ⟨localX X.hI X.p20 X.nl251 w s h hok hC, fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    have h6 := Y.h6
    cases fk with
    | cap => exact noCap (localF_ne (by decide) w s) (fun env env' sp H hk => localF_stable w s env env' sp H hk)
    | stuck => exact absurd rfl Y.hk
    | room => rw [Y.t1 rfl]; exact localRoom X.hI (fun _ q => q.1) X.p20 X.nl251 (by omega) X.c18 w s h hok hC (by omega)
  | .bin op a b, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, ob, wa, wb, sc⟩ := hok
    obtain ⟨op1, op2, pa, pb⟩ := hop
    obtain ⟨ca, cb, cu⟩ := At.mid hC
    rw [tm_len] at cb cu; rw [tm_len] at cu
    have rA := runVO X Y0 a h oa pa ca (by omega)
    have rB := runVO X Y0 b _ ob pb cb (by omega)
    have hA := rA.ok.wid wa
    have hB := rB.ok.wid wb
    have hP := (pairX hA hB sc).wid (show 1 + 1 = 2 from rfl)
    refine ⟨fin2X X.hI hP (fin2_alu (by rwa [← Nat.add_assoc]) ⟨op1, op2⟩), fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
    rw [← ovS Y a] at hA
    exact fin2Cap hP (pairCap hA (rA.fail fk hk) (rB.fail fk hk) sc) (fin2Cap_ofO Y.hk _)
  | .ite c a b t e, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, ob, ot, oe, wa, wb, we, sb, st', se⟩ := hok
    obtain ⟨pa, pb, pt, pe⟩ := hop
    have cA := hC.left.left.left.left.left
    have cB := hC.left.left.left.left.right
    have cH := hC.left.left.left.right
    have cT := hC.left.left.right
    have cJ := At.one hC.left.right
    have cE := hC.right
    simp only [List.length_append, tm_len, ifHeadG, List.length_cons, List.length_nil] at cB cH cT cJ cE
    have rA := runVO X Y0 a h oa pa cA (by omega)
    have rB := runVO X Y0 b _ ob pb cB (by omega)
    have rT := runVO X Y0 t _ ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega)
    have rE := runVO X Y0 e _ oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnV K t by omega)) (by omega)
    have hA := rA.ok.wid wa
    have hB := rB.ok.wid wb
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have e5 : h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 := by omega
    have e6 : h + lnV K a + lnV K b + 6 + lnV K t = h + (lnV K a + lnV K b) + 6 + lnV K t := by omega
    refine ⟨?_, fun fk hk => ?_⟩
    · have hT := rT.ok
      have hE := rE.ok.wid we
      rw [e5] at hT; rw [e6] at hE
      exact ifX X.hI hP (At.cast cH (by omega)) hT (by rw [← cJ]; congr 1; omega) hE st' se (by omega) X.c18
    · have Y := Y0.cx fk hk
      rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
      rw [← ovS Y a] at hA
      exact ifCap X.hI hP (pairCap hA (rA.fail fk hk) (rB.fail fk hk) sb) (At.cast cH (by omega))
        ((rT.fail fk hk).pcEq e5) ((rE.fail fk hk).pcEq e6) st' se (by omega) X.c18
  | .letE s w v b, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have rv := runVO X Y0 v h ov hop.1 cv (by omega)
    have rb := runVO X Y0 b _ ob hop.2 cb (by omega)
    have hv := rv.ok.wid wv
    refine ⟨letX X.hI hv cs rb.ok hk0 sc X.nl251, fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    rw [← ovS Y v] at hv
    exact letCap X.hI hv (rv.fail fk hk) cs (rb.fail fk hk) hk0 sc X.nl251
  | .pair cs, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢; exact runLO X Y0 cs h hok hop hC hl
  | .call id as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, hid, wa⟩ := hok
    have rA := runLO X Y0 as h oa hop hC.left (by omega)
    have hA := rA.ok.wid wa
    have hj := At.one hC.right
    rw [tmL_len] at hj
    have hcb : ∀ s, IG s → s.b + s.lo (h + lnL K as + 1) < 2 ^ 64 := fun s hs => X.cb s hs _ _ hj
    refine ⟨callXS X.ig hA hj (by omega) (X.defs id hid) X.e62 hcb (X.tl id hid) X.c18, fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    rw [← olS Y as] at hA
    exact callCap X.ig hA (rA.fail fk hk) hj (by omega) (Y.defs id hid) X.e62 hcb (X.tl id hid) X.c18
  | .prim pn as, h, hok, hop, hC, hl => by
    simp only [tm, lnV, rd, wr, wd, sv, svF, OkV, OpV] at hok hop hC hl ⊢
    obtain ⟨oa, wa, h0⟩ := hok
    have rP := runLO X Y0 as h oa hop hC.left
      (by have := primT_len K pn 0; unfold primLen at hl; split at hl <;> omega)
    have hP := rP.ok
    have hU := hC.right
    rw [tmL_len] at hU
    unfold primT at hU
    unfold arity at wa
    refine ⟨?_, fun fk hk => ?_⟩
    · unfold primLen
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
    · have Y := Y0.cx fk hk
      have cP := rP.fail fk hk
      rw [← olS Y as] at hP
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
    have rZ := runTO X Y0 z _ _ _ _ oz hop.1 (At.cast cZ (show _ = h + 3 by omega)) (by omega) (by omega) (by omega)
    have rS := runTO X Y0 s _ _ _ _ os hop.2 (At.cast cS (show _ = h + 3 + lnT K z + 2 by omega)) (by omega) (by omega)
      (by omega)
    refine ⟨(loopXS X.hI cH (At.cast cD (by omega)) rZ.ok rS.ok hp hpn hWp hsc X.nl251 (by omega) (by omega) X.c18).mono
      (fun _ q => q) (fun k q => by rcases q with q | q | q <;> simp_all), fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    have hS := rS.ok
    rw [← otS Y s] at hS
    exact loopWCap X.hI cH (At.cast cD (by omega)) hS (rZ.fail fk hk) (rS.fail fk hk) Y.hk hp hpn hWp hsc X.nl251
      (by omega) (by omega) X.c18
  | .cont _, _, hok, _, _, _ => by simp only [OkV] at hok
termination_by e => 2 * sizeOf e
theorem runTO (X : RunCxS K C IG E0 c28 KL) (Y0 : OCx K C IG E0 fsX KL) :
    ∀ (e : Nd) (h Xt Hd w : Nat), OkT K e w → OpV e →
    At C h (tmT K e h Xt Hd) → h + lnT K e ≤ C.length → Xt < C.length → Hd < C.length →
    EVOt KL C h K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rd e) (wr K.p e) w Xt Hd (st K e) (stF K fsX e)
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
    have rA := runVO X Y0 a h oa pa cA (by omega)
    have rB := runVO X Y0 b _ ob pb cB (by omega)
    have rT := runTO X Y0 t _ Xt Hd w ot pt (At.cast cT (show _ = h + lnV K a + lnV K b + 5 by omega)) (by omega) hX hH
    have rE := runTO X Y0 e _ Xt Hd w oe pe (At.cast cE (show _ = h + lnV K a + lnV K b + 6 + lnT K t by omega))
      (by omega) hX hH
    have hA := rA.ok.wid wa
    have hB := rB.ok.wid wb
    have hP := (pairX hA hB sb).wid (show 1 + 1 = 2 from rfl)
    have e5 : h + lnV K a + lnV K b + 5 = h + (lnV K a + lnV K b) + 5 := by omega
    have e6 : h + lnV K a + lnV K b + 6 + lnT K t = h + (lnV K a + lnV K b) + 6 + lnT K t := by omega
    refine ⟨?_, fun fk hk => ?_⟩
    · have hT := rT.ok
      have hE := rE.ok
      rw [e5] at hT; rw [e6] at hE
      exact ifT X.hI hP (At.cast cH (by omega)) hT hE st' se (by omega) X.c18
    · have Y := Y0.cx fk hk
      rw [← ovS Y a, ← ovS Y b, ← oW_pair] at hP
      rw [← ovS Y a] at hA
      exact ifTCap X.hI hP (pairCap hA (rA.fail fk hk) (rB.fail fk hk) sb) (At.cast cH (by omega))
        ((rT.fail fk hk).pcEq e5) ((rE.fail fk hk).pcEq e6) st' se (by omega) X.c18
  | .letE s w' v b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨ov, ob, wv, hk0, sc⟩ := hok
    obtain ⟨cv, cs, cb⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cb
    have l1 := lnT_pos K b
    have rv := runVO X Y0 v h ov hop.1 cv (by omega)
    have rb := runTO X Y0 b _ Xt Hd w ob hop.2 cb (by omega) hX hH
    have hv := rv.ok.wid wv
    refine ⟨letT X.hI hv cs rb.ok hk0 sc X.nl251, fun fk hk => ?_⟩
    have Y := Y0.cx fk hk
    rw [← ovS Y v] at hv
    exact letTCap X.hI hv (rv.fail fk hk) cs (rb.fail fk hk) hk0 sc X.nl251
  | .cont e, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT, OpV] at hok hop hC ⊢
    simp only [lnT] at hl
    obtain ⟨oe, we, hp, hpn⟩ := hok
    obtain ⟨ce, cs, cj⟩ := At.mid hC
    simp only [tm_len, popN_len] at cs cj
    have re := runVO X Y0 e h oe hop ce (by omega)
    exact ⟨contT X.hI (re.ok.wid we) cs (At.one cj) hp hpn X.nl251 hH (by omega) X.c18,
      fun fk hk => contCap (re.fail fk hk)⟩
  | .const v, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .loc s' w', h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, rd, wr, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .bin op a b, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .pair cs, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .call id as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .prim pn as, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
  | .loop z s, h, Xt, Hd, w, hok, hop, hC, hl, hX, hH => by
    simp only [tmT, st, stF, OkT] at hok hC ⊢; simp only [lnT] at hl
    have r := runVO X Y0 _ h hok.1 hop hC.left (by omega)
    exact ⟨valT (r.ok.wid hok.2) (by have hj := At.one hC.right; rwa [tm_len] at hj) hX (by omega) X.c18,
      fun fk hk => exitCap (r.fail fk hk)⟩
termination_by e => 2 * sizeOf e + 1
theorem runLO (X : RunCxS K C IG E0 c28 KL) (Y0 : OCx K C IG E0 fsX KL) :
    ∀ (cs : List Nd) (h : Nat), OkL K cs → OpL cs → At C h (tmL K cs h) → h + lnL K cs < C.length →
    EVO KL C h (lnL K cs) K.p K.nl (IGp IG E0 K.p) IG K.hb E0 (rdL cs) (wrL K.p cs) (wdL K cs) (svL K cs)
      (svLF K fsX cs)
  | [], h, _, _, _, _ => by
    simp only [lnL, rdL, wrL, wdL, svL, svLF]
    exact ⟨nilX.mono (fun _ h => h.elim) (fun _ h => h.elim),
      fun fk hk => noCap (fun _ _ _ => by simp [nilF]) (fun _ _ _ _ _ => rfl)⟩
  | c :: cs, h, hok, hop, hC, hl => by
    simp only [tmL, lnL, rdL, wrL, wdL, svL, svLF, OkL, OpL] at hok hop hC hl ⊢
    obtain ⟨oc, ocs, sc⟩ := hok
    have r1 := runVO X Y0 c h oc hop.1 hC.left (by omega)
    have r2 := runLO X Y0 cs (h + lnV K c) ocs hop.2 (by have := hC.right; rwa [tm_len] at this) (by omega)
    refine ⟨pairX r1.ok r2.ok sc, fun fk hk => ?_⟩
    have h1 := r1.ok
    rw [← ovS (Y0.cx fk hk) c] at h1
    exact pairCap h1 (r1.fail fk hk) (r2.fail fk hk) sc
termination_by cs => 2 * sizeOf cs
end

end runO


end Templates

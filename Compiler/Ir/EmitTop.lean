/- The stub (check its two cells fit, open them, call `main`), and **`emit_ok`**: the machine run of `emitP`'s code
for a terminating Lin run returns to the caller, changes nothing outside the output and work blocks, and either
delivers the output (`peak ≤ work cells`) or the out-of-memory flag (`peak > work cells`). -/
import Compiler.Ir.EmitLayout

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- the exit, from the stub's cell -/
theorem exit_ok' {s : T.S} {q : Nat} {rest : List (BitVec 32)} (hA : C.AtQ s q) (hk : T.keepC C.s0 s)
    (h16 : C.wb + 16 ≤ C.T0) (hstub : bytes (T.mem s) (C.T0 - 16) 8 = (le8 (T.ra C.s0)).map some)
    (hin : InW C.W q (T.encO .exit ++ rest)) : T.runsTo s C.Exited := by
  have htop : T.top s = C.T0 := by rw [T.top_keepC hk, C.htop]; rfl
  have hT := C.T0_le; have hal := C.T0_al; obtain ⟨hw1, hw2⟩ := C.wR
  refine T.toCore.runsTo_mono (T.c_exit (w := T.ra C.s0) (C.at_of hA hin.left) (by rw [htop]; omega)
    (by rw [htop]; exact ⟨by omega, by omega⟩) (by rw [htop]; omega) (by rw [htop]; exact hstub) C.retOK)
    fun s' ⟨hok, hpc, hs, hm⟩ => ⟨hok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2, hs⟩

theorem init_eq {Q : Prog Nat} {F : Func Nat} (hF : Q.funcs[Q.main]? = some F) (input : List UInt8) :
    init Q input = ⟨[⟨Q.main, F.entry, 0, setMany (fun _ => .w 0) F.params
      [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩], Mem.init input, []⟩ := by
  unfold init; rw [hF]



/-- one jump (no frame relation) -/
theorem jW_raw {s : T.S} {q t : Nat} {o : EOp} {rest : List (BitVec 32)}
    (hA : C.AtQ s q) (hj : T.jW q t = some o) (hin : InW C.W q (T.encO o ++ rest)) :
    T.runsTo s fun s' => C.AtQ s' t ∧ T.keep s s' ∧ T.mem s' = T.mem s ∧ T.Same s s' := by
  unfold Target.jW at hj
  have hAt := C.at_of hA hin.left
  split at hj
  · next hqt =>
    split at hj
    · next hok =>
      cases hj
      refine T.toCore.runsTo_mono (T.w_jmp hok hAt) fun s' ⟨d, hs, hm⟩ => ?_
      have hpc := d.hpc; rw [tgt_fwd _ hqt] at hpc
      exact ⟨⟨d.ok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2⟩, d.keep, hm, hs⟩
    · exact nomatch hj
  · next hqt =>
    split at hj
    · next hok =>
      cases hj
      refine T.toCore.runsTo_mono (T.w_jmp hok hAt) fun s' ⟨d, hs, hm⟩ => ?_
      have hpc := d.hpc; rw [tgt_back _ (by omega)] at hpc
      exact ⟨⟨d.ok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2⟩, d.keep, hm, hs⟩
    · exact nomatch hj

set_option maxHeartbeats 1000000 in
/-- **the stub**: its two cells (or `exit0`), then the call of `main` (or the exit), then `main`'s prologue -/
theorem stub_ok {Q : Prog Nat} {L : Lay} {F : Func Nat} {c : List EOp} {rest : List (BitVec 32)}
    (hF : Q.funcs[Q.main]? = some F) (hp3 : F.params.length = 3)
    (hc : T.callTo L.ex F.slots (T.len (T.stub1 ++ exit0 ++ Target.stub2)) (L.fq.getD Q.main 0) = some c)
    (himm : T.immOK .add 8 = true) (hbr0 : T.brOK false (T.lenBr + T.len exit0) = true)
    (hbrJ : T.brOK false (T.lenBr + T.lenJ) = true) (hns : F.slots ≤ T.maxSlots) (h64 : 8 * (F.slots + 1) < 2 ^ 64)
    (hin : InW C.W 0 (T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c) ++ rest))
    (hK : Code C Q L (T.len (T.stub1 ++ exit0 ++ Target.stub2 ++ c)))
    (hok : T.ok C.s0) (hpc : T.pcIs C.s0 C.pc0) (h11 : T.get C.s0 RIn = BitVec.ofNat 64 C.inA)
    (h12 : T.get C.s0 RLen = BitVec.ofNat 64 C.input.length) (h13 : T.get C.s0 RHp = BitVec.ofNat 64 C.wb)
    (h14 : T.get C.s0 ROut = BitVec.ofNat 64 C.outA) (h16 : 16 ≤ T.top C.s0) :
    T.runsTo C.s0 fun s' => C.Rel Q L (T.len (T.stub1 ++ exit0 ++ Target.stub2 ++ c)) (init Q C.input) s' ∨
      (C.wl / 8 < F.slots + 3 ∧ C.Exited s') := by
  have hA0 : C.AtQ C.s0 0 := ⟨hok, by rw [next_zero]; exact hpc, fun _ _ _ => rfl⟩
  have hin1 : InW C.W 0 (T.encO (.top R0) ++ (T.encO (.w (.bini .add R0 R0 8)) ++ (T.encO (.w (.bin .sub R1 R0 RHp)) ++
      (T.encO (.w (.li R2 16)) ++ (T.encO (.w (.br .geu R1 (some R2) false (T.lenBr + T.len exit0))) ++
      (T.words exit0 ++ (T.encO (.w (.bin .sub RLim R0 R2)) ++ (T.encO (.enter 0) ++ (T.encO (.enterC 0) ++
      (T.encO (.w (.mov R0 RIn)) ++ (T.encO (.w (.mov R1 RLen)) ++ (T.encO (.w (.mov R2 ROut)) ++
      (T.words c ++ rest))))))))))))) := by
    simpa only [Target.stub1, Target.stub2, T.words_append, Target.words_cons, Target.words_nil, List.append_nil,
      List.append_assoc, List.cons_append, List.nil_append] using hin
  have htop : T.top C.s0 = C.T0 := C.htop
  obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt; have hal := C.wal; have hT := C.T0_le; have hTa := C.T0_al
  have hdiv := Nat.div_mul_le_self C.wl 8
  have hT0 : C.T0 = C.wb + C.wl / 8 * 8 := rfl
  -- r0 := top - 8; r0 := top; r1 := top - work base; r2 := 16
  refine T.toCore.runsTo_trans (C.op hA0 hin1 fun h => T.toCore.runsTo_mono (T.t_top (d := R0) (by decide) h16 h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s1 ⟨hA1, hk1, hm1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA1 hin1.right fun h => T.toCore.runsTo_mono (T.w_bini himm h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s2 ⟨hA2, hk2, hm2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA2 hin1.right.right fun h => T.toCore.runsTo_mono (T.w_bin h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s3 ⟨hA3, hk3, hm3, st3⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA3 hin1.right.right.right fun h => T.toCore.runsTo_mono (T.w_li h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s4 ⟨hA4, hk4, hm4, st4⟩ => ?_
  have e2 : T.get s2 R0 = BitVec.ofNat 64 C.T0 := by
    rw [Core.Set1.same T.toCore st2, Core.Set1.same T.toCore st1]
    show BitVec.ofNat 64 (T.top C.s0 - 8) + BitVec.ofNat 64 8 = _
    rw [bv_ofNat_add, htop]; congr 1; omega
  have e4R0 : T.get s4 R0 = BitVec.ofNat 64 C.T0 := by
    rw [Core.Set1.other T.toCore st4 (by decide), Core.Set1.other T.toCore st3 (by decide), e2]
  have e4R1 : T.get s4 R1 = BitVec.ofNat 64 (C.wl / 8 * 8) := by
    rw [Core.Set1.other T.toCore st4 (by decide), Core.Set1.same T.toCore st3, e2,
      Core.Set1.other T.toCore st2 (by decide), Core.Set1.other T.toCore st1 (by decide), h13,
      bv_sub _ _ (by omega) (by omega)]
    congr 1; omega
  have e4R2 : T.get s4 R2 = BitVec.ofNat 64 16 := Core.Set1.same T.toCore st4
  have hk04 : T.keep C.s0 s4 := T.keep_trans hk1 (T.keep_trans hk2 (T.keep_trans hk3 hk4))
  have hm04 : T.mem s4 = T.mem C.s0 := by rw [hm4, hm3, hm2, hm1]
  have keepR : ∀ r : Reg, 3 ≤ r.val → T.get s4 r = T.get C.s0 r := fun r hr => by
    rw [Core.Set1.other T.toCore st4 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st3 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st2 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st1 (fun e => by rw [e] at hr; exact absurd hr (by decide))]
  have hin4 := hin1.right.right.right.right
  refine T.toCore.runsTo_trans (T.w_br (c := .geu) (a := R1) (b := some R2) hbr0 (C.at_of hA4 hin4.left))
    fun s5 ⟨d5, hs5, hm5⟩ => ?_
  simp only [Base.getO, e4R1, e4R2] at d5
  have hfitB : (16 ≤ C.wl / 8 * 8) ↔
      Cond.eval .geu (BitVec.ofNat 64 (C.wl / 8 * 8)) (BitVec.ofNat 64 16) = true := by
    simp only [Cond.eval, Bool.not_eq_true', decide_eq_false_iff_not, BitVec.lt_def]
    rw [ofNat_toNat' (by omega), ofNat_toNat' (by omega)]; omega
  have hU5 : C.Unch s5 := fun a _ _ => by rw [hm5, hm04]
  have hk05 : T.keep C.s0 s5 := T.keep_trans hk04 d5.keep
  have hin5 := hin4.right
  rw [T.len_brO] at hin5
  have hq4 : (0 + (T.encO (.top R0)).length + (T.encO (.w (.bini .add R0 R0 8))).length +
      (T.encO (.w (.bin .sub R1 R0 RHp))).length + (T.encO (.w (.li R2 16))).length) = T.len T.stub1 - T.lenBr := by
    simp only [Target.stub1, Target.len_cons, Target.len_nil, T.len_brO]; omega
  have hst1 : T.len T.stub1 = (T.encO (.top R0)).length + (T.encO (.w (.bini .add R0 R0 8))).length +
      (T.encO (.w (.bin .sub R1 R0 RHp))).length + (T.encO (.w (.li R2 16))).length + T.lenBr := by
    simp only [Target.stub1, Target.len_cons, Target.len_nil, T.len_brO]; omega
  by_cases hfit : 16 ≤ C.wl / 8 * 8
  · -- the stub's cells fit
    have hpc5 := d5.hpc
    rw [if_pos (hfitB.1 hfit)] at hpc5
    simp only [tgt, Bool.false_eq_true, if_false, next_add] at hpc5
    have hA5 : C.AtQ s5 (T.len T.stub1 + T.len exit0) := ⟨d5.ok, by rw [hst1]; simpa [Nat.add_assoc] using hpc5, hU5⟩
    have hin5' : InW C.W (T.len T.stub1 + T.len exit0) (T.encO (.w (.bin .sub RLim R0 R2)) ++ (T.encO (.enter 0) ++
        (T.encO (.enterC 0) ++ (T.encO (.w (.mov R0 RIn)) ++ (T.encO (.w (.mov R1 RLen)) ++ (T.encO (.w (.mov R2 ROut)) ++
        (T.words c ++ rest))))))) := by
      have := hin5.right; rw [hst1]; simpa only [Nat.zero_add, Nat.add_assoc] using this
    refine T.toCore.runsTo_trans (C.op hA5 hin5' fun h => T.toCore.runsTo_mono (T.w_bin h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s6 ⟨hA6, hk6, hm6, st6⟩ => ?_
    have hk06 : T.keep C.s0 s6 := T.keep_trans hk05 hk6
    have htop6 : T.top s6 = C.T0 := by rw [T.top_keepF (T.keepF_of_keep hk06), htop]
    have hm60 : T.mem s6 = T.mem C.s0 := by rw [hm6, hm5, hm04]
    have e6lim : T.get s6 RLim = BitVec.ofNat 64 (C.T0 - 16) := by
      rw [Core.Set1.same T.toCore st6, hs5, hs5, e4R0, e4R2]; exact bv_sub _ _ (by omega) (by omega)
    have keep6 : ∀ r : Reg, 3 ≤ r.val → r ≠ RLim → T.get s6 r = T.get C.s0 r := fun r hr hne => by
      rw [Core.Set1.other T.toCore st6 hne, hs5, keepR r hr]
    -- enter 0: the caller's frame register at `top - 8`
    have hin6 := hin5'.right
    have hAt6 := C.at_of hA6 hin6.left
    obtain ⟨pre6, post6, eW6, hpre6⟩ := hin6
    have hlenW6 := congrArg List.length eW6; simp only [List.length_append] at hlenW6
    have hq6 : (next C.pc0 (T.len T.stub1 + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length)).toNat =
        C.pc0.toNat + 4 * pre6.length := by rw [hpre6]; exact T.toCore.pc_toNat C.codeOK (by omega)
    have hdis := C.dCW; unfold disjoint at hdis; dsimp only at hdis
    have hfr6 : T.frameAt s6 0 = C.T0 - 8 := by rw [T.frameAt_top, htop6]
    refine T.toCore.runsTo_trans (T.f_enter (T.enterOK_of (Nat.zero_le _) (by rw [htop6]; omega)
        (by rw [htop6]; omega) (by rw [htop6]; exact ⟨by omega, by omega⟩)) hAt6
      (by rw [hq6, hfr6]; unfold disjoint; dsimp only; have : (T.encO (.enter 0)).length = (T.encE 0).length := rfl; omega))
      fun s7 ⟨hok7, hkF7, hpc7, hfr7, hreg7, hout7, hsv7, _⟩ => ?_
    rw [hfr6] at hfr7 hsv7 hout7
    have hA7 : C.AtQ s7 (T.len T.stub1 + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length +
        (T.encO (.enter 0)).length) := ⟨hok7, by rw [← next_add]; exact hpc7, fun a h1 h2 => by
          rw [hout7 a (by intro r hr; simp at hr; subst hr; dsimp only; omega), hm60]⟩
    have hra7 : T.ra s7 = T.ra C.s0 := by rw [T.keepF_ra hkF7, T.keep_ra hk06]
    have hfr7' : (T.fr s7).toNat = C.T0 - 8 := by rw [hfr7, ofNat_toNat' (by omega)]
    have hin7 := hin5'.right.right
    refine T.toCore.runsTo_trans (T.c_enterC (n := 0) (Nat.zero_le _) (C.at_of hA7 hin7.left) (by rw [hfr7']; omega)
      (by rw [hfr7']; exact ⟨by omega, by omega⟩) (by rw [hfr7']; omega)
      (fun i hi => C.wr _ _ (.inr ⟨by rw [hfr7']; omega, by rw [hfr7']; omega⟩)))
      fun s8 ⟨hok8, hk8, hpc8, hfr8, hs8, hm8⟩ => ?_
    rw [hfr7', show C.T0 - 8 - 8 * (0 + 1) = C.T0 - 16 by omega] at hfr8 hm8
    rw [hra7] at hm8
    have hl8 : ∀ x : BitVec 64, (le8 x).length = 8 := length_le8
    have hA8 : C.AtQ s8 (T.len T.stub1 + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length +
        (T.encO (.enter 0)).length + (T.encO (.enterC 0)).length) :=
      ⟨hok8, by rw [← next_add]; exact hpc8, unch_work hA7.2.2 hm8 (by omega) (by rw [hl8]; omega)⟩
    have hin8 := hin7.right
    refine T.toCore.runsTo_trans (C.op hA8 hin8 fun h => T.toCore.runsTo_mono (T.w_mov h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s9 ⟨hA9, hk9, hm9, st9⟩ => ?_
    refine T.toCore.runsTo_trans (C.op hA9 hin8.right fun h => T.toCore.runsTo_mono (T.w_mov h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s10 ⟨hA10, hk10, hm10, st10⟩ => ?_
    refine T.toCore.runsTo_trans (C.op hA10 hin8.right.right fun h => T.toCore.runsTo_mono (T.w_mov h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s11 ⟨hA11, hk11, hm11, st11⟩ => ?_
    have hq11 : T.len T.stub1 + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length + (T.encO (.enter 0)).length +
        (T.encO (.enterC 0)).length + (T.encO (.w (.mov R0 RIn))).length + (T.encO (.w (.mov R1 RLen))).length +
        (T.encO (.w (.mov R2 ROut))).length = T.len (T.stub1 ++ exit0 ++ Target.stub2) := by
      simp only [Target.stub2, Target.len_append, Target.len_cons, Target.len_nil]; omega
    rw [hq11] at hA11
    have hin11 := hin8.right.right.right
    rw [hq11] at hin11
    -- registers after the stub's moves
    have hreg811 : ∀ r : Reg, r ≠ R0 → r ≠ R1 → r ≠ R2 → T.get s11 r = T.get s8 r := fun r h0 h1 h2 => by
      rw [Core.Set1.other T.toCore st11 h2, Core.Set1.other T.toCore st10 h1, Core.Set1.other T.toCore st9 h0]
    have hreg68 : ∀ r : Reg, 7 ≤ r.val → T.get s8 r = T.get s6 r := fun r hr => by rw [hs8, hreg7 r hr]
    have e11 : ∀ r : Reg, 7 ≤ r.val → r ≠ RLim → T.get s11 r = T.get C.s0 r := fun r hr hne => by
      rw [hreg811 r (by intro e; rw [e] at hr; exact absurd hr (by decide)) (by intro e; rw [e] at hr; exact absurd hr (by decide))
        (by intro e; rw [e] at hr; exact absurd hr (by decide)), hreg68 r hr, keep6 r (by omega) hne]
    have e11lim : T.get s11 RLim = BitVec.ofNat 64 (C.T0 - 16) := by
      rw [hreg811 _ (by decide) (by decide) (by decide), hreg68 _ (by decide), e6lim]
    have e11r0 : T.get s11 (rk 0) = BitVec.ofNat 64 C.inA := by
      rw [show rk 0 = R0 from rfl, Core.Set1.other T.toCore st11 (by decide), Core.Set1.other T.toCore st10 (by decide),
        Core.Set1.same T.toCore st9, hreg68 _ (by decide), keep6 _ (by decide) (by decide), h11]
    have e11r1 : T.get s11 (rk 1) = BitVec.ofNat 64 C.input.length := by
      rw [show rk 1 = R1 from rfl, Core.Set1.other T.toCore st11 (by decide), Core.Set1.same T.toCore st10,
        Core.Set1.other T.toCore st9 (by decide), hreg68 _ (by decide), keep6 _ (by decide) (by decide), h12]
    have e11r2 : T.get s11 (rk 2) = BitVec.ofNat 64 C.outA := by
      rw [show rk 2 = R2 from rfl, Core.Set1.same T.toCore st11, Core.Set1.other T.toCore st10 (by decide),
        Core.Set1.other T.toCore st9 (by decide), hreg68 _ (by decide), keep6 _ (by decide) (by decide), h14]
    have hm118 : T.mem s11 = T.mem s8 := by rw [hm11, hm10, hm9]
    have hk011 : T.keepC C.s0 s11 := T.keepC_trans (T.keepC_trans (T.keepC_of_keepF (T.keepF_trans
      (T.keepF_of_keep hk06) hkF7)) hk8) (T.keepC_of_keepF (T.keepF_of_keep (T.keep_trans hk9 (T.keep_trans hk10 hk11))))
    have hstub11 : bytes (T.mem s11) (C.T0 - 16) 8 = (le8 (T.ra C.s0)).map some := by
      rw [hm118, hm8]; have e := @bytes_wr_self (T.mem s7) (C.T0 - 16) (le8 (T.ra C.s0)); rw [hl8] at e; exact e
    have hgp11 : bytes (T.mem s11) (C.T0 - 8) 8 = (le8 (T.fr C.s0)).map some := by
      rw [hm118, hm8, bytes_wr_out (.inr (by rw [hl8]; omega)), hsv7, T.keep_fr hk06]
    -- the call of `main`: its frame fits (else the exit), then its prologue
    obtain ⟨rex, hex⟩ := hK.exit
    have hKF := hK.fn _ _ hF
    obtain ⟨jg, restg, hjg, hprog⟩ := hKF.pro
    obtain ⟨BE, hBE⟩ := hKF.ent
    obtain ⟨cE, ctE, hcE, hctE, hinE⟩ := hKF.blocks _ _ hBE
    unfold Target.callTo at hc
    cases hj : T.jW (T.len (T.stub1 ++ exit0 ++ Target.stub2) + T.len (T.chkPre F.slots)) L.ex with
    | none => rw [hj] at hc; exact nomatch hc
    | some j =>
    rw [hj] at hc; simp only at hc
    split at hc
    rotate_left
    · exact nomatch hc
    rename_i hcall
    cases hc
    generalize hd : ((L.fq.getD Q.main 0 : Nat) : Int) - ((T.len (T.stub1 ++ exit0 ++ Target.stub2) +
      T.len (T.chkPre F.slots ++ [j, .w (.bin .sub RLim RLim R8)]) : Nat) : Int) = d at hin11 hcall hK ⊢
    generalize hq0 : T.len (T.stub1 ++ exit0 ++ Target.stub2) = q0 at hin11 hA11 hj hd ⊢
    have hinc : InW C.W q0 (T.encO (.w (.bin .sub R7 RLim RHp)) ++ (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (F.slots + 1))))) ++
        (T.encO (.w (.br .geu R7 (some R8) false (T.lenBr + T.lenJ))) ++ (T.encO j ++
        (T.encO (.w (.bin .sub RLim RLim R8)) ++ (T.encO (.call d) ++ rest)))))) := by
      simpa only [Target.chkPre, T.words_append, Target.words_cons, Target.words_nil, List.append_nil,
        List.append_assoc, List.cons_append, List.nil_append] using hin11
    refine T.toCore.runsTo_trans (C.op hA11 hinc fun h => T.toCore.runsTo_mono (T.w_bin h)
      fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s12 ⟨hA12, hk12, hm12, st12⟩ => ?_
    refine T.toCore.runsTo_trans (C.op hA12 hinc.right fun h => T.toCore.runsTo_mono (T.w_li h)
      fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s13 ⟨hA13, hk13, hm13, st13⟩ => ?_
    have e13r7 : T.get s13 R7 = BitVec.ofNat 64 (C.T0 - 16 - C.wb) := by
      rw [Core.Set1.other T.toCore st13 (by decide), Core.Set1.same T.toCore st12, e11lim,
        e11 _ (by decide) (by decide), h13, bv_sub _ _ (by omega) (by omega)]
    have e13r8 : T.get s13 R8 = BitVec.ofNat 64 (8 * (F.slots + 1)) := Core.Set1.same T.toCore st13
    have hin13 := hinc.right.right
    refine T.toCore.runsTo_trans (T.w_br (c := .geu) (a := R7) (b := some R8) hbrJ (C.at_of hA13 hin13.left))
      fun s14 ⟨d14, hs14, hm14⟩ => ?_
    simp only [Base.getO, e13r7, e13r8] at d14
    have hfree : C.T0 - 16 - C.wb < 2 ^ 64 := by omega
    have hU14 : C.Unch s14 := fun a h1 h2 => by rw [hm14]; exact hA13.2.2 a h1 h2
    have hm14' : T.mem s14 = T.mem s11 := by rw [hm14, hm13, hm12]
    have hk1114 : T.keep s11 s14 := T.keep_trans hk12 (T.keep_trans hk13 d14.keep)
    have hlj := jW_len hj
    by_cases hfits : 8 * (F.slots + 1) ≤ C.T0 - 16 - C.wb
    · -- over the jump to the exit, the frame limit down, the call
      have hpc14 := d14.hpc
      rw [if_pos (by
        simp only [Cond.eval, Bool.not_eq_true']; apply decide_eq_false; intro hlt'
        rw [BitVec.lt_def, ofNat_toNat' hfree, ofNat_toNat' h64] at hlt'; omega)] at hpc14
      simp only [tgt, Bool.false_eq_true, if_false, next_add] at hpc14
      have hA14 : C.AtQ s14 (q0 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (F.slots + 1)))))).length + T.lenBr + T.lenJ) :=
        ⟨d14.ok, by simpa [Nat.add_assoc] using hpc14, hU14⟩
      have hin14 := hin13.right.right
      rw [T.len_brO, hlj] at hin14
      refine T.toCore.runsTo_trans (C.op hA14 hin14 fun h => T.toCore.runsTo_mono (T.w_bin h)
        fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s15 ⟨hA15, hk15, hm15, st15⟩ => ?_
      refine T.toCore.runsTo_trans (T.c_call hcall (C.at_of hA15 hin14.right.left))
        fun s16 ⟨hok16, hk16, hpc16, hra16, hfr16, hs16, hm16⟩ => ?_
      have hqc : q0 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (F.slots + 1)))))).length + T.lenBr + T.lenJ +
          (T.encO (.w (.bin .sub RLim RLim R8))).length = q0 + T.len (T.chkPre F.slots ++ [j, .w (.bin .sub RLim RLim R8)]) := by
        simp only [Target.chkPre, Target.len_append, Target.len_cons, Target.len_nil, T.len_brO, hlj]; omega
      rw [hqc, ← hd, Ctx.next_call] at hpc16
      rw [hqc] at hra16
      have hm16' : T.mem s16 = T.mem s11 := by rw [hm16, hm15, hm14']
      have hreg16 : ∀ r : Reg, r ≠ RLim → r ≠ R7 → r ≠ R8 → T.get s16 r = T.get s11 r := fun r h1 h2 h3 => by
        rw [hs16, Core.Set1.other T.toCore st15 h1, hs14, Core.Set1.other T.toCore st13 h3, Core.Set1.other T.toCore st12 h2]
      have hfb : C.T0 - 16 - 8 * (F.slots + 1) + 8 * (F.slots + 1) = C.T0 - 16 := by omega
      have hP : C.Pre (Mem.init C.input) (C.T0 - 16 - 8 * (F.slots + 1)) F.slots s16 := {
        ok := hok16
        keep := T.keepC_trans (T.keepC_trans hk011 (T.keepC_of_keepF (T.keepF_of_keep (T.keep_trans hk1114 hk15)))) hk16
        fr := by rw [hfr16, T.keep_fr hk15, T.keep_fr hk1114, T.keep_fr hk11, T.keep_fr hk10, T.keep_fr hk9, hfr8, hfb]
        rlim := by
          rw [hs16, Core.Set1.same T.toCore st15, hs14, hs14, e13r8, Core.Set1.other T.toCore st13 (by decide),
            Core.Set1.other T.toCore st12 (by decide), e11lim]
          exact bv_sub _ _ (by omega) (by omega)
        rin := by rw [hreg16 _ (by decide) (by decide) (by decide), e11 _ (by decide) (by decide), h11]
        rhp := by rw [hreg16 _ (by decide) (by decide) (by decide), e11 _ (by decide) (by decide), h13]; simp [Mem.init]
        cap := by simp [Mem.init]; omega
        fit := by omega
        fal := by omega
        nsl := hns
        stub := by rw [hm16']; exact hstub11
        cells := fun g v h => by simp [Mem.init] at h
        out := fun i b h => by simp [Mem.init] at h
        outL := by simp [Mem.init]
        unch := fun a h1 h2 => by rw [hm16']; exact hA11.2.2 a h1 h2
        mok := ⟨rfl, fun k a sz lv h => by simp [Mem.init] at h, fun g v h => by simp [Mem.init] at h⟩ }
      have hA16 : C.AtQ s16 ((Q.env L).fq Q.main) := ⟨hok16, hpc16, hP.unch⟩
      have hargs : ∀ i (h : i < [Val.p 0 0, .w (BitVec.ofNat 64 C.input.length), .p 1 0].length),
          T.get s16 (rk i) = C.repr (Mem.init C.input).blks [Val.p 0 0, .w (BitVec.ofNat 64 C.input.length), .p 1 0][i] := by
        intro i h
        rw [hreg16 _ (by intro e; have := congrArg Fin.val e; simp at h; rw [rk_lt (by omega)] at this; simp [RLim] at this; omega)
          (by intro e; have := congrArg Fin.val e; simp at h; rw [rk_lt (by omega)] at this; simp [R7] at this; omega)
          (by intro e; have := congrArg Fin.val e; simp at h; rw [rk_lt (by omega)] at this; simp [R8] at this; omega)]
        match i, h with
        | 0, _ => rw [e11r0]; simp [repr]
        | 1, _ => rw [e11r1]; rfl
        | 2, _ => rw [e11r2]; simp [repr]
      refine T.toCore.runsTo_mono (C.pro_ok hA16 hP hjg hprog (by simp [hp3]) (by omega) hKF.ps hargs
        (fun v hv => by simp at hv; rcases hv with rfl | rfl | rfl <;> simp [Valid])) fun s17 ⟨hA17, hR17⟩ => .inl ?_
      rw [Ctx.init_eq hF]
      refine ⟨_, [], F, BE, C.T0 - 16 - 8 * (F.slots + 1), T.ra s16, T.mem s16, L.posF Q.main F.entry, cE, ctE, rfl, hF,
        hBE, by simpa using hcE, hctE, hinE, hA17, hR17, ⟨by omega, ?_, rfl, rfl, by rw [hm16']; exact hgp11⟩, ?_, ?_⟩
      · rw [hra16, next_add]
        congr 1
        rw [← hq0]; simp only [Target.chkPre, Target.len_append, Target.len_cons, Target.len_nil]
        have : (T.encO (EOp.call d)).length = T.lenCall := T.len_call d
        omega
      · simp only [Ctx.base, hF, Option.map_some, Option.getD_some, inUse, List.nil_append, Mem.init, List.length_nil]
        omega
      · simp only [Ctx.base, hF, Option.map_some, Option.getD_some, List.nil_append, peak, inUse]
        omega
    · -- the frame of `main` does not fit: to the exit
      have hpc14 := d14.hpc
      rw [if_neg (by
        simp only [Cond.eval, Bool.not_eq_true', Bool.not_eq_false]; apply decide_eq_true
        rw [BitVec.lt_def, ofNat_toNat' hfree, ofNat_toNat' h64]; omega)] at hpc14
      rw [next_add] at hpc14
      have hin14 := hin13.right
      rw [T.len_brO] at hin14
      have hpq : q0 + (T.encO (.w (.bin .sub R7 RLim RHp))).length +
          (T.encO (.w (.li R8 (BitVec.ofNat 64 (8 * (F.slots + 1)))))).length + T.lenBr = q0 + T.len (T.chkPre F.slots) := by
        simp only [Target.chkPre, Target.len_cons, Target.len_nil, T.len_brO]; omega
      have hA14 : C.AtQ s14 (q0 + T.len (T.chkPre F.slots)) := ⟨d14.ok, by rw [← hpq]; exact hpc14, hU14⟩
      rw [hpq] at hin14
      refine T.toCore.runsTo_trans (C.jW_raw hA14 hj hin14) fun s15 ⟨hA15, hk15, hm15, _⟩ =>
        T.toCore.runsTo_mono (C.exit_ok' hA15
          (T.keepC_trans hk011 (T.keepC_of_keepF (T.keepF_of_keep (T.keep_trans hk1114 hk15)))) (by omega)
          (by rw [hm15, hm14']; exact hstub11) hex) fun s16 h16 => .inr ⟨by omega, h16⟩
  · -- they do not fit: `exit0`
    have hpc5 := d5.hpc
    rw [if_neg (fun h => hfit (hfitB.2 h))] at hpc5
    rw [next_add] at hpc5
    have hA5 : C.AtQ s5 (0 + (T.encO (.top R0)).length + (T.encO (.w (.bini .add R0 R0 8))).length +
      (T.encO (.w (.bin .sub R1 R0 RHp))).length + (T.encO (.w (.li R2 16))).length + T.lenBr) := ⟨d5.ok, hpc5, hU5⟩
    have hin6 : InW C.W (0 + (T.encO (.top R0)).length + (T.encO (.w (.bini .add R0 R0 8))).length +
        (T.encO (.w (.bin .sub R1 R0 RHp))).length + (T.encO (.w (.li R2 16))).length + T.lenBr)
        (T.encO (.w (.li RIn (BitVec.allOnes 64))) ++ (T.encO (.w .ret) ++ [])) := by
      have := hin5.left (b := _); simpa only [exit0, Target.words_cons, Target.words_nil, List.append_nil] using this
    refine T.toCore.runsTo_trans (C.op hA5 hin6 fun h => T.toCore.runsTo_mono (T.w_li h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s6 ⟨hA6, hk6, hm6, st6⟩ => ?_
    have hra : T.ra s6 = T.ra C.s0 := by rw [T.keep_ra (T.keep_trans hk05 hk6)]
    refine T.toCore.runsTo_mono (T.w_ret (by rw [hra]; exact C.retOK) (C.at_of hA6 hin6.right.left))
      fun s7 ⟨d7, hs7, hm7⟩ => .inr ⟨by omega, d7.ok, by rw [← hra]; exact d7.hpc,
        fun a _ _ => by rw [hm7, hm6, hm5, hm04], by rw [hs7]; exact Core.Set1.same T.toCore st6⟩


/-- **emission is correct** (any target): from the start of a call, the code of `emitP` runs a terminating Lin run
of the program to its end: back at the caller's return address, nothing changed outside the output and work
blocks, and either the output bytes are in the output block (`peak ≤ work cells`, status the input address) or the
status is the out-of-memory flag (`peak > work cells`). -/
theorem emit_ok {Q : Prog Nat} {L : Lay} {code : List EOp} (he : T.emitP Q L = some code) (hW : C.W = T.words code)
    (hok : T.ok C.s0) (hpc : T.pcIs C.s0 C.pc0) (h11 : T.get C.s0 RIn = BitVec.ofNat 64 C.inA)
    (h12 : T.get C.s0 RLen = BitVec.ofNat 64 C.input.length) (h13 : T.get C.s0 RHp = BitVec.ofNat 64 C.wb)
    (h14 : T.get C.s0 ROut = BitVec.ofNat 64 C.outA) (h16 : 16 ≤ T.top C.s0) {r : Result}
    (hrun : Runs Q (init Q C.input) r) (hout : r.mem.out.length ≤ C.outL) : T.runsTo C.s0 (C.Fin Q r) := by
  obtain ⟨F, c, hF, hp3, hc, himm, hbr0, hbrJ, hns, h64, ⟨rest, hin⟩, hK⟩ := C.code_of he hW
  refine T.toCore.runsTo_trans (C.stub_ok hF hp3 hc himm hbr0 hbrJ hns h64 hin hK hok hpc h11 h12 h13 h14 h16)
    fun s h => ?_
  rcases h with hrel | ⟨hlt, hE⟩
  · obtain ⟨n, hn⟩ := hrun; exact C.sim hK n hrel hn hout
  · refine T.runsTo_of ⟨hE.1, hE.2.1, hE.2.2.1, .inr ⟨?_, hE.2.2.2⟩⟩
    have := peak_append_ge r.ev [Ctx.base Q]
    have e : peak [Ctx.base Q] = F.slots + 3 := by simp [Ctx.base, hF, peak, inUse]
    omega

end Ctx
end Proven.Ir

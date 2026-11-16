/- The prologue (check the frame fits, open it, the parameters of `main`), and **`emit_ok`**: the machine
run of `emitF`'s code for a terminating Lin run returns to the caller, changes nothing outside the output and work
blocks, and either delivers the output (`peak ≤ work cells`) or the out-of-memory flag (`peak > work cells`). -/
import Compiler.Ir.EmitLayout

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem storeRegs_ok {m : Mem} : ∀ (ps : List Nat) (rs : List Reg) (vs : List Val) {regs : Nat → Val} {s : T.S}
    {q : Nat} {rest : List (BitVec 32)}, C.AtQ s q → C.MR m regs s → rs.length = vs.length →
    (∀ p ∈ ps, p < C.nS) → (∀ v ∈ vs, Valid m.blks v) →
    (∀ i (h : i < rs.length) (h' : i < vs.length), T.get s rs[i] = C.repr m.blks vs[i]) →
    InW C.W q (T.words (storeRegs ps rs) ++ rest) →
    T.runsTo s fun s' => C.AtQ s' (q + T.len (storeRegs ps rs)) ∧ C.MR m (setMany regs ps vs) s'
  | [], _, _, regs, s, q, rest, hA, hR, _, _, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, storeRegs, Target.words]), by simpa [setMany] using hR⟩
  | _ :: _, [], [], regs, s, q, rest, hA, hR, _, _, _, _, _ =>
    T.runsTo_of ⟨hA.congr (by simp [Target.len, storeRegs, Target.words]), by simpa [setMany] using hR⟩
  | _ :: _, [], _ :: _, _, _, _, _, _, _, hl, _, _, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, _, _, _, _, hl, _, _, _, _ => nomatch hl
  | p :: ps, r :: rs, v :: vs, regs, s, q, rest, hA, hR, hl, hp, hv, hg, hin => by
    simp only [List.length_cons] at hl
    have hin' : InW C.W q (T.words (.w (.stS p r) :: storeRegs ps rs) ++ rest) := hin
    refine T.toCore.runsTo_trans (C.stS_ok hA hR hin'.cons (hp p (List.mem_cons_self ..))
      (hg 0 (by simp) (by simp)) (hv v (List.mem_cons_self ..))) fun s1 ⟨hA1, hR1, hs1⟩ => ?_
    refine T.toCore.runsTo_mono (storeRegs_ok ps rs vs hA1 hR1 (by omega)
      (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hv x (List.mem_cons_of_mem _ hx))
      (fun i h h' => by rw [hs1]; exact hg (i + 1) (by simp; omega) (by simp; omega)) hin'.next)
      fun s' ⟨hA', hR'⟩ => ⟨hA'.congr (by simp only [Target.len, storeRegs, Target.words, List.length_append]; omega), hR'⟩

/-- **the prologue** -/
theorem pro_ok {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} {j : List EOp}
    {rest : List (BitVec 32)} (hP : P.funcs[P.main]? = some F) (hK : C.Code F pos ex)
    (hj : T.jTo (T.len (T.pro C.nS F)) (pos F.entry) = some j)
    (hin : InW C.W 0 (T.words (T.pro C.nS F ++ j) ++ rest))
    (hns : C.nS ≤ T.maxSlots) (hns2 : C.nS < 2 ^ 32) (hent : (F.blocks.lookup F.entry).isSome = true) (hps : F.params.all (· < C.nS) = true) (himm : T.immOK .add 8 = true)
    (hbr : T.brOK false (T.lenBr + T.len exit0) = true)
    (hok : T.ok C.s0) (hpc : T.pcIs C.s0 C.pc0) (h11 : T.get C.s0 RIn = BitVec.ofNat 64 C.inA)
    (h12 : T.get C.s0 RLen = BitVec.ofNat 64 C.input.length) (h13 : T.get C.s0 RHp = BitVec.ofNat 64 C.wb)
    (h14 : T.get C.s0 ROut = BitVec.ofNat 64 C.outA) (htop : T.top C.s0 = C.wb + C.wl / 8 * 8)
    (h16 : 16 ≤ T.top C.s0) :
    T.runsTo C.s0 fun s' => C.Rel P F pos ex (init P C.input) s' ∨ (C.wl / 8 < C.nS + 1 ∧ C.Exited s') := by
  have hA0 : C.AtQ C.s0 0 := ⟨hok, by rw [next_zero]; exact hpc, fun _ _ _ => rfl⟩
  have hin0 : InW C.W 0 (T.words ([.top R0, .w (.bini .add R0 R0 8), .w (.bin .sub R1 R0 RHp),
      .w (.li R2 (BitVec.ofNat 64 (8 * (C.nS + 1)))), .w (.br .geu R1 (some R2) false (T.lenBr + T.len exit0))] ++
      exit0 ++ Target.pro2 C.nS F ++ j) ++ rest) := hin
  have hin1 : InW C.W 0 (T.words [.top R0, .w (.bini .add R0 R0 8), .w (.bin .sub R1 R0 RHp),
      .w (.li R2 (BitVec.ofNat 64 (8 * (C.nS + 1)))), .w (.br .geu R1 (some R2) false (T.lenBr + T.len exit0))] ++
      (T.words exit0 ++ (T.words (Target.pro2 C.nS F) ++ (T.words j ++ rest)))) := by
    simpa only [T.words_append, List.append_assoc] using hin0
  obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt; have hal := C.wal
  have hdiv := Nat.div_mul_le_self C.wl 8
  -- r0 := top - 8; r0 := top; r1 := top - wb; r2 := frame size
  refine T.toCore.runsTo_trans (C.op hA0 hin1.cons fun h => T.toCore.runsTo_mono (T.t_top (d := R0) (by decide) h16 h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s1 ⟨hA1, hk1, hm1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA1 hin1.next.cons fun h => T.toCore.runsTo_mono (T.w_bini himm h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s2 ⟨hA2, hk2, hm2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA2 hin1.next.next.cons fun h => T.toCore.runsTo_mono (T.w_bin h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s3 ⟨hA3, hk3, hm3, st3⟩ => ?_
  refine T.toCore.runsTo_trans (C.op hA3 hin1.next.next.next.cons fun h => T.toCore.runsTo_mono (T.w_li h)
    fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s4 ⟨hA4, hk4, hm4, st4⟩ => ?_
  have e2 : T.get s2 R0 = BitVec.ofNat 64 (T.top C.s0) := by
    rw [Core.Set1.same T.toCore st2, Core.Set1.same T.toCore st1]
    show BitVec.ofNat 64 (T.top C.s0 - 8) + BitVec.ofNat 64 8 = _
    rw [bv_ofNat_add]; congr 1; omega
  have e4R0 : T.get s4 R0 = BitVec.ofNat 64 (T.top C.s0) := by
    rw [Core.Set1.other T.toCore st4 (by decide), Core.Set1.other T.toCore st3 (by decide), e2]
  have e4R1 : T.get s4 R1 = BitVec.ofNat 64 (C.wl / 8 * 8) := by
    rw [Core.Set1.other T.toCore st4 (by decide), Core.Set1.same T.toCore st3, e2,
      Core.Set1.other T.toCore st2 (by decide), Core.Set1.other T.toCore st1 (by decide), h13, htop,
      bv_sub _ _ (by omega) (by omega)]
    congr 1; omega
  have e4R2 : T.get s4 R2 = BitVec.ofNat 64 (8 * (C.nS + 1)) := Core.Set1.same T.toCore st4
  have hk04 : T.keep C.s0 s4 := T.keep_trans hk1 (T.keep_trans hk2 (T.keep_trans hk3 hk4))
  have hm04 : T.mem s4 = T.mem C.s0 := by rw [hm4, hm3, hm2, hm1]
  have keepR : ∀ r : Reg, 3 ≤ r.val → T.get s4 r = T.get C.s0 r := fun r hr => by
    rw [Core.Set1.other T.toCore st4 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st3 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st2 (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Core.Set1.other T.toCore st1 (fun e => by rw [e] at hr; exact absurd hr (by decide))]
  -- the branch over `exit0`
  obtain ⟨q4, hq4e, hA4', hin4'⟩ : ∃ q4, q4 = 0 + (T.encO (.top R0)).length + (T.encO (.w (.bini .add R0 R0 8))).length +
      (T.encO (.w (.bin .sub R1 R0 RHp))).length + (T.encO (.w (.li R2 (BitVec.ofNat 64 (8 * (C.nS + 1)))))).length ∧
      C.AtQ s4 q4 ∧ InW C.W q4
      (T.encO (.w (.br .geu R1 (some R2) false (T.lenBr + T.len exit0))) ++
        (T.words exit0 ++ (T.words (Target.pro2 C.nS F) ++ (T.words j ++ rest)))) :=
    ⟨_, rfl, hA4, by simpa only [Target.words, List.append_nil, List.append_assoc] using hin1.next.next.next.next⟩
  have hq4 : q4 + T.lenBr + T.len exit0 + (T.words (Target.pro2 C.nS F)).length = T.len (T.pro C.nS F) := by
    rw [hq4e]
    simp only [Target.pro, Target.pro1, Target.len, T.words_append, Target.words, List.length_append, List.length_nil,
      T.len_brO]
    omega
  refine T.toCore.runsTo_trans (T.w_br (c := .geu) (a := R1) (b := some R2) hbr (C.at_of hA4' hin4'.left))
    fun s5 ⟨d5, hs5, hm5⟩ => ?_
  simp only [Base.getO, e4R1, e4R2] at d5
  have hfitB : (8 * (C.nS + 1) ≤ C.wl / 8 * 8) ↔
      Cond.eval .geu (BitVec.ofNat 64 (C.wl / 8 * 8)) (BitVec.ofNat 64 (8 * (C.nS + 1))) = true := by
    simp only [Cond.eval, Bool.not_eq_true', decide_eq_false_iff_not, BitVec.lt_def]
    rw [ofNat_toNat' (by omega), ofNat_toNat' (by omega)]; omega
  have hU5 : C.Unch s5 := fun a _ _ => by rw [hm5, hm04]
  have hk05 : T.keep C.s0 s5 := T.keep_trans hk04 d5.keep
  have hin5 := hin4'.right
  rw [T.len_brO] at hin5
  by_cases hfit : 8 * (C.nS + 1) ≤ C.wl / 8 * 8
  · -- the frame fits
    have hpc5 := d5.hpc
    rw [if_pos (hfitB.1 hfit)] at hpc5
    simp only [tgt, Bool.false_eq_true, if_false, next_add, ← Nat.add_assoc] at hpc5
    have hA5 : C.AtQ s5 (q4 + T.lenBr + T.len exit0) := ⟨d5.ok, hpc5, hU5⟩
    have hin6 : InW C.W (q4 + T.lenBr + T.len exit0) (T.encO (.w (.bin .sub RLim R0 R2)) ++
        (T.encO (.enter C.nS) ++ (T.words (storeRegs F.params [RIn, RLen, ROut]) ++ (T.words j ++ rest)))) := by
      have := hin5.right
      simpa only [Target.pro2, T.words_append, Target.words, List.append_nil, List.append_assoc] using this
    refine T.toCore.runsTo_trans (C.op hA5 hin6 fun h => T.toCore.runsTo_mono (T.w_bin h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s6 ⟨hA6, hk6, hm6, st6⟩ => ?_
    have hk06 : T.keep C.s0 s6 := T.keep_trans hk05 hk6
    have htop6 : T.top s6 = T.top C.s0 := T.top_keepF (T.keepF_of_keep hk06)
    have hF0 : C.F0 = T.top C.s0 - 8 * (C.nS + 1) := by unfold F0; rw [htop]
    have hfr6 : T.frameAt s6 C.nS = C.F0 := by rw [T.frameAt_top, htop6, hF0]
    have hin7 := hin6.right
    have hAt7 := C.at_of hA6 hin7.left
    obtain ⟨pre, post, eW, hpre⟩ := hin7
    have hlenW := congrArg List.length eW; simp only [List.length_append] at hlenW
    have hq : (next C.pc0 (q4 + T.lenBr + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length)).toNat =
        C.pc0.toNat + 4 * pre.length := by
      rw [hpre]; exact T.toCore.pc_toNat C.codeOK (by omega)
    have hdis := C.dCW; unfold disjoint at hdis; dsimp only at hdis
    have hEl : (T.encO (.enter C.nS)).length = (T.encE C.nS).length := rfl
    have hcap0 : C.wb ≤ C.F0 := by rw [hF0, htop]; omega
    have hFt : C.F0 + 8 * (C.nS + 1) = C.wb + C.wl / 8 * 8 := by rw [hF0, htop]; omega
    refine T.toCore.runsTo_trans (T.f_enter (T.enterOK_of hns (by rw [htop6, htop]; omega)
        (by rw [htop6, htop]; omega) (by rw [htop6, ← hF0]; exact ⟨by omega, by omega⟩)) hAt7
      (by rw [hq, hfr6]; unfold disjoint; dsimp only; omega))
      fun s7 ⟨hok7, hkF7, hpc7, hfr7, hreg7, hout7, hsv7, hz7⟩ => ?_
    -- the relation for the empty memory, all registers zero
    have hm6' : T.mem s6 = T.mem C.s0 := by rw [hm6, hm5, hm04]
    have hR11 : T.get s6 RIn = BitVec.ofNat 64 C.inA := by
      rw [Core.Set1.other T.toCore st6 (by decide), hs5, keepR _ (by decide), h11]
    have hR12 : T.get s6 RLen = BitVec.ofNat 64 C.input.length := by
      rw [Core.Set1.other T.toCore st6 (by decide), hs5, keepR _ (by decide), h12]
    have hR13 : T.get s6 RHp = BitVec.ofNat 64 C.wb := by
      rw [Core.Set1.other T.toCore st6 (by decide), hs5, keepR _ (by decide), h13]
    have hR14 : T.get s6 ROut = BitVec.ofNat 64 C.outA := by
      rw [Core.Set1.other T.toCore st6 (by decide), hs5, keepR _ (by decide), h14]
    have hR10 : T.get s6 RLim = BitVec.ofNat 64 C.F0 := by
      rw [Core.Set1.same T.toCore st6, hs5, hs5, e4R0, e4R2, hF0]
      exact bv_sub _ _ (by omega) (by omega)
    have q7 : q4 + T.lenBr + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length + (T.encO (.enter C.nS)).length
        = q4 + T.lenBr + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length + (T.encE C.nS).length := rfl
    have hpos7 : C.AtQ s7 (q4 + T.lenBr + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length +
        (T.encO (.enter C.nS)).length) := ⟨hok7, by rw [q7, ← next_add]; exact hpc7, fun a h1 h2 => by
      rw [hout7 a (by intro r hr; simp at hr; subst hr; rw [hfr6]; dsimp only; omega), hm6']⟩
    have hR7 : C.MR (Mem.init C.input) (fun _ => .w 0) s7 := {
      ok := hok7
      keep := T.keepF_trans (T.keepF_of_keep hk06) hkF7
      fr := by rw [hfr7, hfr6]
      rlim := by rw [hreg7 _ (by decide)]; exact hR10
      rin := by rw [hreg7 _ (by decide)]; exact hR11
      rhp := by rw [hreg7 _ (by decide)]; simpa [Mem.init] using hR13
      cap := by simpa [Mem.init] using hcap0
      fit := hfit
      nsl := hns
      saved := by rw [← hfr6, hsv7, T.keep_fr hk06]
      slots := fun j hj => by rw [← hfr6, hz7 j hj]; rfl
      cells := fun g v h => by simp [Mem.init] at h
      out := fun i b h => by simp [Mem.init] at h
      outL := by simp [Mem.init]
      unch := hpos7.2.2
      valid := fun _ => trivial
      mok := ⟨rfl, fun k a sz lv h => by simp [Mem.init] at h, fun g v h => by simp [Mem.init] at h⟩ }
    have hin8 := hin6.right.right
    refine T.toCore.runsTo_trans (C.storeRegs_ok F.params [RIn, RLen, ROut]
      [.p 0 0, .w (BitVec.ofNat 64 C.input.length), .p 1 0] hpos7 hR7 rfl
      (fun p hp => by simpa using List.all_eq_true.1 hps p hp)
      (fun v hv => by simp at hv; rcases hv with rfl | rfl | rfl <;> simp [Valid])
      (fun i h h' => by
        match i, h with
        | 0, _ => show T.get s7 RIn = _; rw [hreg7 RIn (by decide)]; exact hR11
        | 1, _ => show T.get s7 RLen = _; rw [hreg7 RLen (by decide)]; exact hR12
        | 2, _ => show T.get s7 ROut = _; rw [hreg7 ROut (by decide)]; exact hR14) hin8) fun s8 ⟨hA8, hR8⟩ => ?_
    have hin9 := hin8.right
    have hp9 : q4 + T.lenBr + T.len exit0 + (T.encO (.w (.bin .sub RLim R0 R2))).length + (T.encO (.enter C.nS)).length +
        (T.words (storeRegs F.params [RIn, RLen, ROut])).length = T.len (T.pro C.nS F) := by
      rw [← hq4]; simp only [Target.pro2, T.words_append, Target.words, List.length_append, List.length_nil]; omega
    rw [hp9] at hin9
    have hA8' : C.AtQ s8 (T.len (T.pro C.nS F)) := hA8.congr (by rw [← hp9]; simp only [Target.len])
    refine T.toCore.runsTo_mono (C.jTo_ok hA8' hR8 hj hin9) fun s9 ⟨hA9, hR9⟩ => .inl ?_
    have hinit : init P C.input = ⟨[⟨P.main, F.entry, 0, setMany (fun _ => .w 0) F.params
        [.p 0 0, .w (BitVec.ofNat 64 C.input.length), .p 1 0], []⟩], Mem.init C.input, []⟩ := by
      unfold init; rw [hP]
    obtain ⟨B, hB⟩ : ∃ B, F.blocks.lookup F.entry = some B := by
      cases e : F.blocks.lookup F.entry with
      | some B => exact ⟨B, rfl⟩
      | none => rw [e] at hent; exact nomatch hent
    rw [hinit]
    exact C.enter_rel hK hB hA9 hR9 (fun _ h => nomatch h) rfl
  · -- the frame does not fit: `exit0`
    have hpc5 := d5.hpc
    rw [if_neg (fun h => hfit (hfitB.2 h))] at hpc5
    rw [next_add] at hpc5
    have hA5 : C.AtQ s5 (q4 + T.lenBr) := ⟨d5.ok, hpc5, hU5⟩
    have hin6 : InW C.W (q4 + T.lenBr) (T.encO (.w (.li RIn (BitVec.allOnes 64))) ++ (T.encO (.w .ret) ++
        (T.words (Target.pro2 C.nS F) ++ (T.words j ++ rest)))) := by
      simpa only [exit0, Target.words, List.append_nil, List.append_assoc] using hin5
    refine T.toCore.runsTo_trans (C.op hA5 hin6 fun h => T.toCore.runsTo_mono (T.w_li h)
      fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s6 ⟨hA6, hk6, hm6, st6⟩ => ?_
    have hra : T.ra s6 = T.ra C.s0 := by rw [T.keep_ra (T.keep_trans hk05 hk6)]
    refine T.toCore.runsTo_mono (T.w_ret (by rw [hra]; exact C.retOK) (C.at_of hA6 hin6.right.left))
      fun s7 ⟨d7, hs7, hm7⟩ => .inr ⟨by omega, d7.ok, by rw [← hra]; exact d7.hpc,
        fun a _ _ => by rw [hm7, hm6, hm5, hm04], by rw [hs7]; exact Core.Set1.same T.toCore st6⟩

/-- **emission is correct** (any target): from the start of a call, the code of `emitF` runs a terminating Lin run
of `main` to its end: back at the caller's return address, nothing changed outside the output and work blocks, and
either the output bytes are in the output block (`peak ≤ work cells`, status the input address) or the status is the
out-of-memory flag (`peak > work cells`). -/
theorem emit_ok {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} {code : List EOp}
    (hP : P.funcs[P.main]? = some F) (he : T.emitF F C.nS pos ex = some code) (hW : C.W = T.words code)
    (hok : T.ok C.s0) (hpc : T.pcIs C.s0 C.pc0) (h11 : T.get C.s0 RIn = BitVec.ofNat 64 C.inA)
    (h12 : T.get C.s0 RLen = BitVec.ofNat 64 C.input.length) (h13 : T.get C.s0 RHp = BitVec.ofNat 64 C.wb)
    (h14 : T.get C.s0 ROut = BitVec.ofNat 64 C.outA) (htop : T.top C.s0 = C.wb + C.wl / 8 * 8)
    (h16 : 16 ≤ T.top C.s0) {r : Result} (hrun : Runs P (init P C.input) r)
    (hout : r.mem.out.length ≤ C.outL) : T.runsTo C.s0 (C.Fin r) := by
  obtain ⟨j, hj, ⟨rest, hin⟩, hK⟩ := C.code_of he hW
  unfold Target.emitF at he
  split at he
  · next hc =>
    obtain ⟨hns, hns2, hent, hps, himm, hbr⟩ := hc
    refine T.toCore.runsTo_trans (C.pro_ok hP hK hj hin hns hns2 hent hps himm hbr hok hpc h11 h12 h13 h14 htop h16)
      fun s h => ?_
    rcases h with hrel | ⟨hlt, hE⟩
    · obtain ⟨n, hn⟩ := hrun; exact C.sim hP hK n hrel hn hout
    · refine T.runsTo_of ⟨hE.1, hE.2.1, hE.2.2.1, .inr ⟨?_, hE.2.2.2⟩⟩
      have := peak_append_ge r.ev [.alloc (C.nS + 1)]
      have e : peak [MemEvent.alloc (C.nS + 1)] = C.nS + 1 := by simp [peak, inUse]
      omega
  · exact nomatch he

end Ctx
end Proven.Ir

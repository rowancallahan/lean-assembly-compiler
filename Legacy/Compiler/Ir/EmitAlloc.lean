/- The out-of-memory exit, the return, and `alloc` (free cells checked against the request; out of memory exactly
when the cells in use would exceed the work block). -/
import Legacy.Compiler.Ir.EmitMem

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} (C : Ctx T)

/-- returned to the caller with the out-of-memory flag -/
def Exited (s' : T.S) : Prop :=
  T.ok s' ∧ T.pcIs s' (T.ra C.s0) ∧ C.Unch s' ∧ T.get s' RIn = BitVec.allOnes 64

variable {C}

/-- **the out-of-memory exit**: back to the caller through the stub's cell, the flag in the status register -/
theorem exit_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hin : InW C.W q (T.encO .exit ++ rest)) :
    T.runsTo s C.Exited := by
  have htop : T.top s = C.T0 := by rw [T.top_keepC hR.keep, C.htop]; rfl
  have hfit := hR.fit; have hcap := hR.cap; have hT := C.T0_le; have hal := C.T0_al
  obtain ⟨hw1, hw2⟩ := C.wR
  refine T.toCore.runsTo_mono (T.c_exit (w := T.ra C.s0) (C.at_of hA hin.left) (by rw [htop]; omega)
    (by rw [htop]; exact ⟨by omega, by omega⟩) (by rw [htop]; omega) (by rw [htop]; exact hR.stub) C.retOK)
    fun s' ⟨hok, hpc, hs, hm⟩ => ⟨hok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2, hs⟩

/-- the words before the jump to the exit -/
def allocPre (T : Target) (n : Arg Nat) : List EOp :=
  [ldArg R0 n, .w (.bin .sub R1 RLim RHp), .w (.bini .lshr R1 R1 3),
    .w (.br .geu R1 (some R0) false (T.lenBr + T.lenJ))]

/-- **`alloc`** -/
theorem alloc_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q ex : Nat} {rest rest' : List (BitVec 32)} {d : Nat}
    {n : Arg Nat} {j : EOp} {c : BitVec 64} (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS)
    (hn : okA C.nS n = true) (hi1 : T.immOK .lshr 3 = true) (hi2 : T.immOK .shl 3 = true)
    (hbr : T.brOK false (T.lenBr + T.lenJ) = true) (hj : T.jW (q + T.len (allocPre T n)) ex = some j)
    (hin : InW C.W q (T.words (allocPre T n ++ [j, .w (.stS d RHp), .w (.bini .shl R0 R0 3),
      .w (.bin .add RHp RHp R0)]) ++ rest))
    (hex : InW C.W ex (T.encO .exit ++ rest')) (hc : n.word regs = some c) :
    T.runsTo s fun s' => (C.AtQ s' (q + T.len (allocPre T n ++ [j, .w (.stS d RHp), .w (.bini .shl R0 R0 3),
      .w (.bin .add RHp RHp R0)])) ∧
      C.MR { m with cells := m.cells ++ List.replicate c.toNat none, blks := m.blks ++ [(m.cells.length, c.toNat, true)] }
        (upd regs d (.p (m.blks.length + 2) 0)) s') ∨
      (C.F0 < C.wb + 8 * (m.cells.length + c.toNat) ∧ C.Exited s') := by
  have hin0 : InW C.W q (T.words [ldArg R0 n, .w (.bin .sub R1 RLim RHp), .w (.bini .lshr R1 R1 3),
      .w (.br .geu R1 (some R0) false (T.lenBr + T.lenJ)), j, .w (.stS d RHp), .w (.bini .shl R0 R0 3),
      .w (.bin .add RHp RHp R0)] ++ rest) := hin
  have hF := hR.F0_lt; have hcap := hR.cap; have hal := hR.F0_al
  obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt; have hfit := hR.fit; have hT := C.T0_le
  refine T.toCore.runsTo_trans (C.ldArg_ok hA hR hin0.cons (by decide) hn) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA1 hR1 hin0.next.cons (by decide) fun h => T.w_bin h)
    fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin0.next.next.cons (by decide) fun h => T.w_bini hi1 h)
    fun s3 ⟨hA3, hR3, st3⟩ => ?_
  have e0 : T.get s3 R0 = c := by
    rw [Core.Set1.other T.toCore st3 (by decide), Core.Set1.other T.toCore st2 (by decide),
      Core.Set1.same T.toCore st1, Arg.word_eval hc]; rfl
  have e1 : T.get s3 R1 = BitVec.ofNat 64 ((C.F0 - (C.wb + 8 * m.cells.length)) / 8) := by
    rw [Core.Set1.same T.toCore st3, Core.Set1.same T.toCore st2, Core.Set1.other T.toCore st1 (by decide),
      Core.Set1.other T.toCore st1 (by decide), hR.rlim, hR.rhp, bv_sub _ _ hcap (by omega), bv_lshr3 _ (by omega)]
  refine T.toCore.runsTo_trans (C.br_ok hA3 hR3 hin0.next.next.next.cons hbr (fun h => nomatch h))
    fun s4 ⟨hR4, hs4, ht, hf⟩ => ?_
  simp only [Bool.false_eq_true, if_false] at ht
  rw [e0, e1] at ht hf
  have hfree : (C.F0 - (C.wb + 8 * m.cells.length)) / 8 < 2 ^ 64 := by omega
  by_cases hfits : c.toNat ≤ (C.F0 - (C.wb + 8 * m.cells.length)) / 8
  · -- fits: skip the jump, then the new block
    have hA4 := ht (by
      simp only [Cond.eval, Bool.not_eq_true']
      apply decide_eq_false
      intro hlt'
      rw [BitVec.lt_def, ofNat_toNat' hfree] at hlt'; omega)
    have hlj := jW_len hj
    have hin4 := hin0.next.next.next.next.next
    rw [hlj, T.len_brO] at hin4
    have epos : q + (T.encO (ldArg R0 n)).length + (T.encO (.w (.bin .sub R1 RLim RHp))).length +
        (T.encO (.w (.bini .lshr R1 R1 3))).length + (T.lenBr + T.lenJ) =
        q + (T.encO (ldArg R0 n)).length + (T.encO (.w (.bin .sub R1 RLim RHp))).length +
        (T.encO (.w (.bini .lshr R1 R1 3))).length + T.lenBr + T.lenJ := by omega
    rw [epos] at hA4
    obtain ⟨-, hram, hsal, -, htop⟩ := hR4.slot hd
    have efr : (T.fr s4).toNat + 8 * (d + 1) = C.F0 + 8 * (d + 1) := (hR4.slot hd).1
    refine T.toCore.runsTo_trans (C.opW hA4 hin4.cons (fun h => T.w_stS (Nat.lt_of_lt_of_le hd hR4.nsl) h
        (by rw [efr]; exact hram) (by rw [efr]; exact hsal)
        (fun i hi => C.wr _ _ (.inr ⟨by rw [efr]; omega, by rw [efr]; omega⟩)))
      (fun s' ⟨_, hm⟩ => unch_work hA4.2.2 hm (by rw [efr]; omega) (by rw [efr, length_le8]; omega)))
      fun s5 ⟨hA5, hk5, hs5, hm5⟩ => ?_
    refine T.toCore.runsTo_trans (C.op hA5 hin4.next.cons fun h => T.toCore.runsTo_mono (T.w_bini hi2 h)
      fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s6 ⟨hA6, hk6, hm6, st6⟩ => ?_
    refine T.toCore.runsTo_mono (C.op hA6 hin4.next.next.cons fun h => T.toCore.runsTo_mono (T.w_bin h)
      fun s' ⟨d', st, hm⟩ => ⟨d', hm, st⟩) fun s7 ⟨hA7, hk7, hm7, st7⟩ => ?_
    left
    have e40 : T.get s4 R0 = c := by rw [hs4, e0]
    have e6 : T.get s6 R0 = BitVec.ofNat 64 (8 * c.toNat) := by
      rw [Core.Set1.same T.toCore st6, hs5, e40]; exact bv_shl3 c
    have hhp : T.get s6 RHp = BitVec.ofNat 64 (C.wb + 8 * m.cells.length) := by
      rw [Core.Set1.other T.toCore st6 (by decide), hs5]; exact hR4.rhp
    refine ⟨hA7.congr ?_, hR4.alloc hd (by omega) hA7.1
      (T.keep_trans hk5 (T.keep_trans hk6 hk7))
      (by rw [Core.Set1.other T.toCore st7 (by decide), Core.Set1.other T.toCore st6 (by decide), hs5])
      (by rw [Core.Set1.other T.toCore st7 (by decide), Core.Set1.other T.toCore st6 (by decide), hs5])
      (by rw [Core.Set1.same T.toCore st7, hhp, e6]; show BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = _; rw [bv_ofNat_add]; congr 1; omega)
      (by rw [hm7, hm6, hm5, efr, hR4.rhp])⟩
    simp only [allocPre, Target.len, Target.words, List.length_append, List.length_nil, List.cons_append,
      List.nil_append, T.len_brO, hlj]
    omega
  · -- does not fit: to the exit
    have hA4 := hf (by
      simp only [Cond.eval, Bool.not_eq_false']
      apply decide_eq_true
      rw [BitVec.lt_def, ofNat_toNat' hfree]; omega)
    have hin4 := hin0.next.next.next.next
    rw [T.len_brO] at hin4
    have epos : q + (T.encO (ldArg R0 n)).length + (T.encO (.w (.bin .sub R1 RLim RHp))).length +
        (T.encO (.w (.bini .lshr R1 R1 3))).length + T.lenBr = q + T.len (allocPre T n) := by
      simp only [allocPre, Target.len, Target.words, List.length_append, List.length_nil, T.len_brO]; omega
    rw [epos] at hA4 hin4
    refine T.toCore.runsTo_trans (C.jW_ok hA4 hR4 hj hin4.cons) fun s5 ⟨hA5, hR5, _⟩ => ?_
    refine T.toCore.runsTo_mono (C.exit_ok hA5 hR5 hex) fun s6 h6 => .inr ⟨?_, h6⟩
    omega

end Ctx
end Proven.Ir

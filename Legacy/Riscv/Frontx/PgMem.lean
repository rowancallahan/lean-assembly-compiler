/- Paged arrays (NOTES section 35), the `a0` flag: an entry stub around the paged body (`Implements1PgQ`).

The stub (10 words, then the body):
```
0: sub  t0, sp, a2        t0 = work length
1: srli t0, t0, 13        whole pages of 8192 bytes
2: beq  t0, x0, 8         no page: out of memory without running the body
3: mv   s1, ra            the body keeps s1 (callee-saved)
4: jal  ra, 10            the body
5: mv   ra, s1
6: addi a0, a7, -1        a7 = vOk: 1 → a0 = 0, 0 → a0 = -1
7: ret
8: addi a0, x0, -1
9: ret
```
`s1` is not preserved by the stub (the `AllocSpec` statements do not ask for callee-saved registers); keeping `ra`
in `s1` instead of the work block leaves the body the whole work block, so `memoryNeeded` stays `8192 * (peak + 1)`.
`stub_run`: the stub with the body returns to the caller, changes only the output prefix and the work block, and
`a0 = -1` exactly when the run does not fit (`fits`), else `a0 = 0` and the output. -/
import Legacy.Riscv.Frontx.WpImpl
import Nano.Base.Riscv.Back.Top
import Nano.Base.Compiler.AllocSpec

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Proven.Mach.Riscv
open Proven LeanRV64D

/-- the entry stub -/
def pgStub : List (BitVec 32) :=
  [ encR 0x20 0 5 2 12,
    encI 5 (0 <<< 6 ||| (13#6).toNat) 5 5,
    wB 0 (.ofFin 5) (.ofFin 0) 12#12,
    encR 0 0 9 0 1,
    wJ (.ofFin 1) 12#20,
    encR 0 0 1 0 9,
    encI 0 (0xfff#12).toNat 10 17,
    iRet,
    encI 0 (0xfff#12).toNat 10 0,
    iRet ]

theorem pgStub_length : pgStub.length = 10 := rfl

/-- word `i` of the code at `e` -/
abbrev PA (e : BitVec 64) (i : Nat) : BitVec 64 := e + BitVec.ofNat 64 (4 * i)

theorem PA_succ (e : BitVec 64) (i : Nat) : PA e i + 4 = PA e (i + 1) := pc_add e i 1

theorem PA_toNat {e : BitVec 64} {i : Nat} (h : e.toNat + 4 * i < 2 ^ 64) : (PA e i).toNat = e.toNat + 4 * i := by
  simp only [PA, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem instrAt_keep {s s' : St} {pc : BitVec 64} {w : BitVec 32}
    (hk : ∀ k, k < 4 → s'.mem[pc.toNat + k]? = s.mem[pc.toNat + k]?) (h : instrAt s pc w) : instrAt s' pc w := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hk 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact h0
  · rw [hk 1 (by omega)]; exact h1
  · rw [hk 2 (by omega)]; exact h2
  · rw [hk 3 (by omega)]; exact h3

theorem codeBytes_app (a b : List (BitVec 32)) : codeBytes (a ++ b) = codeBytes a ++ codeBytes b := by
  simp [codeBytes, List.flatMap_append]

theorem getX_nx {s s' : St} {pc rd v m} (n : Next s s' pc rd v m) (j : Fin 32) :
    getX s' j = if j = rd ∧ j ≠ 0 then v else getX s j := n.x j

/-- **The stub around a paged body**: for any work block (also below one page), the code returns to the caller,
changes nothing outside the output prefix and the work block, and `a0 = -1` exactly when the run does not fit;
when it fits, `a0 = 0` and the output -/
theorem stub_run {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {code : List (BitVec 32)}
    {f : α → β} {fits : α → Nat → Prop} {maxLen : Nat} {retLen : Bool}
    (hbody : Implements1PgQ encA encB code f 8192 fits (Proven.WA.okQ fits) maxLen retLen)
    (hsmall : ∀ a L, L < 8192 → ¬ fits a L) :
    ∀ (a : α) (s : St) (entry ra : BitVec 64) (input output work : Proven.Region),
    let x := encA a
    let y := encB (f a)
    let codeR : Proven.Region := ⟨entry.toNat, 4 * (pgStub ++ code).length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * (pgStub ++ code).length) = codeBytes (pgStub ++ code) →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → Proven.disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → y.length ≤ output.len → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise Proven.disjoint →
    Mapped s output → Mapped s work →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧ Cfg s' ∧
      unchangedOutside s s' [⟨output.base, y.length⟩, work] ∧
      (fits a work.len → bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧ getX s' 10 = 0) ∧
      (¬ fits a work.len → getX s' 10 = BitVec.allOnes 64) := by
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  obtain ⟨ri, ro, rw', rc⟩ := hin
  have hdis' := hdis
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis'
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis'
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34 hrad
  simp only [codeR, List.length_append, pgStub_length] at rc d14 d24 d34 hrad
  have hok : codeOK entry (pgStub ++ code).length := ⟨hal, by omega, by simp [pgStub_length]; omega⟩
  have hca := codeAt_of_codeBytes hok hcode
  obtain ⟨hcs, hcb⟩ := codeAt_append.1 hca
  rw [pgStub_length] at hcb
  have hP : ∀ i, i ≤ 10 → (PA entry i).toNat = entry.toNat + 4 * i := fun i hi => PA_toNat (by omega)
  have hpcok : ∀ i, i < 10 → pcOK (PA entry i) := fun i hi => by
    refine ⟨?_, ?_, ?_⟩ <;> rw [hP i (by omega)] <;> omega
  -- the stub's words stay in place while nothing in the code region changes
  have hI : ∀ (t : St) (i : Nat) (hi : i < 10), (∀ q, entry.toNat ≤ q → q < entry.toNat + 40 → t.mem[q]? = s.mem[q]?) →
      instrAt t (PA entry i) (pgStub[i]'(by rw [pgStub_length]; exact hi)) := by
    intro t i hi hm
    refine instrAt_keep (fun k hk => ?_) (hcs i (by rw [pgStub_length]; exact hi))
    rw [hP i (by omega)]; exact hm _ (by omega) (by omega)
  have hsame : ∀ t : St, t.mem = s.mem → ∀ q, entry.toNat ≤ q → q < entry.toNat + 40 → t.mem[q]? = s.mem[q]? :=
    fun t ht q _ _ => by rw [ht]
  have hpc0 : s.regs.get? .PC = some (PA entry 0) := by rw [hpc]; simp [PA]
  have g2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have g12 : getX s 12 = BitVec.ofNat 64 work.base := getX_of (h.x12.symm.trans h12) rfl
  have g1 : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  -- 0: sub t0, sp, a2
  obtain ⟨s1, n1⟩ := G.step_sub h hpc0 (hpcok 0 (by omega)) 5 2 12 (hI s 0 (by omega) (hsame s rfl))
  -- 1: srli t0, t0, 13
  obtain ⟨s2, n2⟩ := G.step_srli n1.cfg (by rw [n1.pc, PA_succ]) (hpcok 1 (by omega)) 5 5 13#6
    (hI s1 1 (by omega) (hsame s1 n1.mem))
  have ht0 : getX s2 5 = BitVec.ofNat 64 (work.len / 8192) := by
    rw [getX_nx n2, if_pos ⟨rfl, by decide⟩, getX_nx n1, if_pos ⟨rfl, by decide⟩, g2, g12]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, Nat.reduceMod]
    omega
  have m2 : s2.mem = s.mem := by rw [n2.mem, n1.mem]
  have k2 : ∀ j : Fin 32, j ≠ 5 → getX s2 j = getX s j := fun j hj => by
    rw [getX_nx n2, if_neg (fun e => hj e.1), getX_nx n1, if_neg (fun e => hj e.1)]
  by_cases hL : work.len < 8192
  · -- 2: beq t0, x0 (taken), 8: addi a0, x0, -1, 9: ret
    obtain ⟨s3, n3⟩ := G.beq_t n2.cfg (by rw [n2.pc, PA_succ]) (hpcok 2 (by omega)) 5 0 12#12
      (hI s2 2 (by omega) (hsame s2 m2)) (by
        rw [ht0, G.getX_zero]; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]; omega)
    have hb : PA entry 2 + boff 12#12 = PA entry 8 := by
      apply BitVec.eq_of_toNat_eq; rw [hP 8 (by omega), BitVec.toNat_add, hP 2 (by omega)]
      have : (boff 12#12).toNat = 24 := by decide
      rw [this]; omega
    obtain ⟨s4, n4⟩ := G.step_addi n3.cfg (by rw [n3.pc, hb]) (hpcok 8 (by omega)) 10 0 0xfff#12
      (hI s3 8 (by omega) (hsame s3 (by rw [n3.mem, m2])))
    have g1' : getX s4 1 = ra := by
      rw [getX_nx n4, if_neg (by decide), getX_nx n3, if_neg (by decide), k2 1 (by decide), g1]
    obtain ⟨s5, n5⟩ := G.step_ret' n4.cfg (by rw [n4.pc, PA_succ]) (hpcok 9 (by omega))
      (hI s4 9 (by omega) (hsame s4 (by rw [n4.mem, n3.mem, m2]))) (by rw [g1']; omega)
    refine runsTo_next n1 (runsTo_next n2 (runsTo_next n3 (runsTo_next n4 (runsTo_next n5 ⟨0, s5, rfl, ?_⟩))))
    refine ⟨by rw [n5.pc, g1'], n5.cfg, fun q _ => by rw [n5.mem, n4.mem, n3.mem, m2], fun hf => absurd hf
      (hsmall a _ hL), fun _ => ?_⟩
    rw [getX_nx n5, if_neg (by decide), getX_nx n4, if_pos ⟨rfl, by decide⟩, G.getX_zero]; decide
  · -- 2: beq (not taken), 3: mv s1, ra, 4: jal ra, body
    obtain ⟨s3, n3⟩ := G.beq_n n2.cfg (by rw [n2.pc, PA_succ]) (hpcok 2 (by omega)) 5 0 12#12
      (hI s2 2 (by omega) (hsame s2 m2)) (by
        rw [ht0, G.getX_zero]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega)
    obtain ⟨s4, n4⟩ := G.step_mv n3.cfg (by rw [n3.pc, PA_succ]) (hpcok 3 (by omega)) 9 1 (by decide)
      (hI s3 3 (by omega) (hsame s3 (by rw [n3.mem, m2])))
    obtain ⟨s5, n5⟩ := G.step_jal n4.cfg (by rw [n4.pc, PA_succ]) (hpcok 4 (by omega)) 1 12#20
      (hI s4 4 (by omega) (hsame s4 (by rw [n4.mem, n3.mem, m2])))
    have m5 : s5.mem = s.mem := by rw [n5.mem, n4.mem, n3.mem, m2]
    have hj : PA entry 4 + joff 12#20 = PA entry 10 := by
      apply BitVec.eq_of_toNat_eq; rw [hP 10 (by omega), BitVec.toNat_add, hP 4 (by omega)]
      have : (joff 12#20).toNat = 24 := by decide
      rw [this]; omega
    have k5 : ∀ j : Fin 32, j ≠ 1 → j ≠ 5 → j ≠ 9 → getX s5 j = getX s j := fun j a b c => by
      rw [getX_nx n5, if_neg (fun e => a e.1), getX_nx n4, if_neg (fun e => c e.1), getX_nx n3,
        if_neg (by simp), k2 j b]
    have g9 : getX s5 9 = ra := by
      rw [getX_nx n5, if_neg (by decide), getX_nx n4, if_pos ⟨rfl, by decide⟩, getX_nx n3, if_neg (by decide),
        k2 1 (by decide), g1]
    have g1r : getX s5 1 = PA entry 5 := by
      rw [getX_nx n5, if_pos ⟨rfl, by decide⟩, PA_succ]
    have hbody' := hbody a s5 (PA entry 10) (PA entry 5) input output work hmax n5.cfg
      (by rw [n5.pc, hj]) (by rw [hP 10 (by omega)]; omega)
      (by
        have e := hcode
        rw [codeBytes_app] at e
        rw [List.length_append, pgStub_length] at e
        rw [Nat.mul_add] at e
        rw [bytesAt_append] at e
        obtain ⟨-, e2⟩ := List.append_inj e (by simp [bytesAt, codeBytes, pgStub])
        unfold bytesAt at e2 ⊢; rw [m5, hP 10 (by omega)]; exact e2)
      (by rw [n5.cfg.x10, k5 10 (by decide) (by decide) (by decide)]; exact h.x10.symm.trans h10)
      (by rw [n5.cfg.x11, k5 11 (by decide) (by decide) (by decide)]; exact h.x11.symm.trans h11)
      (by rw [n5.cfg.x12, k5 12 (by decide) (by decide) (by decide)]; exact h.x12.symm.trans h12)
      (by rw [n5.cfg.x13, k5 13 (by decide) (by decide) (by decide)]; exact h.x13.symm.trans h13)
      (by rw [n5.cfg.x2, k5 2 (by decide) (by decide) (by decide)]; exact h.x2.symm.trans h2)
      (by rw [n5.cfg.x1, g1r]) (by rw [hP 5 (by omega)]; omega)
      (by unfold Proven.disjoint; dsimp only; rw [hP 5 (by omega), hP 10 (by omega)]; omega)
      (by unfold bytesAt; rw [m5]; exact hx) hil hol (by omega) hwal
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.inRAM]
        rw [hP 10 (by omega)]; omega)
      (by
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          List.Pairwise.nil, and_true, Proven.disjoint]
        rw [hP 10 (by omega)]
        refine ⟨⟨d12, d13, ?_⟩, ⟨d23, ?_⟩, ?_⟩
        all_goals first | omega | exact ⟨by omega, fun _ h => h.elim⟩)
      (fun i hi => by show (s5.mem[_]?).isSome; rw [m5]; exact hmapO i hi)
      (fun i hi => by show (s5.mem[_]?).isSome; rw [m5]; exact hmapW i hi)
    refine runsTo_next n1 (runsTo_next n2 (runsTo_next n3 (runsTo_next n4 (runsTo_next n5
      (runsTo_trans hbody' ?_)))))
    rintro s6 ⟨p1, p2, p3, p5, p6, -, v, p7, p8⟩
    -- the stub region is untouched by the body
    have hm6 : ∀ q, entry.toNat ≤ q → q < entry.toNat + 40 → s6.mem[q]? = s.mem[q]? := fun q h1 h2 => by
      rw [p2 q (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with e | e <;> rw [e]
        · show q < output.base ∨ output.base + y.length ≤ q; omega
        · show q < work.base ∨ work.base + work.len ≤ q; omega), m5]
    have g9' : getX s6 9 = ra := by
      have e := p3 .x9 (by simp)
      rw [p5.x9, n5.cfg.x9, g9] at e
      exact Option.some.inj e
    obtain ⟨s7, n7⟩ := G.step_mv p5 (by rw [p1, ← PA_succ, ← PA_succ]) (hpcok 5 (by omega)) 1 9 (by decide)
      (hI s6 5 (by omega) hm6)
    obtain ⟨s8, n8⟩ := G.step_addi n7.cfg (by rw [n7.pc, PA_succ]) (hpcok 6 (by omega)) 10 17 0xfff#12
      (hI s7 6 (by omega) (fun q a b => by rw [n7.mem]; exact hm6 q a b))
    have g1'' : getX s8 1 = ra := by
      rw [getX_nx n8, if_neg (by decide), getX_nx n7, if_pos ⟨rfl, by decide⟩, g9']
    obtain ⟨s9, n9⟩ := G.step_ret' n8.cfg (by rw [n8.pc, PA_succ]) (hpcok 7 (by omega))
      (hI s8 7 (by omega) (fun q a b => by rw [n8.mem, n7.mem]; exact hm6 q a b)) (by rw [g1'']; omega)
    have m9 : s9.mem = s6.mem := by rw [n9.mem, n8.mem, n7.mem]
    have g17 : getX s6 17 = v := by rw [p5.x17] at p7; exact (Option.some.inj p7)
    have g10 : getX s9 10 = v + (0xfff#12).signExtend 64 := by
      rw [getX_nx n9, if_neg (by decide), getX_nx n8, if_pos ⟨rfl, by decide⟩, getX_nx n7, if_neg (by decide), g17]
    refine runsTo_next n7 (runsTo_next n8 (runsTo_next n9 ⟨0, s9, rfl, ?_⟩))
    refine ⟨by rw [n9.pc, g1''], n9.cfg, fun q hq => by rw [m9, p2 q hq, m5], fun hf => ?_, fun hf => ?_⟩
    · refine ⟨by unfold bytesAt; rw [m9]; exact (p6 hf).1, ?_⟩
      rw [g10, p8.1 hf]; decide
    · rw [g10, p8.2 hf]; decide

end Proven.Mach.Riscv

namespace Proven.Top
open Proven.Mach.Riscv Proven.Top.Alloc

/-- **The stub from `StartCorrect`**: the code returns to the caller, changes nothing outside the output and work
blocks, and the status register is `oomFlag` exactly when the run does not fit; when it fits, the output -/
theorem stub_top {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {code : List (BitVec 32)}
    {f : α → β} {fits : α → Nat → Prop} {retLen : Bool}
    {maxLen : Nat} (hbody : Implements1PgQ encA encB code f 8192 fits (Proven.WA.okQ fits) maxLen retLen)
    (hsmall : ∀ a L, L < 8192 → ¬ fits a L) {argument : α} {startState : St} {call : Call}
    (hmax : (encA argument).length ≤ maxLen)
    (startsRight : StartCorrect riscv startState call (wordBytes (pgStub ++ code)) (encA argument))
    (outputFits : (encB (f argument)).length ≤ call.outputLength) :
    ∃ finishState : St, Runs riscv startState finishState ∧
      (riscvObserve finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscvObserve finishState).memory address = (riscvObserve startState).memory address) ∧
      (fits argument call.workLength → (riscvObserve finishState).register 10 ≠ oomFlag ∧
        readMemory (riscvObserve finishState) call.outputAddress (encB (f argument)).length
          = some (encB (f argument))) ∧
      (¬ fits argument call.workLength → (riscvObserve finishState).register 10 = oomFlag) := by
  obtain ⟨configured, codeLoaded, inputLoaded, inputLength, inputSmall, returnRegister, inputRegister,
    lengthRegister, workRegister, workTopRegister, outputRegister, codeAligned, returnAligned, workAligned,
    returnOutsideCode, inRam, disjoint, outputPresent, workPresent⟩ := startsRight
  change Cfg startState at configured
  have eObserve : riscv.observe = riscvObserve := rfl
  have eMapping : riscv.mapping = riscvMapping := rfl
  have eStart : riscv.ramStart = 0x80000000 := rfl
  have eEnd : riscv.ramEnd = 0x100000000 := rfl
  simp only [eObserve, eMapping, eStart, eEnd, riscvMapping, Call.blocks, wordBytes_length] at *
  generalize hpc : (riscvObserve startState).programCounter = pc at *
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at inRam
  obtain ⟨⟨ri1, ri2⟩, ⟨ro1, ro2⟩, ⟨rw1, rw2⟩, ⟨rc1, rc2⟩⟩ := inRam
  have hreg := fun (register : LeanRV64D.Register) hregister => isSome_of_cfg configured (register := register) hregister
  have hpcReg := register_of (hreg .PC (by simp)) hpc
  have hentry : (BitVec.ofNat 64 pc.toNat).toNat = pc.toNat := by simp
  have hra : (BitVec.ofNat 64 call.returnAddress.toNat).toNat = call.returnAddress.toNat := by simp
  have hcode := (readMemory_riscv startState (address := pc) (length := (wordBytes (pgStub ++ code)).length) _
    (by rw [wordBytes_length]; omega)).1 (by rw [wordBytes_length]; exact codeLoaded)
  rw [wordBytes_length, wordBytes_codeBytes] at hcode
  have hinput := (readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1 inputLoaded
  have run := stub_run hbody hsmall argument startState (BitVec.ofNat 64 pc.toNat)
    (BitVec.ofNat 64 call.returnAddress.toNat)
    ⟨call.inputAddress.toNat, call.inputLength⟩ ⟨call.outputAddress.toNat, call.outputLength⟩
    ⟨call.workAddress.toNat, call.workLength⟩ hmax configured hpcReg (by rw [hentry]; exact codeAligned)
    (by rw [hentry]; exact hcode)
    (register_of (hreg .x10 (by simp)) inputRegister)
    (by have := register_of (hreg .x11 (by simp)) lengthRegister
        rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
    (register_of (hreg .x12 (by simp)) workRegister)
    (register_of (hreg .x13 (by simp)) outputRegister)
    (by have := register_of (hreg .x2 (by simp)) workTopRegister
        rw [this, toNat_add_offset (bound := call.workLength + 1) (by omega) (by omega)])
    (register_of (hreg .x1 (by simp)) returnRegister) (by rw [hra]; exact returnAligned)
    (by rw [hra, hentry]; exact returnOutsideCode) hinput inputLength outputFits workAligned
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.inRAM, hentry]
      omega)
    (by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, Proven.disjoint, Apart, hentry, false_implies, implies_true] at disjoint ⊢
      simpa only [] using disjoint)
    (fun offset (hoffset : offset < call.outputLength) => by
      have := outputPresent offset hoffset
      simp only [riscvObserve, Option.isSome_map] at this
      rwa [toNat_add_offset (by omega) hoffset] at this)
    (fun offset (hoffset : offset < call.workLength) => by
      have := workPresent offset hoffset
      simp only [riscvObserve, Option.isSome_map] at this
      rwa [toNat_add_offset (by omega) hoffset] at this)
  obtain ⟨steps, finishState, hsteps, hpcFinish, hcfg, hunchanged, hfit, hnofit⟩ := run
  have hx10 : ∀ v, getX finishState 10 = v → (riscvObserve finishState).register 10 = UInt64.ofBitVec v := by
    intro v hv; simp only [riscvObserve, riscvRegister, hcfg.x10, hv, Option.map_some, Option.getD_some]
  refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, fun hf => ?_, fun hf => ?_⟩
  · simp [riscvObserve, hpcFinish]
  · intro address hout hwork
    simp only [riscvObserve]
    rw [hunchanged address.toNat (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      unfold Outside at hout hwork
      simp only at hout hwork
      exact ⟨by show _ ∨ _; omega, hwork⟩)]
  · obtain ⟨hb, h0⟩ := hfit hf
    refine ⟨by rw [hx10 _ h0]; decide, ?_⟩
    exact (readMemory_riscv finishState (address := call.outputAddress) _ (by omega)).2 hb
  · rw [hx10 _ (hnofit hf)]; rfl

end Proven.Top

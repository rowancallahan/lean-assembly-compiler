/- The call interface `MachineC` (`Compiler/Call.lean`) on DeepMind's AArch64 semantics:
`apcC L : MachineC` over `apcF L`.  Link register x30, frame register x28.
`call d` = `bl #4d` (`-2^25 ≤ d < 2^25`, symbolic decoding), `enterC n` = `sub x28, x28, #8(n+1); str x30, [x28]`,
`leaveC n` = `ldr x30, [x28]; add x28, x28, #8(n+1)`, `stA m v` = `stur xv, [x28, #-8m]`. -/
import Apc.Frame
import Nano.Base.Compiler.CProg
namespace Proven.Apc
open Proven Proven.Mach

/-! ## Words -/
def wBl (d : Int) : BitVec 32 := 0x25#6 ++ BitVec.ofInt 26 d                                         -- bl #4d
def wSubFr (n : Nat) : BitVec 32 := BitVec.ofNat 32 (0xD1000000 ||| (8 * (n + 1)) <<< 10 ||| 28 <<< 5 ||| 28)
def wAddFr (n : Nat) : BitVec 32 := BitVec.ofNat 32 (0x91000000 ||| (8 * (n + 1)) <<< 10 ||| 28 <<< 5 ||| 28)
def wStur (t m : Nat) : BitVec 32 := BitVec.ofNat 32 (0xF8000000 ||| ((512 - 8 * m) % 512) <<< 12 ||| 28 <<< 5 ||| t)

def encC : COp → List (BitVec 32)
  | .call d => [wBl d]
  | .enterC n => [wSubFr n, wStr 30 28 0]
  | .leaveC n => [wLdr 30 28 0, wAddFr n]
  | .stA m v => [wStur (xn v) m]

/-! ## Decoding -/
theorem dec_bl (d : Int) (hd : -2 ^ 25 ≤ d ∧ d < 2 ^ 25) :
    Arm64.decode (wBl d) = some (.bl (BitVec.ofInt 64 (4 * d))) := by
  rw [wBl, dec_blsym]
  by_cases h0 : 0 ≤ d
  · have e : BitVec.ofInt 26 d = BitVec.ofNat 26 d.toNat := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
    rw [e, off_fwd (w := 26) (by decide) (by decide) (by omega)]
    congr 2; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
  · have e : BitVec.ofInt 26 d = BitVec.ofNat 26 (2 ^ 26 - (-d).toNat) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
    rw [e, off_back (w := 26) (by decide) (by decide) (by omega) (by omega)]
    congr 2; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
theorem dec_subfr : ∀ n : Fin 17, Arm64.decode (wSubFr n.val) =
    some (.addSubImm .W64 .SUB (.gpr 28#5) (.gpr 28#5) (BitVec.ofNat 12 (8 * (n.val + 1))) false) := by decide +kernel
theorem dec_addfr : ∀ n : Fin 17, Arm64.decode (wAddFr n.val) =
    some (.addSubImm .W64 .ADD (.gpr 28#5) (.gpr 28#5) (BitVec.ofNat 12 (8 * (n.val + 1))) false) := by decide +kernel
theorem dec_str30 : Arm64.decode (wStr 30 28 0) = some (.str .X64 (.gpr 30#5) (.Offset (.gpr 28#5) 0#64)) := by decide
theorem dec_ldr30 : Arm64.decode (wLdr 30 28 0) = some (.ldr .W64 .X64 false (.gpr 30#5) (.Offset (.gpr 28#5) 0#64)) := by
  decide
theorem dec_stur : ∀ (v : Mach.Reg) (m : Fin 17), 1 ≤ m.val → Arm64.decode (wStur (xn v) m.val) =
    some (.str .X64 (.gpr (xr v)) (.UnscaledOffset (.gpr 28#5) (BitVec.ofNat 64 (2 ^ 64 - 8 * m.val)))) := by
  decide +kernel

/-! ## Evaluation -/
theorem ev_bl (off : BitVec 64) (s : Arm64.State) :
    P.evalInst (.bl off) s = { s with regs := s.regs.write 30#5 (s.pc + 4#64), pc := s.pc + off } := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.writeReg64, Arm64.State.setPC, Arm64.Reg.lr]

theorem setW12 (k : Nat) (hk : k < 4096) : (BitVec.ofNat 12 k).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem ev_subi (t n : BitVec 5) (k : Nat) (hk : k < 4096) (s : Arm64.State) (ht : (t == 31#5) = false)
    (hn : (n == 31#5) = false) :
    P.evalInst (.addSubImm .W64 .SUB (.gpr t) (.gpr n) (BitVec.ofNat 12 k) false) s =
      { s with regs := s.regs.write t (s.regs.read n - BitVec.ofNat 64 k), pc := s.pc + 4#64 } := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.evalAddSub, Arm64.AddWithCarry64,
    ht, hn, Arm64.RegFile.read, setW12 k hk, sub_res]
theorem ev_addi (t n : BitVec 5) (k : Nat) (hk : k < 4096) (s : Arm64.State) (ht : (t == 31#5) = false)
    (hn : (n == 31#5) = false) :
    P.evalInst (.addSubImm .W64 .ADD (.gpr t) (.gpr n) (BitVec.ofNat 12 k) false) s =
      { s with regs := s.regs.write t (s.regs.read n + BitVec.ofNat 64 k), pc := s.pc + 4#64 } := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.evalAddSub, Arm64.AddWithCarry64,
    ht, hn, Arm64.RegFile.read, setW12 k hk, add_res]

theorem ev_stur (t n : BitVec 5) (off : BitVec 64) (s : Arm64.State) (ht : (t == 31#5) = false) (hn : (n == 31#5) = false)
    (hw : s.mem.canWrite (s.regs.read n + off) 8 = true) :
    P.evalInst (.str .X64 (.gpr t) (.UnscaledOffset (.gpr n) off)) s =
      { s with mem := s.mem.write64 (s.regs.read n + off) (s.regs.read t), pc := s.pc + 4#64 } := by
  have hw' : s.mem.canWrite (s.regs.regs n + off) 8 = true := hw
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.setMem, Arm64.State.advancePC, Arm64.Memory.writeSized, ht, hn,
    Arm64.RegFile.read, hw', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

/-! ## Laws -/
def keepCS : Arm64.State → Arm64.State → Prop := keepX fun x => x = 28#5 ∨ x = 30#5

theorem law_call {L : Lay} {d : Int} {s : Arm64.State} {pc : BitVec 64} (hd : -2 ^ 25 ≤ d ∧ d < 2 ^ 25)
    (h : (base L).At s pc (encC (.call d))) :
    (base L).runsTo s fun s' => (base L).ok s' ∧ keepCS s s' ∧ (base L).pcIs s' (pc + BitVec.ofInt 64 (4 * d)) ∧
      s'.regs.read 30#5 = next pc 1 ∧ s'.regs.read 28#5 = s.regs.read 28#5 ∧ (base L).Same s s' ∧
      (base L).mem s' = (base L).mem s := by
  refine run1 h (dec_bl d hd) ?_
  rw [ev_bl]
  refine ⟨okS_of h.ok rfl rfl, ⟨fun x _ hx => ?_, rfl⟩, ?_, ?_, ?_, fun r => ?_, rfl⟩
  · have : x ≠ 30#5 := fun e => hx (.inr e)
    simp [Arm64.RegFile.read, Arm64.RegFile.write, this]
  · show s.pc + _ = _; rw [show s.pc = pc from h.hpc]
  · simp [Arm64.RegFile.read, Arm64.RegFile.write, show s.pc = pc from h.hpc, next]
  · simp [Arm64.RegFile.read, Arm64.RegFile.write]
  · simp [base, getR, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne30 r]

theorem law_enterC {L : Lay} {n : Nat} {s : Arm64.State} {pc : BitVec 64} (hn : n ≤ 16)
    (h : (base L).At s pc (encC (.enterC n))) (h8 : 8 * (n + 1) ≤ (s.regs.read 28#5).toNat)
    (hr : (base L).inRAM ((s.regs.read 28#5).toNat - 8 * (n + 1)) 8) (_ : (s.regs.read 28#5).toNat % 8 = 0)
    (hw : ∀ i, i < 8 → (base L).writable s ((s.regs.read 28#5).toNat - 8 * (n + 1) + i)) :
    (base L).runsTo s fun s' => (base L).ok s' ∧ keepCS s s' ∧ (base L).pcIs s' (next pc (encC (.enterC n)).length) ∧
      s'.regs.read 28#5 = BitVec.ofNat 64 ((s.regs.read 28#5).toNat - 8 * (n + 1)) ∧ (base L).Same s s' ∧
      (base L).mem s' = ((base L).mem s).wr ((s.regs.read 28#5).toNat - 8 * (n + 1)) (le8 (s.regs.read 30#5)) := by
  obtain ⟨hok, hpc, hal, i1, i2⟩ := at2 h
  have hco : pc.toNat + 4 * 2 ≤ 2 ^ 64 - 1 := h.codeOK.2.2
  have e4 : (pc + 4#64).toNat = pc.toNat + 4 := by rw [BitVec.toNat_add]; simp; omega
  have st1 := exec_ok hok hpc hal i1 (dec_subfr ⟨n, by omega⟩)
  rw [ev_subi 28#5 28#5 _ (by omega) s rfl rfl] at st1
  have ef : s.regs.read 28#5 - BitVec.ofNat 64 (8 * (n + 1)) = BitVec.ofNat 64 ((s.regs.read 28#5).toNat - 8 * (n + 1)) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega
  rw [ef] at st1
  generalize hs1 : ({ s with regs := s.regs.write 28#5 (BitVec.ofNat 64 ((s.regs.read 28#5).toNat - 8 * (n + 1))), pc := s.pc + 4#64 } : Arm64.State) = s1 at st1
  have ok1 : okS L s1 := by rw [← hs1]; exact okS_of hok rfl rfl
  have r28 : s1.regs.read 28#5 = BitVec.ofNat 64 ((s.regs.read 28#5).toNat - 8 * (n + 1)) := by
    rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write]
  have r30 : s1.regs.read 30#5 = s.regs.read 30#5 := by rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write]
  have eA : (s1.regs.read 28#5 + 0#64).toNat = (s.regs.read 28#5).toNat - 8 * (n + 1) := by
    rw [BitVec.add_zero, r28]; simp; have := hr.2; simp only [base] at this; omega
  obtain ⟨hcw, hp, hm⟩ := write64_ok ok1 (by rw [eA]; have := hr.2; simp only [base] at this; omega)
    (fun i hi => by rw [eA]; exact hw i hi) (s1.regs.read 30#5)
  have st2 := exec_ok ok1 (by rw [← hs1]; show s.pc + 4#64 = _; rw [show s.pc = pc from hpc]) (by rw [e4]; omega)
    (instrAt_of (by rw [← hs1]) i2) dec_str30
  rw [ev_str 30#5 28#5 0#64 s1 rfl rfl hcw] at st2
  refine ⟨_, .step st1 (.step st2 (.refl _)), okS_pres ok1 (by rw [← hs1]) hp, ⟨fun x _ hx => ?_, by rw [← hs1]⟩, ?_, ?_,
    fun r => ?_, ?_⟩
  · have : x ≠ 28#5 := fun e => hx (.inl e)
    rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write, this]
  · show s1.pc + 4#64 = next pc (encC (.enterC n)).length
    rw [← hs1]; show s.pc + 4#64 + 4#64 = _; rw [show s.pc = pc from hpc, BitVec.add_assoc]; rfl
  · exact r28
  · show s1.regs.read (xr r) = s.regs.read (xr r)
    rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write, xr_ne28 r]
  · show memM (s1.mem.write64 _ _) = Mem.wr (memM s.mem) _ _
    rw [hm, eA, r30, show s1.mem = s.mem by rw [← hs1]]

theorem law_leaveC {L : Lay} {n : Nat} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 64} (hn : n ≤ 16)
    (h : (base L).At s pc (encC (.leaveC n))) (hr : (base L).inRAM (s.regs.read 28#5).toNat (8 * (n + 1)))
    (_ : (s.regs.read 28#5).toNat % 8 = 0) (hb : bytes ((base L).mem s) (s.regs.read 28#5).toNat 8 = (le8 w).map some) :
    (base L).runsTo s fun s' => (base L).ok s' ∧ keepCS s s' ∧ (base L).pcIs s' (next pc (encC (.leaveC n)).length) ∧
      s'.regs.read 30#5 = w ∧ s'.regs.read 28#5 = BitVec.ofNat 64 ((s.regs.read 28#5).toNat + 8 * (n + 1)) ∧
      (base L).Same s s' ∧ (base L).mem s' = (base L).mem s := by
  obtain ⟨hok, hpc, hal, i1, i2⟩ := at2 h
  have hco : pc.toNat + 4 * 2 ≤ 2 ^ 64 - 1 := h.codeOK.2.2
  have e4 : (pc + 4#64).toNat = pc.toNat + 4 := by rw [BitVec.toNat_add]; simp; omega
  obtain ⟨hcr, hv⟩ := read64_of (m := s.mem) (a := s.regs.read 28#5 + 0#64) (by rw [BitVec.add_zero]; exact hb)
  have st1 := exec_ok hok hpc hal i1 dec_ldr30
  rw [ev_ldr 30#5 28#5 0#64 s rfl rfl hcr, hv] at st1
  generalize hs1 : ({ s with regs := s.regs.write 30#5 w, pc := s.pc + 4#64 } : Arm64.State) = s1 at st1
  have ok1 : okS L s1 := by rw [← hs1]; exact okS_of hok rfl rfl
  have st2 := exec_ok ok1 (by rw [← hs1]; show s.pc + 4#64 = _; rw [show s.pc = pc from hpc]) (by rw [e4]; omega)
    (instrAt_of (by rw [← hs1]) i2) (dec_addfr ⟨n, by omega⟩)
  rw [ev_addi 28#5 28#5 _ (by omega) s1 rfl rfl] at st2
  have r28 : s1.regs.read 28#5 = s.regs.read 28#5 := by rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write]
  refine ⟨_, .step st1 (.step st2 (.refl _)), okS_of ok1 rfl rfl, ⟨fun x _ hx => ?_, by rw [← hs1]⟩, ?_, ?_, ?_,
    fun r => ?_, by rw [← hs1]; rfl⟩
  · have h28 : x ≠ 28#5 := fun e => hx (.inl e)
    have h30 : x ≠ 30#5 := fun e => hx (.inr e)
    rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write, h28, h30]
  · show s1.pc + 4#64 = next pc (encC (.leaveC n)).length
    rw [← hs1]; show s.pc + 4#64 + 4#64 = _; rw [show s.pc = pc from hpc, BitVec.add_assoc]; rfl
  · rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write]
  · rw [show ∀ (rf : Arm64.RegFile) (x : BitVec 64), (rf.write 28#5 x).read 28#5 = x from fun rf x => by
      simp [Arm64.RegFile.read, Arm64.RegFile.write], r28]
    apply BitVec.eq_of_toNat_eq; simp
  · show (s1.regs.write 28#5 _).read (xr r) = s.regs.read (xr r)
    rw [← hs1]; simp [Arm64.RegFile.read, Arm64.RegFile.write, xr_ne28 r, xr_ne30 r]

theorem law_stA {L : Lay} {m : Nat} {v : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (_ : v.val = 0) (h1 : 1 ≤ m)
    (hm : m ≤ 16) (h : (base L).At s pc (encC (.stA m v))) (h8 : 8 * m ≤ (s.regs.read 28#5).toNat)
    (hr : (base L).inRAM ((s.regs.read 28#5).toNat - 8 * m) 8) (_ : (s.regs.read 28#5).toNat % 8 = 0)
    (hw : ∀ i, i < 8 → (base L).writable s ((s.regs.read 28#5).toNat - 8 * m + i)) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (encC (.stA m v)).length) ∧ (base L).Same s s' ∧
      (base L).mem s' = ((base L).mem s).wr ((s.regs.read 28#5).toNat - 8 * m) (le8 ((base L).get s v)) := by
  have e : (s.regs.read 28#5 + BitVec.ofNat 64 (2 ^ 64 - 8 * m)).toNat = (s.regs.read 28#5).toNat - 8 * m := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have := str_run (val := s.regs.read (xr v)) h (dec_stur v ⟨m, by omega⟩ h1)
    (fun hc => ev_stur _ _ _ s (xr_ne31 v) rfl hc)
    (by rw [e]; have := hr.2; simp only [base] at this; omega) (fun i hi => by rw [e]; exact hw i hi)
  rw [e] at this; exact this

/-- **The call interface on DeepMind's AArch64 semantics.** -/
def apcC (L : Lay) : MachineC where
  toMachineF := apcF L
  encC := encC
  keepC := keepCS
  callOK d := -2 ^ 25 ≤ d ∧ d < 2 ^ 25
  lenCall := 1
  len_call _ := rfl
  keepC_of_keepF h := ⟨fun x hx he => h.1 x hx (fun e => he (.inl e)), h.2⟩
  keepC_trans h₁ h₂ := ⟨fun x hx he => (h₂.1 x hx he).trans (h₁.1 x hx he), h₂.2.trans h₁.2⟩
  keepF_of_keepC h hra := ⟨fun x hx h28 => if e : x = 30#5 then e ▸ hra else
    h.1 x hx (by rintro (a | a); exact h28 a; exact e a), h.2⟩
  retOK_al _ _ := trivial
  law_call := law_call
  law_enterC := law_enterC
  law_leaveC := law_leaveC
  law_stA := law_stA

end Proven.Apc

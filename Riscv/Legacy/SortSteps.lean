/- Step lemmas for every instruction word of `asm/sort.S` (generated from `asm/sort.dis`;
symbolic `pc`, register values and memory; each by `step_word`). -/
import Riscv.Steps.Step

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Proven.Sort

/-- `addi t0,zero,0` -/
theorem w00000293 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00000293#32) :
    ∃ s', Next s s' (pc + 4) 5 (0) s.mem := by step_word

/-- `bgeu t0,a1,8000005c` -/
theorem w00b2fe63_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00b2fe63#32) (hc : (getX s 11).toNat ≤ (getX s 5).toNat) :
    ∃ s', Next s s' (pc + 28) 0 0 s.mem := by step_word

/-- `bgeu t0,a1,8000005c` -/
theorem w00b2fe63_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00b2fe63#32) (hc : (getX s 5).toNat < (getX s 11).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `add t1,a0,t0` -/
theorem w00550333 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00550333#32) :
    ∃ s', Next s s' (pc + 4) 6 (getX s 10 + getX s 5) s.mem := by step_word

/-- `lbu t2,0(t1)` -/
theorem w00034383 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00034383#32)
    (ha : 0x80000000 ≤ (getX s 6).toNat ∧ (getX s 6).toNat < 0x100000000) {b : BitVec 8} (hb : s.mem[(getX s 6).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) 7 ((s.mem[(getX s 6).toNat]?.getD 0).setWidth 64) s.mem := by step_word

/-- `add t1,a3,t0` -/
theorem w00568333 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00568333#32) :
    ∃ s', Next s s' (pc + 4) 6 (getX s 13 + getX s 5) s.mem := by step_word

/-- `sb t2,0(t1)` -/
theorem w00730023 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00730023#32)
    (ha : 0x80000000 ≤ (getX s 6).toNat ∧ (getX s 6).toNat < 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert (getX s 6).toNat ((getX s 7).setWidth 8)) := by step_word

/-- `addi t0,t0,1` -/
theorem w00128293 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00128293#32) :
    ∃ s', Next s s' (pc + 4) 5 (getX s 5 + 1) s.mem := by step_word

/-- `jal zero,80000040` -/
theorem wfe9ff06f {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0xfe9ff06f#32) :
    ∃ s', Next s s' (pc - 24) 0 0 s.mem := by step_word

/-- `addi t3,a3,0` -/
theorem w00068e13 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00068e13#32) :
    ∃ s', Next s s' (pc + 4) 28 (getX s 13) s.mem := by step_word

/-- `addi t4,a2,0` -/
theorem w00060e93 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00060e93#32) :
    ∃ s', Next s s' (pc + 4) 29 (getX s 12) s.mem := by step_word

/-- `addi t5,zero,1` -/
theorem w00100f13 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00100f13#32) :
    ∃ s', Next s s' (pc + 4) 30 (1) s.mem := by step_word

/-- `bgeu t5,a1,80000100` -/
theorem w08bf7c63_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x08bf7c63#32) (hc : (getX s 11).toNat ≤ (getX s 30).toNat) :
    ∃ s', Next s s' (pc + 152) 0 0 s.mem := by step_word

/-- `bgeu t5,a1,80000100` -/
theorem w08bf7c63_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x08bf7c63#32) (hc : (getX s 30).toNat < (getX s 11).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `addi t6,zero,0` -/
theorem w00000f93 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00000f93#32) :
    ∃ s', Next s s' (pc + 4) 31 (0) s.mem := by step_word

/-- `bgeu t6,a1,800000ec` -/
theorem w06bffe63_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x06bffe63#32) (hc : (getX s 11).toNat ≤ (getX s 31).toNat) :
    ∃ s', Next s s' (pc + 124) 0 0 s.mem := by step_word

/-- `bgeu t6,a1,800000ec` -/
theorem w06bffe63_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x06bffe63#32) (hc : (getX s 31).toNat < (getX s 11).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `add a4,t6,t5` -/
theorem w01ef8733 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x01ef8733#32) :
    ∃ s', Next s s' (pc + 4) 14 (getX s 31 + getX s 30) s.mem := by step_word

/-- `bgeu a1,a4,80000080` -/
theorem w00e5f463_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00e5f463#32) (hc : (getX s 14).toNat ≤ (getX s 11).toNat) :
    ∃ s', Next s s' (pc + 8) 0 0 s.mem := by step_word

/-- `bgeu a1,a4,80000080` -/
theorem w00e5f463_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00e5f463#32) (hc : (getX s 11).toNat < (getX s 14).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `addi a4,a1,0` -/
theorem w00058713 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00058713#32) :
    ∃ s', Next s s' (pc + 4) 14 (getX s 11) s.mem := by step_word

/-- `add a5,a4,t5` -/
theorem w01e707b3 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x01e707b3#32) :
    ∃ s', Next s s' (pc + 4) 15 (getX s 14 + getX s 30) s.mem := by step_word

/-- `bgeu a1,a5,8000008c` -/
theorem w00f5f463_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00f5f463#32) (hc : (getX s 15).toNat ≤ (getX s 11).toNat) :
    ∃ s', Next s s' (pc + 8) 0 0 s.mem := by step_word

/-- `bgeu a1,a5,8000008c` -/
theorem w00f5f463_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00f5f463#32) (hc : (getX s 11).toNat < (getX s 15).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `addi a5,a1,0` -/
theorem w00058793 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00058793#32) :
    ∃ s', Next s s' (pc + 4) 15 (getX s 11) s.mem := by step_word

/-- `addi t0,t6,0` -/
theorem w000f8293 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x000f8293#32) :
    ∃ s', Next s s' (pc + 4) 5 (getX s 31) s.mem := by step_word

/-- `addi t1,a4,0` -/
theorem w00070313 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00070313#32) :
    ∃ s', Next s s' (pc + 4) 6 (getX s 14) s.mem := by step_word

/-- `addi t2,t6,0` -/
theorem w000f8393 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x000f8393#32) :
    ∃ s', Next s s' (pc + 4) 7 (getX s 31) s.mem := by step_word

/-- `bgeu t2,a5,800000e4` -/
theorem w04f3f663_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x04f3f663#32) (hc : (getX s 15).toNat ≤ (getX s 7).toNat) :
    ∃ s', Next s s' (pc + 76) 0 0 s.mem := by step_word

/-- `bgeu t2,a5,800000e4` -/
theorem w04f3f663_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x04f3f663#32) (hc : (getX s 7).toNat < (getX s 15).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `bgeu t0,a4,800000c8` -/
theorem w02e2f663_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x02e2f663#32) (hc : (getX s 14).toNat ≤ (getX s 5).toNat) :
    ∃ s', Next s s' (pc + 44) 0 0 s.mem := by step_word

/-- `bgeu t0,a4,800000c8` -/
theorem w02e2f663_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x02e2f663#32) (hc : (getX s 5).toNat < (getX s 14).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `bgeu t1,a5,800000b8` -/
theorem w00f37c63_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00f37c63#32) (hc : (getX s 15).toNat ≤ (getX s 6).toNat) :
    ∃ s', Next s s' (pc + 24) 0 0 s.mem := by step_word

/-- `bgeu t1,a5,800000b8` -/
theorem w00f37c63_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00f37c63#32) (hc : (getX s 6).toNat < (getX s 15).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `add a6,t3,t0` -/
theorem w005e0833 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x005e0833#32) :
    ∃ s', Next s s' (pc + 4) 16 (getX s 28 + getX s 5) s.mem := by step_word

/-- `lbu a6,0(a6)` -/
theorem w00084803 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00084803#32)
    (ha : 0x80000000 ≤ (getX s 16).toNat ∧ (getX s 16).toNat < 0x100000000) {b : BitVec 8} (hb : s.mem[(getX s 16).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) 16 ((s.mem[(getX s 16).toNat]?.getD 0).setWidth 64) s.mem := by step_word

/-- `add a7,t3,t1` -/
theorem w006e08b3 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x006e08b3#32) :
    ∃ s', Next s s' (pc + 4) 17 (getX s 28 + getX s 6) s.mem := by step_word

/-- `lbu a7,0(a7)` -/
theorem w0008c883 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0008c883#32)
    (ha : 0x80000000 ≤ (getX s 17).toNat ∧ (getX s 17).toNat < 0x100000000) {b : BitVec 8} (hb : s.mem[(getX s 17).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) 17 ((s.mem[(getX s 17).toNat]?.getD 0).setWidth 64) s.mem := by step_word

/-- `bltu a7,a6,800000c8` -/
theorem w0108ea63_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0108ea63#32) (hc : (getX s 17).toNat < (getX s 16).toNat) :
    ∃ s', Next s s' (pc + 20) 0 0 s.mem := by step_word

/-- `bltu a7,a6,800000c8` -/
theorem w0108ea63_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0108ea63#32) (hc : (getX s 16).toNat ≤ (getX s 17).toNat) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `jal zero,800000d4` -/
theorem w0100006f {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0100006f#32) :
    ∃ s', Next s s' (pc + 16) 0 0 s.mem := by step_word

/-- `add a6,t3,t1` -/
theorem w006e0833 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x006e0833#32) :
    ∃ s', Next s s' (pc + 4) 16 (getX s 28 + getX s 6) s.mem := by step_word

/-- `addi t1,t1,1` -/
theorem w00130313 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00130313#32) :
    ∃ s', Next s s' (pc + 4) 6 (getX s 6 + 1) s.mem := by step_word

/-- `add a7,t4,t2` -/
theorem w007e88b3 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x007e88b3#32) :
    ∃ s', Next s s' (pc + 4) 17 (getX s 29 + getX s 7) s.mem := by step_word

/-- `sb a6,0(a7)` -/
theorem w01088023 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x01088023#32)
    (ha : 0x80000000 ≤ (getX s 17).toNat ∧ (getX s 17).toNat < 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert (getX s 17).toNat ((getX s 16).setWidth 8)) := by step_word

/-- `addi t2,t2,1` -/
theorem w00138393 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00138393#32) :
    ∃ s', Next s s' (pc + 4) 7 (getX s 7 + 1) s.mem := by step_word

/-- `jal zero,80000098` -/
theorem wfb9ff06f {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0xfb9ff06f#32) :
    ∃ s', Next s s' (pc - 72) 0 0 s.mem := by step_word

/-- `addi t6,a5,0` -/
theorem w00078f93 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00078f93#32) :
    ∃ s', Next s s' (pc + 4) 31 (getX s 15) s.mem := by step_word

/-- `jal zero,80000070` -/
theorem wf89ff06f {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0xf89ff06f#32) :
    ∃ s', Next s s' (pc - 120) 0 0 s.mem := by step_word

/-- `addi a6,t3,0` -/
theorem w000e0813 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x000e0813#32) :
    ∃ s', Next s s' (pc + 4) 16 (getX s 28) s.mem := by step_word

/-- `addi t3,t4,0` -/
theorem w000e8e13 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x000e8e13#32) :
    ∃ s', Next s s' (pc + 4) 28 (getX s 29) s.mem := by step_word

/-- `addi t4,a6,0` -/
theorem w00080e93 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00080e93#32) :
    ∃ s', Next s s' (pc + 4) 29 (getX s 16) s.mem := by step_word

/-- `slli t5,t5,0x1` -/
theorem w001f1f13 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x001f1f13#32) :
    ∃ s', Next s s' (pc + 4) 30 (getX s 30 <<< 1) s.mem := by step_word

/-- `jal zero,80000068` -/
theorem wf6dff06f {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0xf6dff06f#32) :
    ∃ s', Next s s' (pc - 148) 0 0 s.mem := by step_word

/-- `beq t3,a3,80000124` -/
theorem w02de0263_taken {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x02de0263#32) (hc : getX s 28 = getX s 13) :
    ∃ s', Next s s' (pc + 36) 0 0 s.mem := by step_word

/-- `beq t3,a3,80000124` -/
theorem w02de0263_not {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x02de0263#32) (hc : getX s 28 ≠ getX s 13) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := by step_word

/-- `add t1,t3,t0` -/
theorem w005e0333 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x005e0333#32) :
    ∃ s', Next s s' (pc + 4) 6 (getX s 28 + getX s 5) s.mem := by step_word

/-- `jalr zero,0(ra)` -/
theorem w00008067 {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00008067#32) (he : (getX s 1).toNat % 2 = 0) :
    ∃ s', Next s s' (getX s 1) 0 0 s.mem := by step_word

end Proven.Sort

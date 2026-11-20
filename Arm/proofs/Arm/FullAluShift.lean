/- PROOF NOTES (draft, NOT yet compiled; statements fuzz-confirmed under qemu-aarch64, 1.4M+ cases, shift = xm mod 64).
Opcode masks: 0xFFE0FC00 with T = 0x9AC02000 / 0x9AC02400 / 0x9AC02800 (lslv/lsrv/asrv, sf=1; bits 15..10 = op2:00 / 01 / 10).
SEE after decode: lslv 57, lsrv 58, asrv 56. op2 fixed field is `slice w 10 2` = 0/1/2, sf = 1.
Plan per instruction: (1) `dec_*sym`: `sprune` the `__DecodeA64` chain then `__DecodeA64_DataProcReg` (as `dec_movsym`), `sfin`;
(2) `full_*`: rewrite the decode with `*_exec` (Arm/Exec.lean; fields turned back into `BitVec.ofNat 5 _` by `ofNat_toNat5`),
then `full_x` (BrFull); the not-ERET side condition `noteret` uses bit 30 (T bit 30 = 0 differs from 879088 bit 18 = 1).
Risks: sprune may leave undecided tests on bits 20..16 (Rm); if so add `sx_false` cases or widen via `sw_false`. Registers d n m < 31 only (xzr/sp not covered). -/
/- Full machine steps for the 64-bit variable shifts `lslv`/`lsrv`/`asrv xd, xn, xm` (shift amount = xm mod 64),
all registers symbolic (`d n m < 31`): decode prune, then the execute lemmas of `Arm/Exec.lean`, then `full_*`. -/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.all false

namespace ArmProof

theorem dec_lslvsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x9AC02000#32) :
    __DecodeA64 pc w s = decode_lslv_aarch64_instrs_integer_shift_variable (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 0#2
      (Sail.BitVec.slice w 16 5) 1#1 { s with regs := s.regs.insert .SEE (57 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem dec_lsrvsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x9AC02400#32) :
    __DecodeA64 pc w s = decode_lsrv_aarch64_instrs_integer_shift_variable (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 1#2
      (Sail.BitVec.slice w 16 5) 1#1 { s with regs := s.regs.insert .SEE (58 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem dec_asrvsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x9AC02800#32) :
    __DecodeA64 pc w s = decode_asrv_aarch64_instrs_integer_shift_variable (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 2#2
      (Sail.BitVec.slice w 16 5) 1#1 { s with regs := s.regs.insert .SEE (56 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`lslv xd, xn, xm`** (`d n m < 31`) -/
theorem full_lslv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat <<< ((a.x (Sail.BitVec.slice w 16 5).toNat).toNat % 64))) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_lslvsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    lslv_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`lsrv xd, xn, xm`** (`d n m < 31`) -/
theorem full_lsrv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02400#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat >>> ((a.x (Sail.BitVec.slice w 16 5).toNat).toNat % 64))) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_lsrvsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    lsrv_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`asrv xd, xn, xm`** (`d n m < 31`) -/
theorem full_asrv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02800#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat ((a.x (Sail.BitVec.slice w 5 5).toNat).sshiftRight ((a.x (Sail.BitVec.slice w 16 5).toNat).toNat % 64))) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_asrvsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    asrv_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

end

#print axioms full_lslv
#print axioms full_lsrv
#print axioms full_asrv
#print axioms dec_lslvsym
#print axioms dec_lsrvsym
#print axioms dec_asrvsym

end ArmProof

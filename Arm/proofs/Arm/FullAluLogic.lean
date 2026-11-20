/- Full machine steps (`stepModel`, under `ArmFull`) for the 64-bit shifted-register logical ops with shift 0:
`and`, `orr`, `eor` `xd, xn, xm`, all registers symbolic (`d n m < 31`).

PROOF NOTES (status: draft, not yet compiled; statements fuzz-confirmed against qemu-aarch64, 20000 cases each incl.
aliasing, QEMU-ARM commit fb59ba1).
* Decode: `dec_*rsym` = `sprune` on `__DecodeA64` then `__DecodeA64_DataProcReg`, `sfin`; mirrors `dec_movsym`
  (SymDec.lean) with the mask widened to `0xFFE0FC00` (sf, opc, N, shift, imm6 fixed; Rm, Rn, Rd free). SEE values 48/55/53
  are those of `dec_and_0`/`dec_orr_0`/`dec_eor_0` in Words.lean.
* Execute: `and_exec`/`orr_exec`/`eor_exec` (Exec.lean), rewritten with `ofNat_toNat5` as in `full_mov`.
* Full step: `full_x` (BrFull.lean) with `noteret` at bit 26 (K bit set, T bit 0 differs from 879088 bit 14).
* Risk: the `rw [← ofNat_toNat5 ..]` may rewrite other occurrences of slice terms; if so use `simp only` or `have`.
-/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

theorem dec_andrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x8A000000#32) :
    __DecodeA64 pc w s = decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (Sail.BitVec.slice w 0 5)
      (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#1 0#2 0#2 1#1
      { s with regs := s.regs.insert .SEE (48 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`and xd, xn, xm`** (`d n m < 31`) -/
theorem full_andr (hK : w &&& 0xFFE0FC00#32 = 0x8A000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat &&& a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_andrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    and_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

end

theorem dec_orrrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0xAA000000#32) :
    __DecodeA64 pc w s = decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (Sail.BitVec.slice w 0 5)
      (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#1 0#2 1#2 1#1
      { s with regs := s.regs.insert .SEE (55 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`orr xd, xn, xm`** (`d n m < 31`) -/
theorem full_orrr (hK : w &&& 0xFFE0FC00#32 = 0xAA000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat ||| a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_orrrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    orr_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

end

theorem dec_eorrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0xCA000000#32) :
    __DecodeA64 pc w s = decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (Sail.BitVec.slice w 0 5)
      (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#1 0#2 2#2 1#1
      { s with regs := s.regs.insert .SEE (53 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`eor xd, xn, xm`** (`d n m < 31`) -/
theorem full_eorr (hK : w &&& 0xFFE0FC00#32 = 0xCA000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat ^^^ a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_eorrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    eor_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

end

end ArmProof

#print axioms ArmProof.dec_andrsym
#print axioms ArmProof.dec_orrrsym
#print axioms ArmProof.dec_eorrsym
#print axioms ArmProof.full_andr
#print axioms ArmProof.full_orrr
#print axioms ArmProof.full_eorr

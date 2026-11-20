/- PROOF NOTES (DRAFT: statement fuzz-confirmed under qemu-aarch64, 20000 cases each for add/sub incl. aliasing;
   proof not yet checked against the built model).
   Decode path: `__DecodeA64` -> `__DecodeA64_DataProcReg` -> `decode_{add,sub}_addsub_shift_..._shiftedreg`,
   pruned with `sprune`/`sfin` from `w &&& 0xFFE0FC00 = 0x8B000000` (add) / `0xCB000000` (sub): sf=1, S=0, shift=00,
   bit21=0, imm6=0 fixed; Rd/Rn/Rm stay symbolic slices. SEE = 14 (add) / 16 (sub), as in `dec_add_0`/`dec_sub_0`.
   Execute: existing `add_exec`/`sub_exec` (Arm/Exec.lean) for `d n m < 31`: only X[d] := a+b / a-b.
   Full step: mirrors `full_mov` (Arm/BrFull.lean): rewrite the slices to `BitVec.ofNat 5 _` via `ofNat_toNat5`,
   rewrite with the exec lemma, then `full_x`; `noteret` at a bit where the word differs from the ret word
   (bit 30 for add, bit 28 for sub). d, n, m = 31 (xzr/sp) are excluded by the `< 31` hypotheses. -/
/- Full machine steps with all registers symbolic for 64-bit `add xd, xn, xm` and `sub xd, xn, xm`
(shifted-register form, shift 0, no flags). -/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

theorem dec_addrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x8B000000#32) :
    __DecodeA64 pc w s = decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
      (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#2 0#1 0#1 1#1
      { s with regs := s.regs.insert .SEE (14 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem dec_subrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0xCB000000#32) :
    __DecodeA64 pc w s = decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
      (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#2 0#1 1#1 1#1
      { s with regs := s.regs.insert .SEE (16 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`add xd, xn, xm`** (`d n m < 31`) -/
theorem full_addr (hK : w &&& 0xFFE0FC00#32 = 0x8B000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat + a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_addrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    add_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`sub xd, xn, xm`** (`d n m < 31`) -/
theorem full_subr (hK : w &&& 0xFFE0FC00#32 = 0xCB000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat - a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_subrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    sub_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 28 (by decide) (by decide) (by decide)) hd31 hd

end

end ArmProof

#print axioms ArmProof.dec_addrsym
#print axioms ArmProof.dec_subrsym
#print axioms ArmProof.full_addr
#print axioms ArmProof.full_subr

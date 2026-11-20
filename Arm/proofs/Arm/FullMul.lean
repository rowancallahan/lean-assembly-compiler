/- PROOF NOTES (AL5, DRAFT — NOT YET COMPILED against the model; listed in check.sh on this draft branch only)
Statement status: fuzz-confirmed under qemu-aarch64 (QF-MUL: 1,390,272 cases, 0 mismatches; QEMU-ARM: 5000/kind,
full x0..x30 + NZCV compared). madd: x d := x a + x n * x m (mod 2^64); mul (Ra = 31 = xzr): x d := x n * x m.
Decode: Sail clause `__DecodeA64_DataProcReg` [sf=1, op54=00, 11011, op31=000, o0=0] with SEE < 690, SEE := 690;
  mask 0xFFE08000 = 0x9B000000 (mul: 0xFFE0FC00 = 0x9B007C00). Proof = `sprune` through `__DecodeA64` and
  `__DecodeA64_DataProcReg`, then `sfin` (as `dec_movsym`). `dec_mulsym` reuses `dec_maddsym` + `sl_eq` for Ra.
Execute: `result = UInt(a) + UInt(n) * UInt(m)` as Int, then `result[63..0]`. Assumed generated as
  `integer_subrange` (as in `AddWithCarry`); `sub_madd` rewrites it to `z + x * y`. If the generated form differs
  (e.g. `get_slice_int` direct or `BitVec.ofInt`), adapt `sub_madd` only. Xzr read (Ra = 31) via `X_read` in exec_simp,
  as in `mov_exec` (Rn = 31).
Full step: `full_x` (BrFull) with `noteret hK 30` (bit 30: T = 0, ERET = 1). -/
/- 64-bit multiply-add `madd xd, xn, xm, xa` and `mul xd, xn, xm` (= `madd` with `xa = xzr`), all registers
symbolic: decode (data-processing 3-source, symbolic fields), execute, and the full `stepModel` step. -/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

/-! ## decode: `__DecodeA64` → `__DecodeA64_DataProcReg` → `decode_madd_*` (SEE := 690) -/

theorem dec_maddsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE08000#32 = 0x9B000000#32) :
    __DecodeA64 pc w s = decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.BitVec.slice w 0 5)
      (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 5) 0#1 (Sail.BitVec.slice w 16 5) 1#1
      { s with regs := s.regs.insert .SEE (690 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem mul_K {w : BitVec 32} (hK : w &&& 0xFFE0FC00#32 = 0x9B007C00#32) : w &&& 0xFFE08000#32 = 0x9B000000#32 := by
  have : w &&& 0xFFE08000#32 = (w &&& 0xFFE0FC00#32) &&& 0xFFE08000#32 := by rw [BitVec.and_assoc]; rfl
  rw [this, hK]; rfl

theorem mul_ra {w : BitVec 32} (hK : w &&& 0xFFE0FC00#32 = 0x9B007C00#32) : Sail.BitVec.slice w 10 5 = 31#5 := by
  rw [sl_eq hK (by decide)]; rfl

theorem dec_mulsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x9B007C00#32) :
    __DecodeA64 pc w s = decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.BitVec.slice w 0 5)
      (Sail.BitVec.slice w 5 5) 31#5 0#1 (Sail.BitVec.slice w 16 5) 1#1
      { s with regs := s.regs.insert .SEE (690 : Int) } := by
  rw [dec_maddsym s pc see hs h (mul_K hK), mul_ra hK]

/-! ## execute: low 64 bits of `xa + xn * xm` -/

theorem sub_madd (x y z : BitVec 64) :
    integer_subrange ((z.toNat : Int) + (x.toNat : Int) * (y.toNat : Int)) 63 0 = z + x * y := by
  apply BitVec.eq_of_toNat_eq
  simp [integer_subrange, Sail.BitVec.length, get_slice_int, BitVec.toNat_add, BitVec.toNat_mul]
  norm_cast
  simp [Nat.add_mod, Nat.mul_mod]

section
variable {s : St} {d n m r : Nat} {x y z : BitVec 64}

theorem madd_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (hr : r < 31) (hx : xget s.regs n = some x)
    (hy : xget s.regs m = some y) (hz : xget s.regs r = some z) :
    decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (BitVec.ofNat 5 d) (BitVec.ofNat 5 n)
      (BitVec.ofNat 5 r) 0#1 (BitVec.ofNat 5 m) 1#1 s = .ok () { s with regs := xset s.regs d (z + x * y) } := by
  idx d; idx n; idx m; idx r
  dsimp only [decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub]; dsimp
  have hsm := sub_madd x y z
  simp only [execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub]
  exec_simp

theorem mul_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (hx : xget s.regs n = some x)
    (hy : xget s.regs m = some y) :
    decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (BitVec.ofNat 5 d) (BitVec.ofNat 5 n)
      31#5 0#1 (BitVec.ofNat 5 m) 1#1 s = .ok () { s with regs := xset s.regs d (x * y) } := by
  idx d; idx n; idx m
  dsimp only [decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub]; dsimp
  have := sub_madd x y 0
  rw [BitVec.zero_add] at this
  simp only [execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub]
  exec_simp
end

/-! ## full steps -/

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`madd xd, xn, xm, xa`** (`d n m a < 31`): `x d := x a + x n * x m` (mod 2^64) -/
theorem full_madd (hK : w &&& 0xFFE08000#32 = 0x9B000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31)
    (ha31 : (Sail.BitVec.slice w 10 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 10 5).toNat +
        a.x (Sail.BitVec.slice w 5 5).toNat * a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_maddsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 10 5), ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    madd_exec hd31 hn31 hm31 ha31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31) (s0_xk ha w _ ha31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`mul xd, xn, xm`** (`madd xd, xn, xm, xzr`; `d n m < 31`): `x d := x n * x m` (mod 2^64) -/
theorem full_mul (hK : w &&& 0xFFE0FC00#32 = 0x9B007C00#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat * a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_mulsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    mul_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

end

end ArmProof

#print axioms ArmProof.dec_maddsym
#print axioms ArmProof.dec_mulsym
#print axioms ArmProof.madd_exec
#print axioms ArmProof.mul_exec
#print axioms ArmProof.full_madd
#print axioms ArmProof.full_mul

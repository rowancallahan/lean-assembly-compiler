/- AL6: `br xn` / `blr xn` (indirect branch, any `n < 31`) and `ldur xt, [xn, #simm9]` (8-byte unscaled load)
with symbolic fields: decode prune, execute, full step.

Model fact: `br` sets `BTypeNext := 0b01`, `blr` sets `BTypeNext := 0b10` (`execute_aarch64_instrs_branch_unconditional_register`,
`InGuardedPage` is false), and with BTI off nothing resets `BTypeNext` (only `ret` writes `0b00`), so after either
the state is NOT in `ArmFull` (which pins `BTypeNext = 0`). The full steps for `br`/`blr` therefore use
`ArmFullB s n` (Full.lean; `ArmFull s := ArmFullB s 0`).

STATUS: draft, NOT yet checked against the built model (sent to runner ARM-R1). Statements fuzz-confirmed under
qemu-aarch64 (br, blr incl. n = 30, ldur aligned/unaligned; BTYPE not observable there).
Proof notes:
- decode: `dec_brsym` (SEE 92, mask 0xFFFFFC1F), `dec_blrsym` (SEE 90), `dec_ldursym` (SEE 680, mask 0xFFE00C00),
  same `sprune`/`sfin` recipe as SymDec (no full decoder unfold, no `Reduce__1`).
- execute: `br_exec`/`blr_exec` follow `ret_exec`/`bl_exec` (`retcfg_of`, `ret_simp`; `InGuardedPage = false`
  kills the `n == 16 | n == 17` branch); `ldur_exec` mirrors `stur_exec` with `memreadG8` (8-aligned assumed:
  the model checks alignment, qemu-user does not fault).
- full step: `full_gen` (BrFull), which takes `ArmFullB s n0` to `ArmFullB s' n1`;
  `full_ldur` reuses `full_ld` from Mem. `noteret` bit 23 (br/blr), 29 (ldur). -/
import Arm.Mem
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false
set_option pp.deepTerms false
set_option pp.maxSteps 3000

namespace ArmProof

/-! ## decode prune -/

theorem dec_brsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFFFFC1F#32 = 0xD61F0000#32) :
    __DecodeA64 pc w s = decode_br_aarch64_instrs_branch_unconditional_register 0#5 (Sail.BitVec.slice w 5 5) 0#1 0#1 0#2 0#1
      { s with regs := s.regs.insert .SEE (92 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl

theorem dec_ldursym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE00C00#32 = 0xF8400000#32) :
    __DecodeA64 pc w s = decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 12 9) 1#2 3#2
      { s with regs := s.regs.insert .SEE (680 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

/-! ## execute -/

/-- the registers `br` (`b = 1`, INDIR) / `blr` (`b = 2`, INDCALL) write after `X[30]`: BTypeNext, Branchtypetaken, PC -/
def indRegs (m : Regs) (btn : BitVec 2) (bty : BranchType) (t : BitVec 64) : Regs :=
  (((m.insert .BTypeNext btn).insert .Branchtypetaken bty).insert ._PC t).insert .__BranchTaken true

section
variable {s : St} (hc : Pins s.regs)
include hc

theorem br_exec {n : Nat} (hn : n < 31) {t : BitVec 64} (ht : xget s.regs n = some t)
    (hg : s.regs.get? .InGuardedPage = some false) :
    decode_br_aarch64_instrs_branch_unconditional_register 0#5 (BitVec.ofNat 5 n) 0#1 0#1 0#2 0#1 s =
      .ok () { s with regs := indRegs s.regs 1#2 .BranchType_INDIR t } := by
  have hr := retcfg_of hc
  obtain ⟨p, hp, hrw, hel⟩ := hr.p
  obtain ⟨fi, hfi, hgcs, hbrbe, hspe, hpac, hvhe, ha64⟩ := hr.fi
  obtain ⟨scr, hscr⟩ := hr.scr
  idx n
  simp only [decode_br_aarch64_instrs_branch_unconditional_register, indRegs]
  rcases hel with ⟨hel3, tcr, htcr, htbi⟩ | ⟨hel1, -⟩
  · ret_simp
  · obtain ⟨q, hq, h3, -⟩ := hc.ps; rw [hp] at hq; cases hq; rw [hel1] at h3; cases h3

theorem ldur_exec {t n : Nat} (ht : t < 31) (hn : n < 31) (imm : BitVec 9) {a : BitVec 64} (ha : xget s.regs n = some a)
    {v : BitVec 64} (hlt : VaOK (a + imm.signExtend 64).toNat) (hal : (a + imm.signExtend 64).toNat % 8 = 0)
    (hv : MemD s.mem (a + imm.signExtend 64).toNat v) :
    decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) imm 1#2 3#2 s =
      .ok () { s with regs := xset (s.regs.insert .InGuardedPage false) t v } := by
  idx t; idx n
  have hg := gpr_ok hc .MemOp_LOAD (.inl rfl)
  have hm := memreadG8 hc (a + imm.signExtend 64) v hlt hal hv
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (xset (s.regs.insert .InGuardedPage false) t v).get? .SPESampleInFlight = some false := by
    rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide))]; simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal, sign_extend, Sail.BitVec.signExtend]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hm
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_LOAD != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz8, sz8', w64, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz8', hm, BitVec.setWidth_eq]
  esimp

end

/-! ## full step with a general `BTypeNext` -/

theorem s0B_pins {s : St} {n : BitVec 2} (hf : ArmFullB s n) (w : BitVec 32) (k : Int) : Pins ((s0of s w).regs.insert .SEE k) := by
  refine (pins_insert _ rfl).2 ?_
  show Pins (preRegs (s.regs.insert .SEE (-1 : Int)) w)
  unfold preRegs; simp [pins_insert, NotPinned, hf.pins]

theorem s0_igp' (s : St) (w : BitVec 32) (k : Int) : ((s0of s w).regs.insert .SEE k).get? .InGuardedPage = some false := by
  simp [s0of, preRegs, Std.ExtDHashMap.get?_insert]

/-! ## full steps -/

section
variable {w : BitVec 32} {s : St} {a : AState} {n0 : BitVec 2} (hf : ArmFullB s n0) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`br xn`** (`n < 31`) as a full step: PC := xn; `BTypeNext` (and PSTATE.BTYPE) become `0b01` -/
theorem full_brB (hK : w &&& 0xFFFFFC1F#32 = 0xD61F0000#32) (hn : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' 1#2 ∧
      s'.regs.get? ._PC = some (a.x (Sail.BitVec.slice w 5 5).toNat) ∧ s'.mem = s.mem := by
  have hd := dec_brsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  let t := a.x (Sail.BitVec.slice w 5 5).toNat
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    br_exec (s0B_pins hf w _) hn (s0_xk ha w _ hn) (s0_igp' s w _)] at hd
  have hx : ∀ r : Register, r ≠ .SEE → r ≠ ._PC → r ≠ .__BranchTaken → r ≠ .Branchtypetaken → r ≠ .BTypeNext →
      (indRegs ((s0of s w).regs.insert .SEE (92 : Int)) 1#2 .BranchType_INDIR t).get? r = (s0of s w).regs.get? r :=
    fun r h1 h2 h3 h4 h5 => by
      simp [indRegs, Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm (noteret hK 23 (by decide) (by decide) (by decide)) hd
    (bt := true) (pc1 := t) (b := .BranchType_INDIR) (n1 := 1#2)
    (fun r _ _ h3 h4 h5 h6 h7 => hx r h3 h4 h5 h6 h7)
    (fun p hp => ⟨p, (hx _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((s0_get _ _ _ (by decide) (by decide)).trans hp), pkeep_refl p⟩)
    (by simp [indRegs, Std.ExtDHashMap.get?_insert]) (by simp [indRegs, Std.ExtDHashMap.get?_insert, t])
    (by simp [indRegs, Std.ExtDHashMap.get?_insert]) (by decide)
    (by simp [indRegs, Std.ExtDHashMap.get?_insert])
    (by
      have := abs_ins (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) (92 : Int)) .BTypeNext (by decide) (by decide) 1#2
      have := abs_ins this .Branchtypetaken (by decide) (by decide) .BranchType_INDIR
      exact abs_ins (abs_ins this ._PC (by decide) (by decide) t) .__BranchTaken (by decide) (by decide) true)
  exact ⟨s', h1, h2, h3, h4, h5⟩

end

section
variable {w : BitVec 32} {s : St} {a : AState} (hf : ArmFull s) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`br xn`** from `ArmFull` (ends in `ArmFullB _ 1`, not `ArmFull`) -/
theorem full_br (hK : w &&& 0xFFFFFC1F#32 = 0xD61F0000#32) (hn : (Sail.BitVec.slice w 5 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' 1#2 ∧
      s'.regs.get? ._PC = some (a.x (Sail.BitVec.slice w 5 5).toNat) ∧ s'.mem = s.mem :=
  full_brB hf ha hpc hlt hal hm hK hn

/-- **`ldur xt, [xn, #simm9]`** (8-aligned address below `2^29`) -/
theorem full_ldur (hK : w &&& 0xFFE00C00#32 = 0xF8400000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31) {v : BitVec 64}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat)
    (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat % 8 = 0)
    (hv : MemD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat v) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat v) ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldursym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ldur_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (680 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) hA hA8 hv] at hd
  exact full_ld hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) ht hd

end

end ArmProof

#print axioms ArmProof.dec_brsym
#print axioms ArmProof.dec_ldursym
#print axioms ArmProof.br_exec
#print axioms ArmProof.ldur_exec
#print axioms ArmProof.full_brB
#print axioms ArmProof.full_br
#print axioms ArmProof.full_ldur

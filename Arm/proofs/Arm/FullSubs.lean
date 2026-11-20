/- `subs xd, xn, xm` (64-bit shifted register, shift 0, `d n m < 31`) as one full step: `X[d] := x n - x m` and
NZCV := the sub flags (`AState.setSub`). rv2arm emits it as `subs x16, xn, xm` before a `b.cond` (`A64Sem.cmpbr`);
`FullCmp.full_cmp` is the `d = 31` (xzr, `cmp`) case and does not cover it.
Proof notes:
* decode: `dec_subsrsym` = `dec_cmpsym` with the Rd field symbolic (mask `0xFFE0FC00`), same SEE 17, same
  `sprune`/`sfin` recipe.
* execute: `subs_exec` = `cmp_exec` (Exec.lean) plus the `X[d]` write; the model writes PSTATE before `X[d]`.
* full step: `full_xpst` = `full_x` (BrFull) with the PSTATE write of `full_pst` (FullCmp): `full_gen` with
  `PKeep` (only NZCV changes), then `Abs.xset` after `abs_pst`. -/
import Arm.FullCmp
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

theorem dec_subsrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0xEB000000#32) :
    __DecodeA64 pc w s = decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
      (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#2 1#1 1#1 1#1
      { s with regs := s.regs.insert .SEE (17 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem subs_exec {s : St} {d n m : Nat} {a b : BitVec 64} (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) {p : ProcState} (hp : s.regs.get? .PSTATE = some p) :
    decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#6
      (BitVec.ofNat 5 m) 0#2 1#1 1#1 1#1 s =
      .ok () { s with regs := xset (s.regs.insert .PSTATE (setFlags p (AddWithCarry a (~~~b) 1#1).2)) d (a - b) } := by
  idx d; idx n; idx m
  dsimp only [decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg]; dsimp
  exec_simp

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
  (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20)
include hf ha hpc hlt hal hm heret

/-- full step for a decode+execute that writes SEE, PSTATE.NZCV and one `X` register -/
theorem full_xpst {k : Int} {d : Nat} (hd : d < 31) {v : BitVec 64} {q : ProcState} {a' : AState}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok ()
      { s0of s w with regs := xset (((s0of s w).regs.insert .SEE k).insert .PSTATE q) d v })
    (hq : ∀ p, s.regs.get? .PSTATE = some p → PKeep p q) (hx : a'.x = a.x)
    (hN : q.N = .ofBool a'.n) (hZ : q.Z = .ofBool a'.z) (hC : q.C = .ofBool a'.c) (hV : q.V = .ofBool a'.v) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a'.setX d v) ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx' : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .SEE → r ≠ .PSTATE →
      (xset (((s0of s w).regs.insert .SEE k).insert .PSTATE q) d v).get? r = (s0of s w).regs.get? r :=
    fun r h1 h2 h3 => by rw [xset_get_ne _ _ _ _ h1]; simp [Std.ExtDHashMap.get?_insert, Ne.symm h2, Ne.symm h3]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r h1 h2 h3 _ _ _ _ => hx' r h1 h3 h2)
    (fun p hp => ⟨q, by rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide))]; simp [Std.ExtDHashMap.get?_insert], hq p hp⟩)
    (by rw [hx' _ (xreg_ne' (by decide)) (by decide) (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx' _ (xreg_ne' (by decide)) (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx' _ (xreg_ne' (by decide)) (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx' _ (xreg_ne' (by decide)) (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (Abs.xset (abs_pst (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) hx q hN hZ hC hV) hd v)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩
end

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`subs xd, xn, xm`** (`d n m < 31`): `x d := x n - x m`, NZCV := sub flags -/
theorem full_subsr (hK : w &&& 0xFFE0FC00#32 = 0xEB000000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' ((a.setSub (a.x (Sail.BitVec.slice w 5 5).toNat) (a.x (Sail.BitVec.slice w 16 5).toNat)).setX
        (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat - a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨p, hp, hN, hZ, hC, hV⟩ := ha.p
  have hd := dec_subsrsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have hp0 : ((s0of s w).regs.insert .SEE (17 : Int)).get? .PSTATE = some p := by
    simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hp
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    subs_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31) hp0, sub_flags] at hd
  exact full_xpst hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) hd31 hd
    (fun p' hp' => by rw [hp] at hp'; cases hp'; rfl) rfl rfl rfl rfl rfl

end

end ArmProof

#print axioms ArmProof.full_subsr

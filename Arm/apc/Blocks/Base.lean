/- Shared definitions for the per-form step lemmas on DeepMind's `Arm64.Step` (Blocks/NOTES.md).
Every form lemma has the shape of the Sail `full_*` lemmas of `Arm/proofs`: premise = the opcode mask
`w &&& K = C` and `< 31` on the register fields (as `w.extractLsb'` slices, = Sail's `Sail.BitVec.slice w`);
conclusion = one step to `t'` with `abs t'` = the small-machine effect on `abs t`, and `Post` (running, PC, memory, sp). -/
import Apc.Agree
import Apc.Sym
namespace Proven.Apc.Blocks
open Proven.Arm

/-- the word `w` is fetchable at the PC of `t` (DeepMind side of `BridgeBr.WordAt`) -/
structure At (t : Arm64.State) (w : BitVec 32) : Prop where
  run : t.status = .Running
  al : t.pc.toNat % 4 = 0
  exec : t.mem.canExec t.pc 4 = true
  rd : t.mem.read32 t.pc = w

/-- the frame every form lemma states: running, PC, memory, sp -/
structure Post (t t' : Arm64.State) (pc' : BitVec 64) (m : Arm64.Memory) : Prop where
  run : t'.status = .Running
  pc : t'.pc = pc'
  mem : t'.mem = m
  sp : t'.sp = t.sp

theorem step_of {w : BitVec 32} {i : Arm64.Instr} {t : Arm64.State} (hd : Arm64.decode w = some i) (h : At t w) :
    Arm64.Step Pg t (Pg.evalInst i t) := by
  refine .exec h.run ?_
  have he : Pg.externAt? t.pc = none := rfl
  unfold Arm64.Program.fetchMem; rw [he]; simp [h.al, h.exec, h.rd, hd]

theorem ne31 {r : BitVec 5} (h : r.toNat < 31) : (r == 31#5) = false := by
  apply Bool.eq_false_iff.mpr; intro e; rw [beq_iff_eq] at e; subst e; simp at h

theorem fromSP {d : BitVec 5} (hd : (d.toNat < 31)) : Arm64.Reg.fromSPBits d = .gpr d := by
  simp [Arm64.Reg.fromSPBits, ne31 hd]
theorem fromZR' {d : BitVec 5} (hd : (d.toNat < 31)) : Arm64.Reg.fromZRBits d = .gpr d := fromZR (ne31 hd)

theorem abs_adv (t : Arm64.State) : abs t.advancePC = abs t := rfl
theorem abs_setPC (t : Arm64.State) (x : BitVec 64) : abs (t.setPC x) = abs t := rfl
theorem abs_wr (t : Arm64.State) {d : BitVec 5} (hd : d.toNat < 31) (v : BitVec 64) :
    abs (t.writeReg64 (.gpr d) v) = (abs t).setX d.toNat v := by
  simp only [abs, Arm64.State.writeReg64, ne31 hd, AState.setX, show d.toNat ≠ 31 by omega, ite_false]
  congr 1; funext i
  by_cases hi : i < 31
  · by_cases e : i = d.toNat
    · subst e; simp [Arm64.RegFile.write, Arm64.RegFile.read, hi]
    · have : BitVec.ofNat 5 i ≠ d := fun h => e (by rw [← h]; simp; omega)
      simp [Arm64.RegFile.write, Arm64.RegFile.read, hi, e, this]
  · simp [hi]; omega
theorem abs_x (t : Arm64.State) {d : BitVec 5} (hd : d.toNat < 31) : (abs t).x d.toNat = t.regs.read d := by
  simp [abs, hd]
theorem rd_gpr (t : Arm64.State) {d : BitVec 5} (hd : d.toNat < 31) : t.readReg64 (.gpr d) = (abs t).x d.toNat := by
  simp [Arm64.State.readReg64, ne31 hd, abs_x t hd]

end Proven.Apc.Blocks

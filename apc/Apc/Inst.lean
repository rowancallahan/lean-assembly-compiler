/- PROTOTYPE: our machine interface (`Compiler/Iface.lean`) on the AlphaProof-Code AArch64 semantics
(google-deepmind/code-verification b0f729a, `Arm64.Step`).  Three of the nine laws: mov, bin add, ret. -/
import Arm64
import Compiler.Iface
namespace Proven.Apc
open Proven Proven.Mach

/-- hook-free program, every `svc` traps -/
def P : Arm64.Program := Arm64.Program.ofSvc Arm64.noSyscalls

/-- abstract register -> x register number (as `Arm/CompilerArm.lean`: temporaries x9..x15, x4..x7; variables x0..x3) -/
def xn (r : Mach.Reg) : Nat :=
  match r.val with
  | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 12 | 4 => 13 | 5 => 14 | 6 => 15 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7
  | 11 => 0 | 12 => 1 | 13 => 2 | _ => 3
def xr (r : Mach.Reg) : BitVec 5 := BitVec.ofNat 5 (xn r)

def rrr (base rd rn rm : Nat) : BitVec 32 := BitVec.ofNat 32 (base ||| rm <<< 16 ||| rn <<< 5 ||| rd)
def encMov (d a : Mach.Reg) : BitVec 32 := rrr 0xAA000000 (xn d) 31 (xn a)       -- orr xd, xzr, xa
def encAdd (d a b : Mach.Reg) : BitVec 32 := rrr 0x8B000000 (xn d) (xn a) (xn b)  -- add xd, xa, xb
def encRet : BitVec 32 := 0xD65F03C0#32

def runsTo (s : Arm64.State) (Q : Arm64.State → Prop) : Prop := ∃ s', Arm64.Steps P s s' ∧ Q s'
def get (s : Arm64.State) (r : Mach.Reg) : BitVec 64 := s.regs.read (xr r)
def instrAt (s : Arm64.State) (pc : BitVec 64) (w : BitVec 32) : Prop :=
  s.mem.canExec pc 4 = true ∧ s.mem.read32 pc = w
def ok (s : Arm64.State) : Prop := s.status = .Running
/-- frame: x30, sp, flags are NOT in it for `bin` in general; here x30 and sp -/
def keep (s s' : Arm64.State) : Prop := s'.regs.read 30#5 = s.regs.read 30#5 ∧ s'.sp = s.sp

theorem steps_one {s s' : Arm64.State} (h : Arm64.Step P s s') : Arm64.Steps P s s' := .step h (.refl _)

/-- one fetched instruction is one step -/
theorem step_of {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} {i : Arm64.Instr}
    (hok : ok s) (hpc : s.pc = pc) (hal : pc.toNat % 4 = 0) (hi : instrAt s pc w) (hd : Arm64.decode w = some i) :
    Arm64.Step P s (P.evalInst i s) := by
  refine .exec hok ?_
  have he : P.externAt? s.pc = none := rfl
  unfold Arm64.Program.fetchMem
  rw [he, hpc]
  simp [hal, hi.1, hi.2, hd]

theorem dec_mov : ∀ d a : Mach.Reg, Arm64.decode (encMov d a) =
    some (.logicalShift .W64 .ORR (.gpr (xr d)) .xzr (.gpr (xr a)) .LSL 0) := by decide
/-- the shape `law_bin` needs: `a = d`, `b = d + 1`, `d < 10` -/
def sucR (d : Fin 10) : Mach.Reg := ⟨d.val + 1, by omega⟩
def toR (d : Fin 10) : Mach.Reg := ⟨d.val, by omega⟩
theorem dec_add : ∀ d : Fin 10, Arm64.decode (encAdd (toR d) (toR d) (sucR d)) =
    some (.addSubShift .W64 .ADD (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_ret : Arm64.decode encRet = some (.ret (.gpr 30#5)) := by decide

/-- distinct abstract registers are distinct x registers, none is x30 or x31 -/
theorem xr_inj : ∀ a b : Mach.Reg, xr a = xr b → a = b := by decide
theorem xr_ne30 : ∀ a : Mach.Reg, xr a ≠ 30#5 := by decide
theorem xr_ne31 : ∀ a : Mach.Reg, (xr a == 31#5) = false := by decide

theorem orr_val (v : BitVec 64) (ps : Arm64.PState) :
    Arm64.evalLogical .W64 .ORR 0#64 (Arm64.shiftVal .W64 v .LSL 0) ps = (v, none) := by
  simp [Arm64.evalLogical, Arm64.shiftVal, Arm64.shift64]
theorem add_val (x y : BitVec 64) :
    Arm64.evalAddSub .W64 .ADD x (Arm64.shiftVal .W64 y .LSL 0) none = (x + y, none) := by
  simp [Arm64.evalAddSub, Arm64.shiftVal, Arm64.shift64, Arm64.AddWithCarry64]
  bv_omega

/-- `law_mov` of `Compiler/Iface.lean` (without the `MovOK` restriction, not needed here) -/
theorem law_mov {d a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64}
    (hok : ok s) (hpc : s.pc = pc) (hal : pc.toNat % 4 = 0) (hi : instrAt s pc (encMov d a)) :
    runsTo s fun s' => (ok s' ∧ keep s s' ∧ s'.pc = next pc 1) ∧
      (∀ r, get s' r = if r = d then get s a else get s r) ∧ s'.mem = s.mem := by
  refine ⟨_, steps_one (step_of hok hpc hal hi (dec_mov d a)), ?_⟩
  simp only [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execLogicalShift, Arm64.State.readReg,
    Arm64.State.readReg64, orr_val]
  refine ⟨⟨hok, ⟨?_, rfl⟩, ?_⟩, ?_, rfl⟩
  · simp [Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write,
      xr_ne31, (xr_ne30 d).symm]
  · simp [Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, next, hpc]
  · intro r
    by_cases h : r = d
    · subst h; simp [get, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne31]
    · have : xr r ≠ xr d := fun e => h (xr_inj _ _ e)
      simp [get, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne31, h, this]

/-- `law_bin` for `op = add` (operand shape `a = d`, `b = d + 1`, `d < 10`, as in the interface) -/
theorem law_bin_add {d : Fin 10} {s : Arm64.State} {pc : BitVec 64}
    (hok : ok s) (hpc : s.pc = pc) (hal : pc.toNat % 4 = 0) (hi : instrAt s pc (encAdd (toR d) (toR d) (sucR d))) :
    runsTo s fun s' => (ok s' ∧ keep s s' ∧ s'.pc = next pc 1) ∧
      (∀ r, get s' r = if r = toR d then Op.add.eval (get s (toR d)) (get s (sucR d)) else get s r) ∧ s'.mem = s.mem := by
  refine ⟨_, steps_one (step_of hok hpc hal hi (dec_add d)), ?_⟩
  simp only [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execAddSubShift, Arm64.State.readReg,
    Arm64.State.readReg64, xr_ne31, add_val]
  refine ⟨⟨hok, ⟨?_, rfl⟩, ?_⟩, ?_, rfl⟩
  · simp [Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write,
      xr_ne31, (xr_ne30 (toR d)).symm]
  · simp [Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, next, hpc]
  · intro r
    by_cases h : r = toR d
    · subst h; simp [get, Op.eval, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne31]
    · have : xr r ≠ xr (toR d) := fun e => h (xr_inj _ _ e)
      simp [get, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne31, h, this]

/-- `law_ret`: return address = x30, no restriction on it -/
theorem law_ret {s : Arm64.State} {pc : BitVec 64}
    (hok : ok s) (hpc : s.pc = pc) (hal : pc.toNat % 4 = 0) (hi : instrAt s pc encRet) :
    runsTo s fun s' => (ok s' ∧ keep s s' ∧ s'.pc = s.regs.read 30#5) ∧ (∀ r, get s' r = get s r) ∧ s'.mem = s.mem := by
  refine ⟨_, steps_one (step_of hok hpc hal hi dec_ret), ?_⟩
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg64, Arm64.State.setPC, ok, keep, get,
    Arm64.RegFile.read]
  exact hok

#print axioms law_mov
#print axioms law_bin_add
#print axioms law_ret
end Proven.Apc

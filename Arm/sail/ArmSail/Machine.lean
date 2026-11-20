/- `armSail : Proven.Top.Machine` on the official Sail ARM v9.4-A model (outside `Spec/`).

* `step` = one Sail `step_model` (`ArmProof.stepModel`: `SEE := -1; __TopLevel (); __CycleEnd ()`), `none` on a model
  exception;
* `observe` = `_PC`, `x0..x30` (registers ≥ 31 read as 0: rv2arm never names sp/xzr as a data register, and every
  `A64Sem` field keeps them), and the bytes present in Sail's memory map;
* `configured` = `ArmFullB s n` for some `n` (the pinned EL3 / MMU-off configuration of `Arm/proofs/Arm/Full.lean`,
  any `BTypeNext`: `br` leaves `0b01`) and a `_PC`;
* RAM window `[2^31, 3·2^30)` as `A64Sem` requires; `VaOK` covers it (no device page there).

Proof notes: every per-form Sail lemma `full_X` concludes `∃ s', stepModel s = .ok () s' ∧ Abs s' a' ∧ ArmFullB s' n ∧
PC = p ∧ s'.mem = M`; `obs_eq` turns `Abs`+`PC` into `obsA p a' M`, so each `A64Sem` field reduces to an equation
between `obsA`s (`set_obsA`, `jump_obsA`). Permissions are not modelled by Sail (`X = W = True`). -/
import Spec.Top
import Nano.V2Self.Proof.Machine.A64Sem
import Arm.Mem
import Arm.FullSubs
import Arm.FullAluAdd
import Arm.FullAluLogic
import Arm.FullAluShift
import Arm.FullMul
import Arm.FullBrLdur
set_option linter.unusedVariables false
namespace ArmSail
open Proven.Top ArmProof

abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- one Sail `step_model` as a partial function -/
def stepS (s : St) : Option St :=
  match stepModel s with
  | .ok _ s' => some s'
  | .error _ _ => none

def pcOf (s : St) : BitVec 64 := ((s.regs.get? ._PC : Option (BitVec 64))).getD 0

/-- what `Spec` observes -/
def obsS (s : St) : MachineState where
  programCounter := UInt64.ofBitVec (pcOf s)
  register r := if r < 31 then UInt64.ofBitVec ((xget s.regs r).getD 0) else 0
  memory u := (s.mem.get? u.toNat).map UInt8.ofBitVec

def armSail : Machine where
  State := St
  step := stepS
  observe := obsS
  configured s := (∃ n, ArmFullB s n) ∧ (s.regs.get? ._PC : Option (BitVec 64)).isSome
  mapping := armMapping
  ramStart := 2 ^ 31
  ramEnd := 3 * 2 ^ 30

/-- Sail has no permissions here: both predicates are `True` -/
abbrev TT : St → Nat → Prop := fun _ _ => True

/-- the observation of a state with pc `p`, abstract registers `a`, memory `m` -/
def obsA (p : BitVec 64) (a : AState) (m : Mem) : MachineState :=
  ⟨UInt64.ofBitVec p, fun r => if r < 31 then UInt64.ofBitVec (a.x r) else 0, fun u => (m.get? u.toNat).map UInt8.ofBitVec⟩

theorem obs_eq {s : St} {a : AState} {p : BitVec 64} (ha : Abs s a) (hp : s.regs.get? ._PC = some p) :
    obsS s = obsA p a s.mem := by
  simp only [obsS, obsA, pcOf, hp, Option.getD_some]
  congr 1; funext r; split
  · rename_i hr; rw [ha.x r hr]; rfl
  · rfl

theorem ofBool_beq1 (b : BitVec 1) : BitVec.ofBool (b == 1#1) = b := by
  have : ∀ c : BitVec 1, c = 0#1 ∨ c = 1#1 := by decide
  rcases this b with rfl | rfl <;> rfl

/-- every configured state has an abstraction -/
theorem abs_ex {s : St} {n : BitVec 2} (hf : ArmFullB s n) : ∃ a, Abs s a := by
  obtain ⟨p, hp, -⟩ := hf.pins.ps
  refine ⟨⟨fun i => (xget s.regs i).getD 0, p.N == 1#1, p.Z == 1#1, p.C == 1#1, p.V == 1#1⟩, fun i hi => ?_,
    p, hp, (ofBool_beq1 _).symm, (ofBool_beq1 _).symm, (ofBool_beq1 _).symm, (ofBool_beq1 _).symm⟩
  have := hf.x i hi; revert this; cases xget s.regs i <;> simp

/-- a full step with a configured result is a `GoesK` -/
theorem goes1 {s s' : St} {o : MachineState} {n : BitVec 2} (h : stepModel s = .ok () s') (hf : ArmFullB s' n)
    {p : BitVec 64} (hp : s'.regs.get? ._PC = some p) (ho : obsS s' = o) : JT.GoesK armSail TT TT s o :=
  ⟨s', .step (show stepS s = some s' by simp [stepS, h]) .stop, ⟨⟨n, hf⟩, by simp [hp]⟩, ho,
    fun _ h => h, fun _ h => h⟩

theorem goes2 {s s1 s' : St} {o : MachineState} {n : BitVec 2} (h1 : stepModel s = .ok () s1)
    (h : stepModel s1 = .ok () s') (hf : ArmFullB s' n)
    {p : BitVec 64} (hp : s'.regs.get? ._PC = some p) (ho : obsS s' = o) : JT.GoesK armSail TT TT s o :=
  ⟨s', .step (show stepS s = some s1 by simp [stepS, h1]) (.step (show stepS s1 = some s' by simp [stepS, h]) .stop),
    ⟨⟨n, hf⟩, by simp [hp]⟩, ho, fun _ h => h, fun _ h => h⟩

theorem set_obsA {p : BitVec 64} {a : AState} {m : Mem} {d : Nat} (hd : d < 31) (v : BitVec 64) :
    obsA (p + 4) (a.setX d v) m = JT.setReg (obsA p a m) d (UInt64.ofBitVec v) := by
  simp only [obsA, JT.setReg]
  congr 1
  funext r
  by_cases e : r = d
  · subst e; simp [hd, AState.setX, show r ≠ 31 by omega]
  · simp only [e, ite_false, AState.setX, show d ≠ 31 by omega]

theorem jump_obsA {p : BitVec 64} {a : AState} {m : Mem} (t : BitVec 64) :
    obsA t a m = JT.jumpTo (obsA p a m) (UInt64.ofBitVec t) := rfl

/-! ## the premises of a field, on Sail -/

theorem map_ofBV {x : Option (BitVec 8)} {y : BitVec 8} (h : x.map UInt8.ofBitVec = some (UInt8.ofBitVec y)) :
    x = some y := by
  cases x with
  | none => simp at h
  | some v =>
    simp only [Option.map_some, Option.some.injEq] at h
    rw [show v = (UInt8.ofBitVec v).toBitVec from rfl, h]; rfl

/-- an observed byte at a Nat address below `2^64` is in Sail's memory -/
theorem byte_obs {s : St} {a : Nat} {b : UInt8} (ha : a < 2 ^ 64) (h : (obsS s).memory (UInt64.ofNat a) = some b) :
    s.mem.get? a = some b.toBitVec := by
  apply map_ofBV
  have e : (UInt64.ofNat a).toNat = a := by simp; omega
  simp only [obsS, e] at h; rw [h]; rfl

/-- the observed word at `p` is a `MemWord` -/
theorem memword {s : St} {p w : Nat} (hp : p + 4 ≤ 2 ^ 64) (h : JT.WordAt (obsS s) p w) :
    MemWord s.mem p (BitVec.ofNat 32 w) := by
  have g : ∀ k < 4, s.mem.get? (p + k) = some ((BitVec.ofNat 32 w).extractLsb' (8 * k) 8) := fun k hk =>
    byte_obs (by omega) (h k hk)
  exact ⟨g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)⟩

/-- what a field's premises give on Sail: the configuration, an abstraction, the pc and the fetched word -/
structure Pre (s : St) (w : Nat) (n : BitVec 2) (a : AState) (pc : BitVec 64) : Prop where
  hf : ArmFullB s n
  ha : Abs s a
  hpc : s.regs.get? ._PC = some pc
  va : VaOK pc.toNat
  al : pc.toNat % 4 = 0
  lo : 2 ^ 31 ≤ pc.toNat
  hi : pc.toNat + 4 ≤ 3 * 2 ^ 30
  hm : MemWord s.mem pc.toNat (BitVec.ofNat 32 w)
  obs : obsS s = obsA pc a s.mem

theorem pre {s : St} {w : Nat} (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat w) :
    ∃ n a pc, Pre s w n a pc := by
  obtain ⟨⟨n, hf⟩, hpc⟩ := hc
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp hpc
  obtain ⟨a, ha⟩ := abs_ex hf
  have e : (armSail.observe s).programCounter.toNat = pc.toNat := by
    show (UInt64.ofBitVec (pcOf s)).toNat = _; simp [pcOf, hpc]
  obtain ⟨h4, hlo, hhi⟩ := hp
  rw [e] at h4 hlo hhi hw
  simp only [armSail] at hlo hhi
  exact ⟨n, a, pc, hf, ha, hpc, vaRam hlo (by omega), h4, hlo, hhi, memword (by omega) hw, obs_eq ha hpc⟩

end ArmSail

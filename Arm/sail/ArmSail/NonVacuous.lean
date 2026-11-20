/- Non-vacuity of `armSail.configured` (verification aid; not imported by `ArmSail.Top`).

`ArmProof.witness_full` (Arm/proofs/Arm/Witness.lean) gives one state satisfying `ArmFull`, with `_PC = 0`,
`X0..X30 = 0` and the default (empty) memory. `StartCorrect` needs more: a PC in the RAM window, the call's addresses
in `x0..x4, x30`, and code/input bytes in memory. Here: for ANY `pc`, ANY `x : Nat → BitVec 64` and ANY memory map
`m`, the state `wst pc x m` is `armSail.configured`, and `armSail.observe` of it is exactly `pc`, `x` (below 31) and
the bytes of `m`. So `configured` constrains nothing that `StartCorrect` can see, and every remaining `StartCorrect`
premise is a statement about a freely chosen observation.

STATUS: written without a model build on the authoring box (no toolchain, 15 GB); to be compiled with
`lake env lean ArmSail/NonVacuous.lean` in Arm/sail once the partitioned model is built. -/
import ArmSail.Machine
import Arm.Witness
namespace ArmSail
open Proven.Top ArmProof

/-- write `x 0 .. x (k-1)` into `X0 .. X(k-1)` -/
def setXs (m : Regs) (x : Nat → BitVec 64) : Nat → Regs
  | 0 => m
  | k + 1 => xset (setXs m x k) k (x k)

theorem setXs_get (m : Regs) (x : Nat → BitVec 64) (k : Nat) (r : Register) (hr : ∀ i < 31, xreg i ≠ r) :
    (setXs m x k).get? r = m.get? r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (xset (setXs m x k) k (x k)).get? r = m.get? r
    rw [xset_get_ne _ _ _ _ hr, ih]

theorem setXs_xget (m : Regs) (x : Nat → BitVec 64) (k : Nat) (hk : k ≤ 31) (i : Nat) (hi : i < k) :
    xget (setXs m x k) i = some (x i) := by
  induction k with
  | zero => omega
  | succ k ih =>
    show xget (xset (setXs m x k) k (x k)) i = some (x i)
    rw [xget_xset _ (show k < 31 by omega)]
    by_cases e : i = k
    · rw [if_pos e, e]
    · rw [if_neg e]; exact ih (by omega) (by omega)

/-- the pinned witness with a chosen PC, chosen `X0..X30` and a chosen memory -/
def wst (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) : St :=
  { witness with regs := setXs (witnessRegs.insert ._PC (pc : RegisterType ._PC)) x 31, mem := m }

theorem wst_get (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) (r : Register) (h1 : ∀ i < 31, xreg i ≠ r)
    (h2 : r ≠ ._PC) : (wst pc x m).regs.get? r = witness.regs.get? r := by
  show (setXs (witnessRegs.insert ._PC (pc : RegisterType ._PC)) x 31).get? r = witnessRegs.get? r
  rw [setXs_get _ _ _ _ h1, Std.ExtDHashMap.get?_insert, dif_neg (fun e => h2 (eq_of_beq e).symm)]

theorem wst_pc (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) : (wst pc x m).regs.get? ._PC = some pc := by
  show (setXs (witnessRegs.insert ._PC (pc : RegisterType ._PC)) x 31).get? ._PC = some pc
  rw [setXs_get _ _ _ _ (xreg_ne' (by decide))]
  simp [Std.ExtDHashMap.get?_insert]

theorem wst_x (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) (i : Nat) (hi : i < 31) :
    xget (wst pc x m).regs i = some (x i) :=
  setXs_xget _ _ 31 (Nat.le_refl 31) i hi

/-- the pinned configuration holds whatever the PC, the X registers and the memory are -/
theorem wst_full (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) : ArmFull (wst pc x m) := by
  have hw : ArmFull witness := witness_full
  have hp0 : Pins witnessRegs := hw.pins
  have hp1 : Pins (witnessRegs.insert ._PC (pc : RegisterType ._PC)) := (pins_insert (r := ._PC) _ rfl).2 hp0
  have hp2 : Pins (setXs (witnessRegs.insert ._PC (pc : RegisterType ._PC)) x 31) :=
    pins_frame hp1 (fun r h _ _ => setXs_get _ _ _ r h) (fun p hp =>
      ⟨p, (setXs_get _ _ _ Register.PSTATE (xreg_ne' (by decide))).trans hp, rfl, rfl, rfl⟩)
  obtain ⟨b, hb, hbr⟩ := hw.bt
  obtain ⟨c, hc⟩ := hw.cc
  exact ⟨hp2,
    ⟨b, (wst_get pc x m Register.Branchtypetaken (xreg_ne' (by decide)) (by decide)).trans hb, hbr⟩,
    (wst_get pc x m Register.BTypeNext (xreg_ne' (by decide)) (by decide)).trans hw.btn,
    ⟨c, (wst_get pc x m Register.__cycle_count (xreg_ne' (by decide)) (by decide)).trans hc⟩,
    fun i hi => by rw [wst_x pc x m i hi]; rfl⟩

/-- **`armSail.configured` is satisfiable with any PC, any `x0..x30`, any memory.** -/
theorem wst_configured (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) : armSail.configured (wst pc x m) :=
  ⟨⟨0, wst_full pc x m⟩, by simp [wst_pc]⟩

/-! ## what `Spec` observes of the witness: exactly the chosen data -/

theorem wst_obs_pc (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) :
    (armSail.observe (wst pc x m)).programCounter = UInt64.ofBitVec pc := by
  show UInt64.ofBitVec (pcOf (wst pc x m)) = UInt64.ofBitVec pc
  simp only [pcOf, wst_pc, Option.getD_some]

theorem wst_obs_reg (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) (r : Nat) (hr : r < 31) :
    (armSail.observe (wst pc x m)).register r = UInt64.ofBitVec (x r) := by
  show (if r < 31 then UInt64.ofBitVec ((xget (wst pc x m).regs r).getD 0) else 0) = UInt64.ofBitVec (x r)
  rw [if_pos hr, wst_x pc x m r hr]; rfl

theorem wst_obs_mem (pc : BitVec 64) (x : Nat → BitVec 64) (m : Mem) (u : UInt64) :
    (armSail.observe (wst pc x m)).memory u = (m.get? u.toNat).map UInt8.ofBitVec := rfl

end ArmSail

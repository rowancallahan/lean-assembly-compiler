/- Mask and field facts for ArmBlock's Nat-built words (`ArmBlock.movz`, `addi`, …): the premises of the `dm_*`
lemmas, for symbolic register numbers and immediates in range. `mask32` decides the opcode mask bit by bit. -/
import Blocks.ArmBlockDefs
import Blocks.Base
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks

abbrev wd (n : Nat) : BitVec 32 := BitVec.ofNat 32 n

theorem fin32 : ∀ j < 32, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
    j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨
    j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by intro j hj; omega

set_option hygiene false in
/-- `wd n &&& K = C` for `n` = literal opcode + bounded fields: bit by bit, each by `omega` -/
macro "mask32" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  rcases fin32 j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp <;> omega))

/-- a field of `wd n`, as a number -/
theorem fld (n i k : Nat) : ((wd n).extractLsb' i k).toNat = n % 2 ^ 32 / 2 ^ i % 2 ^ k := by
  simp [Nat.shiftRight_eq_div_pow]

/-- a field equation `(wd n).extractLsb' i k).toNat = v` -/
macro "fldt" : tactic => `(tactic| (rw [fld]; omega))
/-- an immediate equation `((wd n).extractLsb' i k).setWidth 64 = BitVec.ofNat 64 v` -/
macro "immt" : tactic => `(tactic| (apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega))

end Proven.Apc.Blocks

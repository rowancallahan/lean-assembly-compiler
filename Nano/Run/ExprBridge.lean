/- Closing the link template ↔ Sail: for every J instruction the expression templates use, the word C's encoders emit
(`CallProbe.encG`, Proof/ExprExact.lean) is the word nano-v2/Sail runs (`SimW.encJ`, which the `SimW.sim_*` lemmas consume). -/
import Nano.Run.ExprExact
import Nano.Run.RvEnc
import Nano.Run.JLay
namespace CallProbe
open Bridge Nano.V2B

theorem sI_iu (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) : sI (iu z) = z := by
  unfold sI; rw [iu_toNat]; split <;> omega

theorem toU_toNat (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by simp [Nat.toUInt64]; omega

/-- the side conditions under which `encG i` is `SimW.encJ i` (register and immediate ranges, as in `SimW.SafeX`) -/
def GoodW : J → Prop
  | .addi rd rs imm => rd < 32 ∧ rs < 32 ∧ -2048 ≤ imm ∧ imm < 2048
  | .ld rd rs off => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048
  | .sd b a off => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048
  | .bgeu a b o => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 3 ∨ o = 4)
  | .beq a b o => a < 32 ∧ b < 32 ∧ o = 2
  | .bltu a b o => a < 32 ∧ b < 32 ∧ o = 2
  | .jal rd _ => rd < 32
  | .jalr rd rs => rd = 0 ∧ rs < 32
  | .alu op rd a b => rd < 32 ∧ a < 32 ∧ b < 32 ∧ 1 ≤ op ∧ op ≤ 8
  | .slli rd rs sh => rd < 32 ∧ rs < 32 ∧ sh < 64
  | .lbu rd rs off => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048
  | .srli _ _ _ => False
  | .bne _ _ _ => False
  | .sb _ _ _ => False

theorem encG_addi (rd rs : Nat) (imm : Int) (h : GoodW (.addi rd rs imm)) :
    (encG (.addi rd rs imm)).toNat = SimW.encJ (.addi rd rs imm) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [encG, SimW.encJ]
  rw [g10_I _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), sI_iu _ (by omega) (by omega)]

theorem encG_ld (rd rs : Nat) (off : Int) (h : GoodW (.ld rd rs off)) :
    (encG (.ld rd rs off)).toNat = SimW.encJ (.ld rd rs off) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [encG, SimW.encJ]
  rw [g11_I _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), sI_iu _ (by omega) (by omega)]

theorem encG_sd (b a : Nat) (off : Int) (h : GoodW (.sd b a off)) :
    (encG (.sd b a off)).toNat = SimW.encJ (.sd b a off) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [encG, SimW.encJ]
  rw [g12_I _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), sI_iu _ (by omega) (by omega)]

theorem iu8 : iu (4 * 2) = 8 := by decide

theorem encG_bgeu (a b : Nat) (o : Int) (h : GoodW (.bgeu a b o)) :
    (encG (.bgeu a b o)).toNat = SimW.encJ (.bgeu a b o) := by
  obtain ⟨h1, h2, ho⟩ := h
  simp only [encG, SimW.encJ]
  rw [g4_bgeu _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega)]
  rcases ho with rfl | rfl | rfl <;> rfl

theorem encG_beq (a b : Nat) (o : Int) (h : GoodW (.beq a b o)) :
    (encG (.beq a b o)).toNat = SimW.encJ (.beq a b o) := by
  obtain ⟨h1, h2, rfl⟩ := h
  simp only [encG, SimW.encJ]
  rw [g4_beq _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), iu8]
  have : sI 8 = 8 := by decide
  rw [this]

theorem encG_bltu (a b : Nat) (o : Int) (h : GoodW (.bltu a b o)) :
    (encG (.bltu a b o)).toNat = SimW.encJ (.bltu a b o) := by
  obtain ⟨h1, h2, rfl⟩ := h
  simp only [encG, SimW.encJ]
  rw [g4_bltu _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), iu8]
  have : sI 8 = 8 := by decide
  rw [this]

theorem iu_ofInt (z : Int) : iu z = UInt64.ofInt z := by
  apply UInt64.toNat.inj; rw [iu_toNat]; unfold UInt64.ofInt; rw [UInt64.toNat_ofNat']
  have h1 : (0 : Int) ≤ z % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h2 : z % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  omega

theorem encG_jal (rd : Nat) (off : Int) (h : GoodW (.jal rd off)) :
    (encG (.jal rd off)).toNat = SimW.encJ (.jal rd off) := by
  simp only [encG, SimW.encJ, iu_ofInt]

theorem encG_jalr (rd rs : Nat) (h : GoodW (.jalr rd rs)) :
    (encG (.jalr rd rs)).toNat = SimW.encJ (.jalr rd rs) := by
  obtain ⟨rfl, _⟩ := h
  rfl

set_option maxHeartbeats 2000000 in
theorem encG_alu (op rd a b : Nat) (h : GoodW (.alu op rd a b)) :
    (encG (.alu op rd a b)).toNat = SimW.encJ (.alu op rd a b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [encG, SimW.encJ]
  have hF : (aluF op).1.toNat < 128 ∧ (aluF op).2.toNat < 8 := by
    rcases (by omega : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [aluF] <;> decide
  rw [g1_enc _ _ _ _ _ hF.1 hF.2 (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2)
    (by rw [toU_toNat _ (by omega)]; exact h3), toU_toNat _ (by omega), toU_toNat _ (by omega), toU_toNat _ (by omega)]
  rcases (by omega : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [aluF, SimW.ropOf, I.enc] <;> rfl

theorem encG_slli (rd rs sh : Nat) (h : GoodW (.slli rd rs sh)) :
    (encG (.slli rd rs sh)).toNat = SimW.encJ (.slli rd rs sh) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [encG, SimW.encJ]
  rw [g2_enc _ _ _ _ _ (by decide) (by decide) (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega)]
  have : sI (sh.toUInt64) = (sh : Int) := by
    unfold sI; rw [toU_toNat _ (by omega)]; split <;> omega
  rw [this]; rfl

theorem encG_lbu (rd rs : Nat) (off : Int) (h : GoodW (.lbu rd rs off)) :
    (encG (.lbu rd rs off)).toNat = SimW.encJ (.lbu rd rs off) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [encG, SimW.encJ]
  rw [g2_enc _ _ _ _ _ (by decide) (by decide) (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
    toU_toNat _ (by omega), toU_toNat _ (by omega), sI_iu _ (by omega) (by omega)]
  rfl

/-- **the link**: for every template instruction, C's emitted word is the word Sail runs -/
theorem encG_encJ (i : J) (h : GoodW i) : (encG i).toNat = SimW.encJ i := by
  cases i with
  | addi rd rs imm => exact encG_addi _ _ _ h
  | ld rd rs off => exact encG_ld _ _ _ h
  | sd b a off => exact encG_sd _ _ _ h
  | bgeu a b o => exact encG_bgeu _ _ _ h
  | beq a b o => exact encG_beq _ _ _ h
  | bltu a b o => exact encG_bltu _ _ _ h
  | jal rd off => exact encG_jal _ _ h
  | jalr rd rs => exact encG_jalr _ _ h
  | alu op rd a b => exact encG_alu _ _ _ _ h
  | slli rd rs sh => exact encG_slli _ _ _ h
  | lbu rd rs off => exact encG_lbu _ _ _ h
  | srli _ _ _ => exact h.elim
  | bne _ _ _ => exact h.elim
  | sb _ _ _ => exact h.elim

end CallProbe

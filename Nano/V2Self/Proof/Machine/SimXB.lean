/- Machine bridge (Opus box E): Gen's words are the safe layer's words: `(encG i).toNat = encJX i` under
`GoodX` (GoodW plus beq +7, srli, bne +4, sb). -/
import Nano.V2Self.Proof.Machine.ExprBridge
import Nano.V2Self.Proof.Machine.RvEnc
import Nano.V2Self.Proof.Machine.JLay
import Nano.V2Self.Proof.Machine.StartCode
namespace CallProbe
open Bridge Nano.V2B

def GoodX : J → Prop
  | .beq a b o => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 7)
  | .srli rd rs sh => rd < 32 ∧ rs < 32 ∧ sh < 64
  | .bne a b o => a < 32 ∧ b < 32 ∧ o = 4
  | .sb b a off => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048
  | i => GoodW i

theorem encG_encJX (i : J) (h : GoodX i) : (encG i).toNat = SimW.encJX i := by
  cases i with
  | beq a b o =>
    obtain ⟨h1, h2, ho⟩ := h
    simp only [encG, SimW.encJX]
    rw [g4_beq _ _ _ (by rw [toU_toNat _ (by omega)]; exact h1) (by rw [toU_toNat _ (by omega)]; exact h2),
      toU_toNat _ (by omega), toU_toNat _ (by omega), sI_iu _ (by omega) (by omega)]
  | srli rd rs sh =>
    obtain ⟨h1, h2, h3⟩ := h
    show (encG (.srli rd rs sh)).toNat = SimW.encJ (.srli rd rs sh)
    rfl
  | bne a b o =>
    obtain ⟨h1, h2, rfl⟩ := h
    show (encG (.bne a b 4)).toNat = SimW.encJ (.bne a b 4)
    rfl
  | sb b a off =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    show (encG (.sb b a off)).toNat = SimW.encJ (.sb b a off)
    simp only [encG, SimW.encJ]
    congr 2
  | addi => exact encG_encJ _ h
  | ld => exact encG_encJ _ h
  | sd => exact encG_encJ _ h
  | bgeu => exact encG_encJ _ h
  | bltu => exact encG_encJ _ h
  | jal => exact encG_encJ _ h
  | jalr => exact encG_encJ _ h
  | alu => exact encG_encJ _ h
  | slli => exact encG_encJ _ h
  | lbu => exact encG_encJ _ h

end CallProbe
namespace Templates
open CallProbe

theorem startJ_good (S w : Nat) : ∀ i ∈ startJ S w, GoodX i := by
  intro i hi; simp only [startJ, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW]

theorem stubJ_good (S : Nat) : ∀ i ∈ stubJ S, GoodX i := by
  intro i hi; simp only [stubJ, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [GoodX, GoodW]

end Templates

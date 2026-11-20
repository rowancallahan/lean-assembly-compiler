/- **rv2arm's block correctness on DeepMind's AArch64 model** (`BlockOKD`): ArmBlock's `BlockOK` with `RelD` for
`RelA` and DeepMind steps (`Reach`) for `Runs`; same premises (`validJ`, `s.wk = 3`, `AccOK` with `NoWrap`). -/
import Blocks.KMem
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

/-- **Block correctness on DeepMind's machine** (ArmBlock's `BlockOK`, `RelD` for `RelA`): one J step is ≤ 4
DeepMind steps, `RelD` to `RelD` -/
def BlockOKD : Prop :=
  ∀ (C : List J) (D : Nat → Prop) (K : Nat → BitVec 64) (pc : Nat) (s : St) (j : J) (t : Arm64.State)
    (ps' : Nat × St), C[pc]? = some j → validJ C.length pc j → s.wk = 3 → AccOK C D (pc, s) →
    RelD C D K (pc, s) t → step C (pc, s) = some ps' → Reach t (RelD C D K ps')

theorem blockOKD : BlockOKD := by
  intro C D K pc s j t ps' hj hv hwk hacc hR hst
  simp only [AccOK, hj] at hacc
  cases j with
  | addi rd rs imm => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_addi hj hv hacc hR
  | ld rd rs off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_ld hj hv hacc.2 hacc.1.1 hR
  | sd r2 r1 off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_sd hj hv hacc.2 hacc.1.1 hR
  | jal rd off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_jal hj hv hR
  | jalr rd rs => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_jalr hj hv hacc hR
  | bgeu a b off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_bgeu hj hv hR
  | alu op rd a b => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_alu hj hv hR
  | slli rd rs sh => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_slli hj hv hR
  | lbu rd rs off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_lbu hj hv hacc.2 hacc.1.1 hR
  | beq a b off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_beq hj hv hR
  | bltu a b off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_bltu hj hv hR
  | srli rd rs sh => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_srli hj hv hR
  | bne a b off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_bne hj hv hR
  | sb r2 r1 off => simp only [step, hj, Option.some.injEq] at hst; subst hst; exact blk_sb hj hv hacc.2 hacc.1.1 hR

end Proven.Apc.Blocks

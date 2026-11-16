/- Integration glue: nano-proof's verbatim copy `Nano.S` of the stack generator (`Nano/StackRec.lean`) IS nano-e2e's
`Nano/Gen.lean` (`genR`, `depth`), so the lanes can be merged without either editing the other's file. -/
import Nano.Gen
import Nano.StackRec

namespace Nano.Bridge
open Nano

theorem ld_eq : @S.ld = @ld := rfl
theorem sd_eq : @S.sd = @sd := rfl
theorem addSp_eq : @S.addSp = @addSp := rfl
theorem push_eq : S.push = push := rfl
theorem li_eq : @S.li = @li := rfl
theorem binop_eq : @S.binop = @binop := rfl
theorem rd8_eq : S.rd8 = rd8 := rfl
theorem wr8_eq : S.wr8 = wr8 := rfl

theorem mkSc_eq : ∀ k b, S.mkSc k b = mkSc k b
  | 0, _ => rfl
  | k + 1, b => by simp only [S.mkSc, mkSc, mkSc_eq k b]

theorem cnt_eq : ∀ e, S.cnt e = cnt e
  | .acons _ r => by simp only [S.cnt, cnt, cnt_eq r]
  | .num _ | .var _ | .add _ _ | .sub _ _ | .mul _ _ | .let_ _ _ | .call _ _ | .anil => rfl

mutual
theorem genE_eq : ∀ (e : Ex) (sc : List Nat) (d : Nat), S.genE sc d e = genE sc d e
  | .num n, sc, d => by simp only [S.genE, genE, li_eq, push_eq]
  | .var i, sc, d => by simp only [S.genE, genE, ld_eq, push_eq]
  | .add a b, sc, d => by simp only [S.genE, genE, genE_eq a, genE_eq b, binop_eq]
  | .sub a b, sc, d => by simp only [S.genE, genE, genE_eq a, genE_eq b, binop_eq]
  | .mul a b, sc, d => by simp only [S.genE, genE, genE_eq a, genE_eq b, binop_eq]
  | .let_ v b, sc, d => by simp only [S.genE, genE, genE_eq v, genE_eq b, ld_eq, addSp_eq, sd_eq]
  | .call b as, sc, d => by
    simp only [S.genE, genE, genA_eq as, genE_eq b, ld_eq, addSp_eq, sd_eq, cnt_eq, mkSc_eq]
  | .anil, sc, d => by simp only [S.genE, genE]
  | .acons _ _, sc, d => by simp only [S.genE, genE]
theorem genA_eq : ∀ (e : Ex) (sc : List Nat) (d : Nat), S.genA sc d e = genA sc d e
  | .acons e r, sc, d => by simp only [S.genA, genA, genE_eq e, genA_eq r]
  | .num _, _, _ | .var _, _, _ | .add _ _, _, _ | .sub _ _, _, _ | .mul _ _, _, _ | .let_ _ _, _, _
  | .call _ _, _, _ | .anil, _, _ => by simp only [S.genA, genA]
end

theorem pro_eq : ∀ k, S.pro k = pro k
  | 0 => rfl
  | k + 1 => by simp only [S.pro, pro, pro_eq k, rd8_eq, push_eq]; rfl

/-- **the proved generator is the self-hosted one** -/
theorem genR_eq (p : Prog) : S.genR p = genR p := by
  simp only [S.genR, genR, pro_eq, genE_eq, mkSc_eq, ld_eq, wr8_eq]; rfl

mutual
theorem depE_eq : ∀ (e : Ex) (d : Nat), S.depE d e = depE d e
  | .num _, d | .var _, d => by simp only [S.depE, depE]
  | .add a b, d | .sub a b, d | .mul a b, d | .let_ a b, d => by simp only [S.depE, depE, depE_eq a, depE_eq b]
  | .call b as, d => by simp only [S.depE, depE, depA_eq as, depE_eq b, cnt_eq]
  | .anil, d | .acons _ _, d => by simp only [S.depE, depE]
theorem depA_eq : ∀ (e : Ex) (d : Nat), S.depA d e = depA d e
  | .acons e r, d => by simp only [S.depA, depA, depE_eq e, depA_eq r]
  | .num _, _ | .var _, _ | .add _ _, _ | .sub _ _, _ | .mul _ _, _ | .let_ _ _, _ | .call _ _, _ | .anil, _ => by
    simp only [S.depA, depA]
end

theorem depth_eq (p : Prog) : S.depth p = depth p := by simp only [S.depth, depth, depE_eq]

end Nano.Bridge

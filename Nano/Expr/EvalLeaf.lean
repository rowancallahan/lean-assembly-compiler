/- Nano/Expr/EvalLeaf: first lemmas of eval_emit (EXPR.md §6 step 2): the evaluator on the emitter's leaf shapes. -/
import Nano.Expr.Eval
namespace ExprSpec

/-- a UInt64 literal evaluates to its word -/
theorem eval_lit_uw (P : Prog) (f : Nat) (env : List V) (v : UInt64) :
    evalX P (f + 1) env (lit .uw v.toNat) = some (.w v) := by
  simp [lit, apps, U, evalX, spine]

/-- a Nat literal (fuel argument) evaluates to its number -/
theorem eval_lit_nt (P : Prog) (f : Nat) (env : List V) (k : Nat) :
    evalX P (f + 1) env (lit .nt k) = some (.n k) := by
  simp [lit, apps, evalX, spine]

/-- a bvar evaluates to its environment entry -/
theorem eval_bv (P : Prog) (f : Nat) (env : List V) (i : Nat) : evalX P (f + 1) env (.bv i) = env[i]? := by
  simp [evalX]

end ExprSpec

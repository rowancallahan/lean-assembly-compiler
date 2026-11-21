/- Nano/Expr/CLean: **C's emitted Expr = Lean's elaborated Expr**, kernel-checked per def. `ExprLeanC.defs` is
Lean's own normalized Expr of every def of C, as `X` data (generated from Lean's environment by
Testing/nano/expr/lean_expr.lean + gen_leanc.py: the TRUSTED step, EXPR.md §3). The kernel checks that the
(name, type, value) nano emits for each def of C (`oC`, from C's certified AST `Cert.PC.all`) IS Lean's, except
`o32`, `o38` (Nat vs UInt64 for a {0,1} flag, EXPR.md §0; Nat step 1 removes them). -/
import Nano.Expr.CExpr
import Nano.Expr.LeanC
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ExprSpec

/-- the defs whose Expr differs (representation only) -/
def exC : List String := ["o32", "o38"]

theorem C_lean_check : oC.length = ExprLeanC.defs.length ∧
    ((oC.zip ExprLeanC.defs).all fun (e, l) => decide (e = l) || exC.contains e.1) = true := by
  decide +kernel

theorem zip_check {α : Type} [DecidableEq α] {ex : List String} :
    ∀ {l1 l2 : List (String × α)}, l1.length = l2.length →
      ((l1.zip l2).all fun (e, l) => decide (e = l) || ex.contains e.1) = true →
      ∀ i (h : i < l1.length), l1[i].1 ∉ ex → ∃ h', l1[i] = l2[i]'h'
  | [], _, _, _, i, h, _ => absurd h (by simp)
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | e :: l1, f :: l2, hl, hall, i, h, hn => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] at hall
    cases i with
    | zero =>
      refine ⟨by simp, ?_⟩
      rcases hall.1 with h1 | h1
      · exact h1
      · exact absurd h1 hn
    | succ i =>
      obtain ⟨h', he⟩ := zip_check (l1 := l1) (l2 := l2) (by simpa using hl) hall.2 i (by simpa using h) hn
      exact ⟨by simpa using h', he⟩

/-- every def of C outside `exC`: nano's emitted (name, type, value) is Lean's -/
theorem C_lean : ∀ i (h : i < oC.length), oC[i].1 ∉ exC → ∃ h', oC[i] = ExprLeanC.defs[i]'h' :=
  zip_check C_lean_check.1 C_lean_check.2

end ExprSpec

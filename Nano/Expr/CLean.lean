/- Nano/Expr/CLean: **C's emitted Expr = Lean's elaborated Expr**, kernel-checked, for every def. `ExprLeanC.defs` is
Lean's own normalized Expr of every def of C, as `X` data (generated from Lean's environment by
Testing/nano/expr/lean_expr.lean + gen_leanc.py: the TRUSTED step, EXPR.md §3; Lean's side is read through `eq_def`
for every def, N1). The kernel checks that the list `oC` nano emits for C's certified AST `Cert.PC.all` IS that list,
in chunks of 85 defs (one check of all 338 defs needs more memory than the build machines have). -/
import Nano.Expr.CExpr
import Nano.Expr.LeanC
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false  -- one kernel check at a time (memory)
namespace ExprSpec

theorem C_lean0 : (oC.take 85 == ExprLeanC.defs.take 85) = true := by decide +kernel
theorem C_lean1 : ((oC.drop 85).take 85 == (ExprLeanC.defs.drop 85).take 85) = true := by decide +kernel
theorem C_lean2 : (((oC.drop 85).drop 85).take 85 == ((ExprLeanC.defs.drop 85).drop 85).take 85) = true := by
  decide +kernel
theorem C_lean3 : ((((oC.drop 85).drop 85).drop 85).take 85 ==
    (((ExprLeanC.defs.drop 85).drop 85).drop 85).take 85) = true := by decide +kernel
theorem C_lean4 : ((((oC.drop 85).drop 85).drop 85).drop 85 ==
    (((ExprLeanC.defs.drop 85).drop 85).drop 85).drop 85) = true := by decide +kernel

theorem eq_of_take_drop {α : Type} {l1 l2 : List α} (n : Nat) (h1 : l1.take n = l2.take n)
    (h2 : l1.drop n = l2.drop n) : l1 = l2 := by
  rw [← List.take_append_drop n l1, ← List.take_append_drop n l2, h1, h2]

/-- **every def of C**: nano's emitted (name, type, value) list is Lean's -/
theorem C_lean : oC = ExprLeanC.defs := by
  have h0 := C_lean0; have h1 := C_lean1; have h2 := C_lean2; have h3 := C_lean3; have h4 := C_lean4
  simp only [beq_iff_eq] at h0 h1 h2 h3 h4
  exact eq_of_take_drop 85 h0 (eq_of_take_drop 85 h1 (eq_of_take_drop 85 h2 (eq_of_take_drop 85 h3 h4)))

theorem C_lean_all : oC.length = ExprLeanC.defs.length ∧ ∀ i (h : i < oC.length), ∃ h', oC[i] = ExprLeanC.defs[i]'h' :=
  ⟨by rw [C_lean], fun i _ => ⟨by rw [← C_lean]; assumption, by simp [C_lean]⟩⟩

end ExprSpec

import Lean
import Compiler.Ir.Syntax
open Lean
deriving instance ToExpr for Proven.Op
deriving instance ToExpr for Proven.Mach.MOp
deriving instance ToExpr for Proven.Mach.Cond
deriving instance ToExpr for Proven.Ir.Arg
deriving instance ToExpr for Proven.Ir.Rhs
deriving instance ToExpr for Proven.Ir.Tst
deriving instance ToExpr for Proven.Ir.Inst
deriving instance ToExpr for Proven.Ir.Term
deriving instance ToExpr for Proven.Ir.Block
deriving instance ToExpr for Proven.Ir.Func
deriving instance ToExpr for Proven.Ir.Prog
#synth ToExpr (Proven.Ir.Prog Nat)
#synth ToExpr (BitVec 64)

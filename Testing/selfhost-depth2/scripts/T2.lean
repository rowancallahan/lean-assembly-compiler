import Riscv.Frontx.Translate
import Riscv.Frontx.IndCmd
import Riscv.Back.Top
import Riscv.Back.IrTop
import Riscv.Back.Wide
import Compiler.Ir.Emit
import Compiler.Opt.Sel
import Spec.Code
set_option linter.all false
set_option maxHeartbeats 400000
open Proven.Frontx
-- enums
frontx_ind_type TOp := Proven.Op
frontx_ind_type TMOp := Proven.Mach.MOp
frontx_ind_type TCond := Proven.Mach.Cond
frontx_ind_type TWOp := Proven.Mach.WOp
frontx_ind_type TLiStep := Proven.Mach.Riscv.LiStep
frontx_ind_type TEOp := Proven.Ir.EOp
frontx_ind_type TKd := Proven.Mach.Ind.Kd
frontx_ind_type TFld := Proven.Mach.Ind.Fld
-- recursive, Nat location
frontx_ind_type TTst := Proven.Mach.IR.Tst Nat
frontx_ind_type TArg := Proven.Mach.IR.Arg Nat
frontx_ind_type TIns := Proven.Mach.IR.Ins Nat
frontx_ind_type TCode := Proven.Mach.IR.Code Nat
frontx_ind_type TCodeN := Proven.Mach.IR.Code Nat nesting Proven.Mach.IR.Code Nat
frontx_ind_type TIrArg := Proven.Ir.Arg Nat
frontx_ind_type TIrInst := Proven.Ir.Inst Nat
frontx_ind_type TIrRhs := Proven.Ir.Rhs Nat
frontx_ind_type TIrTerm := Proven.Ir.Term Nat
frontx_ind_type TIrBlock := Proven.Ir.Block Nat
frontx_ind_type TSExp := Proven.Mach.Sel.SExp
frontx_ind_type TExp := Proven.Exp
frontx_ind_type TAExp := Proven.AExp
frontx_ind_type TBExp := Proven.Mach.BExp
frontx_ind_type TMBStmt := Proven.Mach.BStmt
frontx_ind_type TCS := Proven.Mach.IR.Tst Nat
frontx_ind_type TStr := Proven.Ir.Val

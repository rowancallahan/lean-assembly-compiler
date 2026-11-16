/- Monomorphisation of type variables (`frontx_mono`, NOTES section 35): the self-hoster's IR accessors, generic in the
register type (`Mach.IR.Tst ρ`, `Ir.Tst ρ`, `Mach.IR.Ins α`, `Mach.IR.Arg α`, `Ir.Block ρ`), specialised at
`ρ := Nat` (the type after allocation) and compiled verbatim (their own equations, the type argument fixed).
Each: `f.at_Nat.eq : f.at_Nat = @f Nat`, `f.at_Nat.implements1`. -/
import Riscv.Frontx.Mono
import Compiler.Opt.Alloc
import Compiler.Opt.Live
import Compiler.Ir.Syntax

set_option linter.unusedVariables false

namespace Proven.Frontx.MonoEx

frontx_ind_type TArg := Proven.Mach.IR.Arg Nat
frontx_ind_type TTst := Proven.Mach.IR.Tst Nat nesting Proven.Mach.IR.Arg Nat, Proven.Mach.Cond
frontx_ind_type TIns := Proven.Mach.IR.Ins Nat nesting Proven.Mach.IR.Arg Nat, Proven.Op, Proven.Mach.MOp
frontx_ind_type TIrTst := Proven.Ir.Tst Nat nesting Proven.Ir.Arg Nat, Proven.Mach.Cond
frontx_ind_type TOptN := Option Nat
frontx_ind_type TListN := List Nat
frontx_ind_type TIrBlock := Proven.Ir.Block Nat nesting List Nat, List (Proven.Ir.Inst Nat), Proven.Ir.Inst Nat,
  Proven.Ir.Term Nat, Proven.Ir.Rhs Nat, Proven.Ir.Arg Nat, List (Proven.Ir.Arg Nat), Proven.Ir.Tst Nat,
  Proven.Mach.Cond, Proven.Op, Proven.Mach.MOp

frontx_mono Proven.Mach.IR.Tst.a at Nat on TTst
frontx_mono Proven.Mach.IR.Tst.b at Nat on TTst
frontx_mono Proven.Mach.IR.Tst.c at Nat on TTst
frontx_mono Proven.Ir.Tst.a at Nat on TIrTst
frontx_mono Proven.Ir.Tst.b at Nat on TIrTst
frontx_mono Proven.Ir.Tst.c at Nat on TIrTst
frontx_mono Proven.Mach.IR.Ins.dst at Nat on TIns using TOptN
frontx_mono Proven.Mach.IR.Arg.regs at Nat on TArg using TListN
frontx_mono Proven.Ir.Block.term at Nat on TIrBlock
frontx_mono Proven.Ir.Block.params at Nat on TIrBlock
frontx_mono Proven.Ir.Block.body at Nat on TIrBlock

end Proven.Frontx.MonoEx

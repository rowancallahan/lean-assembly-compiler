/- The hand-written RTL programs (`Compiler/Ir/Examples.lean`) through `Ir.compile` on RISC-V: both compile, `mix`
is longer than 1024 words, and its loop exit uses the long branch form (`br ¬c +2; jmp far`). QEMU + Sail tests:
`Testing/asm/emit_ir.lean`, `Testing/asm/ir_test.py`. -/
import Riscv.Back.IrTop
import Compiler.Ir.Examples

namespace Proven.Ir.Examples
open Proven.Ir Proven.Mach Proven.Mach.Riscv

/-- inverted short branches over one jump (the long form of `brTo`, on `r0, r1`) -/
def longBranches : List EOp → Nat
  | .w (.br .ne a (some b) false 2) :: .w (.jmp _ _) :: os =>
    (if a = R0 ∧ b = R1 then 1 else 0) + longBranches os
  | _ :: os => longBranches os
  | [] => 0

#guard (compileW reverse).isSome
#guard ((compileW mix).map (·.1.length)).getD 0 > 1024
#guard (((alloc mix).bind fun q => rvT.lin q).map fun c => longBranches c).getD 0 ≥ 1

end Proven.Ir.Examples

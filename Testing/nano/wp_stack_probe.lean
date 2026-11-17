/- PROBE (nano-int, 2026-11-17): does the paged front end (`wp_compile`) accept an explicit-stack machine?  YES, in this
   shape (6.5 min, `umE.compiles` / `umE.computes`, Sail axioms only).  Not part of the `Nano` lib (slow); run with
   `lake env lean Testing/nano/wp_stack_probe.lean`.  Findings in Testing/notes/NANO_INT.md. -/
import Riscv.Frontx.WpCmd
namespace NanoW
open Proven.WA

/-- uniform-step stack machine: every step consumes one input byte, writes one stack cell and pushes two output bytes
(0 = padding); `sp` and the written values are nested conditionals, the sizes are branch-free. -/
def um (buf src : ByteArray) (i sp : Nat) : ByteArray :=
  if i < src.size then
    um (((buf.set! sp (if src.get! i == 40 || src.get! i == 43 then src.get! i else buf.get! sp)).push
          (if src.get! i == 41 && decide (0 < sp) then buf.get! (sp - 1) else 0)).push
          (if src.get! i == 40 || src.get! i == 41 || src.get! i == 43 then 0 else src.get! i))
      src (i + 1 + 0 * sp)
      (if src.get! i == 40 || src.get! i == 43 then sp + 1
       else if src.get! i == 41 && decide (0 < sp) then sp - 1 else sp)
  else buf
termination_by src.size - i

def umE (xs : ByteArray) : ByteArray := um xs xs 0 0
wp_compile umE max 65536
  invariant fun (buf src : ByteArray) (i sp : Nat) => sp ≤ i ∧
    i ≤ src.size ∧ buf.size + 2 * (src.size - i) ≤ 262144 ∧ src.size < 2 ^ 32
  measure fun (_buf src : ByteArray) (i _sp : Nat) => src.size - i

#check @umE.compiles
#check @umE.computes
#print axioms umE.compiles
#print axioms umE.computes
end NanoW

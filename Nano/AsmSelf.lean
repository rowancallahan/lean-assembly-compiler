import Nano.AsmSelfC
/- the assembler stage compiled by OUR compiler (front end `frontx_compile`, list view; Nano/AsmSelfC.lean), with a
machine theorem. This is `frontx_implements_listC nanoAsm` (Riscv/Frontx/Checked.lean) written out, with the
register choice as a literal: computing it (`pickListC`, untrusted) in the interpreter took 186 s of the build.
The kernel checks that the choice is accepted (`optB`, `decide +kernel`). Regenerate after a change to `asm`:
`#eval pickListC nanoAsm.slots nanoAsm.prog` (a choice that is not accepted fails the build). -/
namespace Nano.Self
open Proven Proven.Frontx

def nanoAsm (xs : ByteArray) : List UInt8 := Nano.asm xs.data.toList
theorem nanoAsm_eq (xs : ByteArray) : nanoAsm xs = Nano.asm.view xs 0 := rfl
frontx_entry nanoAsm from nanoAsm_eq

/-- the register table (`pickListC nanoAsm.slots nanoAsm.prog`, untrusted) -/
def nanoAsm.tbl : List (Nat × Nat) := [(0, 11), (1, 12), (2, 13), (3, 14), (4, 7), (5, 8), (6, 9), (7, 10), (9, 7),
  (11, 1), (32, 0), (33, 2), (34, 4), (35, 3), (36, 4), (37, 5)]
/-- the spilled slots (`pickListC nanoAsm.slots nanoAsm.prog`, untrusted) -/
def nanoAsm.spl : List Nat := [16, 15, 18, 17, 20, 19, 13, 4, 5, 6, 8, 9, 10, 11, 12, 22, 0, 21, 14, 7, 2]
def nanoAsm.code : List (BitVec 32) := listCodeC nanoAsm.slots nanoAsm.tbl nanoAsm.spl nanoAsm.prog
set_option maxHeartbeats 0 in
theorem nanoAsm.implements1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) nanoAsm.code nanoAsm
    (fun _ => 8 * (nanoAsm.slots + 1) + 7) (retLen := true) :=
  implements1_listC nanoAsm nanoAsm.slots (by decide) nanoAsm.prog nanoAsm.tbl nanoAsm.spl (by decide +kernel)
    nanoAsm.exec
#print axioms nanoAsm.implements1

end Nano.Self

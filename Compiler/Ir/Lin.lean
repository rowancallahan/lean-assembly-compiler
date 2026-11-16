/- The minimal back-end pipeline below RTL (`Testing/notes/IR_DESIGN.md` §2.4, passes 8, 10, 11, 15 at their
simplest), target-generic:
* allocation: every value in a frame slot.  The trivial allocation keeps virtual register `x` in slot `x`; its
  validation is emission's check that every location is below the slot count `nS` (`emitF` fails otherwise);
* linearisation: blocks in list order, a jump to the next block's position falls through (`jTo`);
* long branches and placement: `emitF` with positions from the untrusted fixpoint `layout`. -/
import Compiler.Ir.Emit

namespace Proven.Ir
open Proven.Mach
set_option autoImplicit false

def Arg.locs : Arg Nat → List Nat
  | .r x => [x]
  | .i _ => []

def Inst.locs : Inst Nat → List Nat
  | .let_ d (.arg a) => d :: a.locs
  | .let_ d (.op _ a b) => d :: a.locs ++ b.locs
  | .let_ d (.mop _ a b) => d :: a.locs ++ b.locs
  | .let_ d (.padd p i) => d :: p :: i.locs
  | .ldb d p i => d :: p :: i.locs
  | .stb v p i => p :: v.locs ++ i.locs
  | .ld d p _ => [d, p]
  | .st v p _ => p :: v.locs
  | .alloc d n => d :: n.locs
  | .free p => [p]
  | .call ds _ as => ds ++ (as.map Arg.locs).flatten

def Term.locs : Term Nat → List Nat
  | .jmp _ as => (as.map Arg.locs).flatten
  | .br t _ a₁ _ a₂ => t.a.locs ++ t.b.locs ++ (a₁.map Arg.locs).flatten ++ (a₂.map Arg.locs).flatten
  | .switch x _ _ => [x]
  | .ret vs => (vs.map Arg.locs).flatten

def Block.locs (B : Block Nat) : List Nat := B.params ++ (B.body.map Inst.locs).flatten ++ B.term.locs

/-- the number of slots of the trivial allocation: one more than the largest location (untrusted) -/
def Func.nSlots (F : Func Nat) : Nat :=
  ((F.params ++ (F.blocks.map fun b => b.2.locs).flatten).foldl max 0) + 1

namespace Target
variable (T : Target)

/-- **the Lin code of a program's `main`**: the operations and the slot count -/
def lin (P : Prog Nat) : Option (List EOp × Nat) :=
  match P.funcs[P.main]? with
  | some F =>
    let nS := F.nSlots
    let h := T.layout F nS (F.blocks.length + 4) ([], 0)
    (T.emitF F nS (posOf h.1) h.2).map fun c => (c, nS)
  | none => none

end Target
end Proven.Ir

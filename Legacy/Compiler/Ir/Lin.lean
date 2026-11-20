/- The minimal back-end pipeline below RTL (`Testing/notes/IR_DESIGN.md` §2.4, passes 8, 10, 11, 15 at their
simplest), target-generic:
* allocation: every value in a frame slot.  The trivial allocation keeps virtual register `x` in slot `x`; its
  validation is emission's check that every location is below the slot count `nS` (`emitF` fails otherwise);
* linearisation: blocks in list order, a jump to the next block's position falls through (`jTo`);
* long branches and placement: `emitF` with positions from the untrusted fixpoint `layout`. -/
import Legacy.Compiler.Ir.Emit

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

/-- the registers of a function -/
def Func.locs (F : Func Nat) : List Nat := F.params ++ (F.blocks.map fun b => b.2.locs).flatten

/-- position in a list (untrusted choice of slots) -/
def idx : List Nat → Nat → Nat
  | [], _ => 0
  | v :: vs, x => if v = x then 0 else idx vs x + 1

/-- the list without repeats (untrusted) -/
def dedup (L : List Nat) : List Nat := L.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- distinct registers get distinct slots -/
def injOn (σ : Nat → Nat) (L : List Nat) : Bool := L.all fun x => L.all fun y => σ x != σ y || x == y

def Func.rename (σ : Nat → Nat) (F : Func Nat) : Func Nat :=
  { F with params := F.params.map σ, blocks := F.blocks.map fun b => (b.1, b.2.map σ) }

/-- one function: every register in its own slot (its position in `D`, untrusted), if the check passes: every
register is in `D`, and distinct registers of `D` get distinct slots -/
def Func.allocD (F : Func Nat) (D : List Nat) : Option (Func Nat) :=
  if F.locs.all (fun x => D.contains x) = true ∧ injOn (idx D) D = true then
    some { F.rename (idx D) with slots := D.length }
  else none

def Func.alloc1 (F : Func Nat) : Option (Func Nat) := F.allocD (dedup F.locs)

/-- **the trivial allocation** (validated): every function's registers in slots -/
def alloc (P : Prog Nat) : Option (Prog Nat) :=
  (P.funcs.mapM Func.alloc1).map fun fs => ⟨fs, P.main⟩

namespace Target
variable (T : Target)

/-- **the Lin code of a program** -/
def lin (P : Prog Nat) : Option (List EOp) :=
  T.emitP P (T.layout P (rounds P) ⟨[], [], 0⟩)

end Target
end Proven.Ir

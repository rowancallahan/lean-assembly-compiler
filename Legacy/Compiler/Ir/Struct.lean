/- Structured code for front ends (`Testing/notes/IR_DESIGN.md` §3): straight-line instructions, `if`, `while`
(`SC`), and code that ends in a terminator (`TC`: `ret`, a jump with arguments, `switch`), flattened into the
blocks of an RTL function (`flatS`, `flatT`: fresh labels from a counter; every `if` / loop closes the current
block).  Front ends lower into `SC` / `TC` and prove their code against the big-step meaning of `SC` / `TC`
(`Compiler/Ir/StructOk.lean`); the flattening is proved once.

Pure Lean (core only). -/
import Legacy.Compiler.Ir.Sem

namespace Proven.Ir
open Proven.Mach
set_option autoImplicit false

/-- straight-line code with structured control -/
inductive SC where
  | nop
  | i (x : Inst VReg)
  | seq (a b : SC)
  /-- `if t then a else b` -/
  | ite (t : Tst VReg) (a b : SC)
  /-- `while t do b` -/
  | loop (t : Tst VReg) (b : SC)
  deriving Repr

/-- code ending in a terminator -/
inductive TC where
  | seq (a : SC) (t : TC)
  | ite (t : Tst VReg) (a b : TC)
  | term (t : Term VReg)
  deriving Repr

/-- `a; b; ...` -/
def SC.seqs : List SC → SC
  | [] => .nop
  | [a] => a
  | a :: as => .seq a (SC.seqs as)

/-- the flattening state: the next fresh label, the finished blocks, the open block (label, parameters,
instructions so far) -/
structure GS where
  nl : Nat
  bs : List (Lbl × Block VReg)
  cl : Lbl
  cp : List VReg
  ci : List (Inst VReg)

/-- close the open block with a terminator -/
def GS.close (g : GS) (t : Term VReg) : GS := { g with bs := g.bs ++ [(g.cl, ⟨g.cp, g.ci, t⟩)] }

/-- open a fresh block without parameters -/
def GS.open (g : GS) (l : Lbl) : GS := { g with cl := l, cp := [], ci := [] }

def flatS : SC → GS → GS
  | .nop, g => g
  | .i x, g => { g with ci := g.ci ++ [x] }
  | .seq a b, g => flatS b (flatS a g)
  | .ite t a b, g =>
    let g1 := ({ g with nl := g.nl + 3 }.close (.br t g.nl [] (g.nl + 1) [])).open g.nl
    let g2 := ((flatS a g1).close (.jmp (g.nl + 2) [])).open (g.nl + 1)
    ((flatS b g2).close (.jmp (g.nl + 2) [])).open (g.nl + 2)
  | .loop t b, g =>
    let g1 := ({ g with nl := g.nl + 3 }.close (.jmp g.nl [])).open g.nl
    let g2 := (g1.close (.br t (g.nl + 1) [] (g.nl + 2) [])).open (g.nl + 1)
    ((flatS b g2).close (.jmp g.nl [])).open (g.nl + 2)

def flatT : TC → GS → GS
  | .seq a t, g => flatT t (flatS a g)
  | .ite t a b, g =>
    let g1 := ({ g with nl := g.nl + 2 }.close (.br t g.nl [] (g.nl + 1) [])).open g.nl
    flatT b ((flatT a g1).open (g.nl + 1))
  | .term t, g => g.close t

/-- regions `(label, code)` in order; the first with parameters `ps` (the entry), labels for the inner blocks
from `nl` -/
def flatRs (nl : Nat) (ps : List VReg) : List (Lbl × TC) → List (Lbl × Block VReg)
  | [] => []
  | (l, t) :: rs =>
    let g := flatT t ⟨nl, [], l, ps, []⟩
    g.bs ++ flatRs g.nl [] rs

/-- **an RTL function** from regions, the first is the entry -/
def mkFunc (params : List VReg) (ps : List VReg) (nl : Nat) (rs : List (Lbl × TC)) : Func VReg :=
  ⟨params, (rs.head?.map (·.1)).getD 0, flatRs nl ps rs, 0⟩

end Proven.Ir

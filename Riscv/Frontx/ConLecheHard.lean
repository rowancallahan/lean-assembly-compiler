/- con-leche hard blockers (NOTES section 36) on the inductive path: specialisation of a constant scalar parameter
(`liftLooseBVars`, `abstract1`), wildcard patterns inside nested patterns (`isStrLit`, `isNatZero`, `isBoolTrue`),
named constants compared inside a function (`c == natZeroName`), a match on a `Nat` together with the tree
(`peelPis`), `Option Expr` results with their payload (the `(full)` shape `TExprF`).
con-leche @6810492c1, verbatim (file:line per block). -/
import Riscv.Frontx.ExprExamples
import Riscv.Frontx.ConLecheBlk

set_option linter.unusedVariables false

namespace ConLeche.Expr

-- Kernel/ExprOps.lean:677-692
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam ty body =>
    .lam (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .forallE ty body =>
    .forallE (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .letE ty v body =>
    .letE (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)

-- Kernel/ExprOps.lean:739-750
def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx ty => if idx = d then .bvar k else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstract1 f d k) (abstract1 a d k)
  | .lam ty body => .lam (abstract1 ty d k) (abstract1 body d (k + 1))
  | .forallE ty body => .forallE (abstract1 ty d k) (abstract1 body d (k + 1))
  | .letE ty val body =>
    .letE (abstract1 ty d k) (abstract1 val d k) (abstract1 body d (k + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstract1 e d k)

-- Kernel/PropRead.lean:44-47
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b => peelPis k b
  | _ + 1, _ => none

-- Kernel/PropRead.lean:51-54
def binderDom : Nat → Expr → Option Expr
  | 0, .forallE A _ => some A
  | k + 1, .forallE _ b => binderDom k b
  | _, _ => none

end ConLeche.Expr

namespace ConLeche

-- Kernel/CoreDefs.lean:440-442
@[inline] def Expr.isEagerReduce : Expr → Bool
  | .app (.app (.const c _) _) _ => c == eagerReduceName
  | _ => false

-- Kernel/CoreDefs.lean:449-451
def Expr.isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false

-- Kernel/Core.lean:1528-1531
def Expr.isNatZero : Expr → Bool
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false

-- Kernel/Core.lean:1535-1538
def Expr.natPred? : Expr → Option Expr
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app (.const c []) x => if c = natSuccName then some x else none
  | _ => none

end ConLeche

namespace Proven.Frontx.ConLecheHard
open Proven.Frontx.ExprEx

/-- entry: lift the loose bound variables at or above the cutoff (from the input) by one (`amount` fixed at `1`:
the front end specialises `liftLooseBVars` to `lift1.spec`) -/
def lift1 (e : ConLeche.Expr) (c : Nat) : ConLeche.Expr := ConLeche.Expr.liftLooseBVars 1 c e
frontx_ind lift1 on TExpr

/-- entry: abstract `fvar 0` to the bound variable at the depth from the input (`d` fixed at `0`) -/
def abs0 (e : ConLeche.Expr) (k : Nat) : ConLeche.Expr := ConLeche.Expr.abstract1 e 0 k
frontx_ind abs0 on TExpr

frontx_ind ConLeche.Expr.isStrLit on TExpr
frontx_ind ConLeche.Expr.isNatZero on TExpr
frontx_ind ConLeche.Expr.isBoolTrue on TExpr

-- `Expr` with `List Expr` and `Option Expr` whose elements / values are in the byte format (`(full)`)
frontx_ind_type (full) TExprF := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List ConLeche.Level,
  ConLeche.Literal, List ConLeche.Expr, Option ConLeche.Expr

/-- entry: peel the number of `∀` binders given in the input -/
def peelN (e : ConLeche.Expr) (k : Nat) : Option ConLeche.Expr := ConLeche.Expr.peelPis k e
frontx_ind peelN on TExprF

/-- entry: the domain of the `∀` binder at the position given in the input -/
def domN (e : ConLeche.Expr) (k : Nat) : Option ConLeche.Expr := ConLeche.Expr.binderDom k e
frontx_ind domN on TExprF

end Proven.Frontx.ConLecheHard

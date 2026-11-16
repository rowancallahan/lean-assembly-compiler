import Riscv.Frontx.ExprExamples
namespace ConLeche
open Name (anonymous)
def natName : Name := anonymous |>.str "Nat"
def natZeroName : Name := natName |>.str "zero"
def natSuccName : Name := natName |>.str "succ"
def boolTrueName : Name := (Name.str .anonymous "Bool").str "true"
def Expr.isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false
def Expr.isNatZero : Expr → Bool
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false
def Expr.natPred? : Expr → Option Expr
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app (.const c []) x => if c = natSuccName then some x else none
  | _ => none
namespace Expr
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b => peelPis k b
  | _ + 1, _ => none
def binderDom : Nat → Expr → Option Expr
  | 0, .forallE A _ => some A
  | k + 1, .forallE _ b => binderDom k b
  | _, _ => none
def piSortTeleLen? : Expr → Option Nat
  | .forallE _ body => (Expr.piSortTeleLen? body).map (· + 1)
  | .sort _ => some 0
  | _ => none
end Expr
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const c [] => if c = natZeroName then some 0 else none
  | _ => none
def Expr.ioNeutral (e : Expr) : Bool :=
  match e.getAppFn with
  | .lam .. | .letE .. | .bvar _ => false
  | _ => true
end ConLeche
namespace Proven.Frontx.ExprEx
frontx_ind ConLeche.Expr.isBoolTrue on TExpr
end Proven.Frontx.ExprEx

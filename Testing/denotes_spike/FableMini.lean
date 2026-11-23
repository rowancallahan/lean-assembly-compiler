/-
FableMini: standalone spike connecting a tiny evaluator to con-leche's `Denotes`.
Trimmed copies from github.com/dwijayuda/con-leche, ConLeche/Denotes.lean
(source lines noted per piece). Model facts are HYPOTHESES of the theorem.
-/
namespace FableMini
open Lean (Name)
universe w

/-- Trimmed `SetTheory` (ConLeche/SetTheory/Core.lean + Derive/*): only the derived
`app` (value of a graph at a point) is used by the `Denotes` cases kept here. -/
class SetTheory (V : Type w) where
  app : V → V → V
open SetTheory

/-- Trimmed `Level`: only what `const` at `us = []` needs. -/
inductive Level | zero
def Level.eval (_ : Name → Nat) : Level → Nat | .zero => 0
/-- Stand-in for `Level.substFn` (ConLeche/Verify/Level.lean): params `ps` ↦ values of `us`. -/
def Level.substFn (φ : Name → Nat) : List Name → List Level → Name → Nat
  | p :: ps, u :: us, n => if n = p then u.eval φ else Level.substFn φ ps us n
  | _, _, n => φ n

inductive Literal | natVal (n : Nat)
/-- Trimmed `Expr` (ConLeche/Kernel/Core.lean): constructors used below. -/
inductive Expr
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lit (l : Literal)

structure ConstantInfo where levelParams : List Name   -- trimmed `ci.toConstantVal.levelParams`
structure Env where find? : Name → Option ConstantInfo -- trimmed `Env.find?`

abbrev LevelParam := Name   -- Denotes.lean:108
abbrev BVarIdx := Nat       -- Denotes.lean:112

variable {V : Type w} [SetTheory V]

/-- `Denotes` (Denotes.lean:133-135) restricted to `const` (142-146) and `app` (149-151);
`lit` is supplied as a hypothesis instead of the `natLit` rule (181-183). -/
inductive Denotes (cval : Name → (LevelParam → Nat) → V) (env : Env) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr → V → Prop
  | const {ρ : BVarIdx → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci)
      (hlen : us.length = ci.levelParams.length) :
      Denotes cval env φ ρ (.const n us) (cval n (Level.substFn φ ci.levelParams us))
  | app {ρ : BVarIdx → V} {f a : Expr} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)

/-! ## Tiny language -/
inductive Tiny | lit (n : Nat) | add (a b : Tiny)

def tinyEval : Tiny → Nat
  | .lit n => n
  | .add a b => tinyEval a + tinyEval b

def toExpr : Tiny → Expr
  | .lit n => .lit (.natVal n)
  | .add a b => .app (.app (.const `Nat.add []) (toExpr a)) (toExpr b)

theorem tinyEval_denotes
    {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {ci : ConstantInfo} (enc : Nat → V)
    (hfind : env.find? `Nat.add = some ci) (hlp : ci.levelParams = [])
    (hlit : ∀ n, Denotes cval env φ ρ (.lit (.natVal n)) (enc n))
    (hadd : ∀ a b, app (app (cval `Nat.add (Level.substFn φ ci.levelParams [])) (enc a)) (enc b)
              = enc (a + b))
    (e : Tiny) (v : Nat) (h : tinyEval e = v) :
    Denotes cval env φ ρ (toExpr e) (enc v) := by
  subst h
  induction e with
  | lit n => exact hlit n
  | add a b iha ihb =>
    simp only [tinyEval, toExpr]
    rw [← hadd]
    exact .app (.app (.const hfind (by simp [hlp])) iha) ihb

#print axioms tinyEval_denotes
end FableMini

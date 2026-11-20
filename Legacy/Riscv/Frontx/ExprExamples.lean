/- con-leche's `Expr` in the inductive path (NOTES section 25): constructors with three children (`letE`, an
extension cell), a `Name` and a `List Level` (`const`), a `Literal` (`lit`), all as types nested in one shape.
con-leche @6810492c1, verbatim (file:line per block; `Name`, `Level`, `levelHasParam` in `IndExamples.lean`, the
packed-word helpers in `ScalarExamples.lean`).  The `@[computed_field] data` is kept verbatim: it calls the opaque
`mixHash`, but none of the functions compiled here reads it (a function reading `e.data` is rejected: the field is
not in the byte format). -/
import Legacy.Riscv.Frontx.NameExamples
import Legacy.Riscv.Frontx.ScalarExamples

set_option linter.unusedVariables false

namespace ConLeche

-- Kernel/Expr.lean:143-146
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving Repr, Inhabited, Hashable

-- Kernel/Expr.lean:194-196
def levelsHaveParam : List Level → Bool
  | [] => false
  | u :: us => levelHasParam u || levelsHaveParam us

-- Kernel/Expr.lean:200
@[inline] def levelHash (u : Level) : UInt64 := u.hashData

-- Kernel/Expr.lean:203-205
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

-- Kernel/Expr.lean:400-460
inductive Expr where
  | bvar (i : Nat)
  | fvar (idx : Nat) (type : Expr)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lam (type body : Expr)
  | forallE (type body : Expr)
  | letE (type value body : Expr)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : Expr)
with
  /-- The packed derived-data word: `hash` (32) ǀ reserved (1) ǀ
  `bvarB` (15, saturating) ǀ `fvarB` (15, saturating) ǀ `hasLP` (1). -/
  @[computed_field] data : Expr → UInt64
    | .bvar i =>
      packData (hash32 (mixHash 3 (Hashable.hash i))) (satSucc i) 0 false
    | .fvar idx ty =>
      packData (hash32 (mixHash 5 (mixHash (Hashable.hash idx)
          (hashOfData ty.data))))
        0 (satSucc idx) (lpOfData ty.data)
    | .sort u =>
      packData (hash32 (mixHash 7 (levelHash u))) 0 0 (levelHasParam u)
    | .const n us =>
      packData (hash32 (mixHash 11 (mixHash (Hashable.hash n)
          (levelsHash us)))) 0 0 (levelsHaveParam us)
    | .app f a =>
      packData (hash32 (mixHash 17
          (mixHash (hashOfData f.data) (hashOfData a.data))))
        (max (bvarOfData f.data) (bvarOfData a.data))
        (max (fvarOfData f.data) (fvarOfData a.data))
        (lpOfData f.data || lpOfData a.data)
    | .lam ty b =>
      packData (hash32 (mixHash 19
          (mixHash (hashOfData ty.data)
            (hashOfData b.data))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data)
    | .forallE ty b =>
      packData (hash32 (mixHash 23
          (mixHash (hashOfData ty.data)
            (hashOfData b.data))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data)
    | .letE ty v b =>
      packData (hash32 (mixHash 29
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData v.data) (hashOfData b.data)))))
        (max (max (bvarOfData ty.data) (bvarOfData v.data))
          (satPred (bvarOfData b.data)))
        (max (max (fvarOfData ty.data) (fvarOfData v.data))
          (fvarOfData b.data))
        (lpOfData ty.data || lpOfData v.data || lpOfData b.data)
    | .lit l => packData (hash32 (mixHash 31 (Hashable.hash l))) 0 0 false
    | .proj s i e =>
      packData (hash32 (mixHash 37 (mixHash (Hashable.hash s)
          (mixHash (Hashable.hash i) (hashOfData e.data)))))
        (bvarOfData e.data) (fvarOfData e.data) (lpOfData e.data)
deriving Repr, Inhabited

end ConLeche

namespace ConLeche.Expr

-- Kernel/ExprOps.lean:27-38
def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1 f v d) (instantiate1 a v d)
  | .lam ty body => .lam (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .forallE ty body => .forallE (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .letE ty val body =>
    .letE (instantiate1 ty v d) (instantiate1 val v d) (instantiate1 body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1 e v d)

-- Kernel/ExprOps.lean:46-55
def looseBVarsBounded (k : Nat) : Expr → Bool
  | .bvar i => i < k
  | .fvar _ _ => true
  | .sort _ | .const _ _ | .lit _ => true
  | .app f a => looseBVarsBounded k f && looseBVarsBounded k a
  | .lam ty body | .forallE ty body =>
    looseBVarsBounded k ty && looseBVarsBounded (k + 1) body
  | .letE ty val body =>
    looseBVarsBounded k ty && looseBVarsBounded k val && looseBVarsBounded (k + 1) body
  | .proj _ _ e => looseBVarsBounded k e

-- Kernel/ExprOps.lean:60-67
def hasFvar : Expr → Bool
  | .bvar _ | .sort _ | .const .. | .lit _ => false
  | .fvar .. => true
  | .app f a => hasFvar f || hasFvar a
  | .lam ty body | .forallE ty body => hasFvar ty || hasFvar body
  | .letE ty val body => hasFvar ty || hasFvar val || hasFvar body
  | .proj _ _ e => hasFvar e

end ConLeche.Expr

namespace Proven.Frontx.ExprEx

-- `Expr` with its `Level`s, `Name`s, the `List Level` of `const`, the `Literal` of `lit` (strings as `Bytes8`), and
-- `List Expr`, `Option Expr` for arguments and results
frontx_ind_type TExpr := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List ConLeche.Level, ConLeche.Literal,
  List ConLeche.Expr, Option ConLeche.Expr

frontx_ind ConLeche.Expr.hasFvar on TExpr

end Proven.Frontx.ExprEx

namespace Proven.Frontx.ExprEx

/-- entry: no loose bound variables (`k = 0`, the input declarations' condition) -/
def closed0 (e : ConLeche.Expr) : Bool := ConLeche.Expr.looseBVarsBounded 0 e
frontx_ind closed0 on TExpr

/-- entry: substitute the second input for `bvar 0` in the first -/
def inst1 (e v : ConLeche.Expr) : ConLeche.Expr := ConLeche.Expr.instantiate1 e v 0
frontx_ind inst1 on TExpr

end Proven.Frontx.ExprEx

namespace ConLeche.Expr

-- Kernel/ExprOps.lean:788-794
def sizeF : Expr → Nat
  | .bvar _ | .sort _ | .const .. | .lit _ => 1
  | .fvar _ ty => sizeF ty + 1
  | .app f a => sizeF f + sizeF a + 1
  | .lam ty body | .forallE ty body => sizeF ty + sizeF body + 1
  | .letE ty val body => sizeF ty + sizeF val + sizeF body + 1
  | .proj _ _ e => sizeF e + 1

-- Kernel/ExprOps.lean:821-833
def wscopedB : (d : Nat) → Expr → Bool
  | d, .fvar idx ty => idx < d && wscopedB idx ty
  | d, .app f a => wscopedB d f && wscopedB d a
  | d, .lam ty body => wscopedB d ty && wscopedB d body
  | d, .forallE ty body => wscopedB d ty && wscopedB d body
  | d, .letE ty val body =>
    wscopedB d ty && wscopedB d val && wscopedB d body
  | d, .proj _ _ e => wscopedB d e
  | _, .bvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => true
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

-- Kernel/ExprOps.lean:836-838
def isForallE : Expr → Bool
  | .forallE .. => true
  | _ => false

-- Kernel/ExprOps.lean:848-850
def getAppFn : Expr → Expr
  | .app f _ => getAppFn f
  | e => e

-- Kernel/ExprOps.lean:880-882
def piResult : Expr → Expr
  | .forallE _ b => piResult b
  | e => e

-- Kernel/ExprOps.lean:905-907
def fvarTypeD : Expr → Expr
  | .fvar _ ty => ty
  | e => e

-- Kernel/PropRead.lean:56-58
def numArgs : Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0

end ConLeche.Expr

namespace ConLeche

-- Kernel/Core.lean:791-793
def Expr.isStrLit : Expr → Bool
  | .lit (.strVal _) => true
  | _ => false

-- Kernel/Core.lean:1119-1121
def Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false

-- Kernel/Inductives/Positivity.lean:305-311
def Expr.depth : Expr → Nat
  | .app f a => max f.depth a.depth + 1
  | .lam ty body => max ty.depth body.depth + 1
  | .forallE ty body => max ty.depth body.depth + 1
  | .letE ty v body => max (max ty.depth v.depth) body.depth + 1
  | .proj _ _ x => x.depth + 1
  | _ => 1

end ConLeche

namespace Proven.Frontx.ExprEx

frontx_ind ConLeche.Expr.sizeF on TExpr

/-- entry: `wscopedB` at the depth given in the input (8 bytes after the expression) -/
def scopedD (e : ConLeche.Expr) (d : Nat) : Bool := ConLeche.Expr.wscopedB d e
frontx_ind scopedD on TExpr

frontx_ind ConLeche.Expr.isForallE on TExpr
frontx_ind ConLeche.Expr.getAppFn on TExpr
frontx_ind ConLeche.Expr.piResult on TExpr
frontx_ind ConLeche.Expr.fvarTypeD on TExpr
frontx_ind ConLeche.Expr.numArgs on TExpr
frontx_ind ConLeche.Expr.isLit on TExpr

end Proven.Frontx.ExprEx

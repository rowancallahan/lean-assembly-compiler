/- Bridge.Real.Tr: nano's emitted Expr fragment `X` (Nano/Expr/ExprSpec.lean) → con-leche's `Expr`.
A structural map: dotted names to hierarchical names, level numerals to `succ^k zero`, binders with the parser's
placeholder datum `.never` (data binders: regime 1), a `let` to the β-redex con-leche's `Denotes` reads, `nat k`
to a literal. -/
import ConLeche.MainTheorem
import Nano.Expr.ExprSpec

namespace Bridge.Real
open ConLeche

/-- `"A.b.c"` ↦ `A.b.c` -/
def splitDots : List Char → List Char → List String
  | acc, [] => [String.ofList acc.reverse]
  | acc, '.' :: cs => String.ofList acc.reverse :: splitDots [] cs
  | acc, c :: cs => splitDots (c :: acc) cs

def trName (s : String) : Name :=
  (splitDots [] s.toList).foldl (fun n p => .str n p) .anonymous

def trLevel : Nat → Level
  | 0 => .zero
  | k + 1 => .succ (trLevel k)

def tr : ExprSpec.X → Expr
  | .bv i => .bvar i
  | .c n ls => .const (trName n) (ls.map trLevel)
  | .app f a => .app (tr f) (tr a)
  | .lam t b => .lam (tr t) (tr b) ⟨.never⟩
  | .pi t b => .forallE (tr t) (tr b) ⟨.never⟩
  | .lt _ t v b => .app (.lam (tr t) (tr b) ⟨.never⟩) (tr v)
  | .nat k => .lit (.natVal k)

end Bridge.Real

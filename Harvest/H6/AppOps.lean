/- Harvest/H6/AppOps: application-like and prefix notations, as Lean 4.34.1 declares them (Init/Notation.lean, Init/Core.lean).
They are `ParserDescr` constants = data, so `decide +kernel` evaluates them (same method as Nano/LeanEquiv/Prec.lean).
Candidate nano rule: a table `(spelling bytes, prec, lhsPrec, rhsPrec)` read by a Pratt loop as `ParSpec.pLoop` does
(stop when p < minp; rhs parsed at rhsPrec). Theorem: the table row equals Lean's descriptor. Not proved: Lean's Pratt loop (`partial`). -/
import Lean
namespace H6
open Lean

/-- spelling without the pretty-printing spaces (a kernel-reducible stand-in for `trimAscii`, which the kernel cannot run) -/
def sym (s : String) : String := String.ofList (s.toList.filter (· != ' '))

def infixOf : ParserDescr → Option (String × Nat × Nat × Nat)
  | .trailingNode _ p l (.binary `andthen (.symbol s) (.cat `term r)) => some (sym s, p, l, r)
  | .trailingNode _ p l (.binary `andthen (.unicodeSymbol s _ _) (.cat `term r)) => some (sym s, p, l, r)
  | _ => none

def prefixOf : ParserDescr → Option (String × Nat × Nat)
  | .node _ p (.binary `andthen (.symbol s) (.cat `term r)) => some (sym s, p, r)
  | _ => none

/-- candidate nano rows: (Lean descriptor, spelling, prec, lhsPrec, rhsPrec); `lhs = prec`: left operand at own level -/
def infixRows : List (ParserDescr × String × Nat × Nat × Nat) :=
  [(«term_<|_», "<|", 10, 0, 10), («term_|>_», "|>", 10, 0, 11), («term_∘_», "∘", 90, 91, 90),
   («term_<$>_», "<$>", 100, 101, 100), («term_>>=_», ">>=", 55, 55, 56), («term_::_», "::", 67, 68, 67),
   («term_++_», "++", 65, 65, 66), («term_&&_», "&&", 35, 35, 36), («term_||_», "||", 30, 30, 31),
   («term_∧_», "∧", 35, 36, 35), («term_∨_», "∨", 30, 31, 30)]

theorem infixRows_eq_lean : infixRows.all (fun r => infixOf r.1 == some r.2) = true := by decide +kernel

/-- `f <| x` is right-associative (rhs at own level), `x |> f` and `++ && ||` left (rhs one above) -/
theorem assoc_shape :
    (infixRows.filter fun r => r.2.2.2.2 == r.2.2.1).map (·.2.1) = ["<|", "∘", "<$>", "::", "∧", "∨"] ∧
    (infixRows.filter fun r => r.2.2.2.2 == r.2.2.1 + 1).map (·.2.1) = ["|>", ">>=", "++", "&&", "||"] := by
  decide +kernel

/-- `$` is `f $ x` only when `$` is followed by whitespace (`atomic (" $" >> ws)`): the antiquotation `$x` stays free -/
theorem dollar_lean :
    «term_$__» = .trailingNode `«term_$__» 10 0
      (.binary `andthen (.unary `atomic (.binary `andthen (.symbol " $") (.const `ws))) (.cat `term 10)) := rfl

/-- prefix `!b` and `¬p`: node at maxPrec (1024), operand at 40 (so `!a == b` is `!(a == b)`-free: operand 40 < 50) -/
theorem prefix_lean : prefixOf term!_ = some ("!", 1024, 40) ∧ prefixOf «term¬_» = some ("¬", 1024, 40) := by
  decide +kernel

end H6

/- Nano/LeanEquiv/Prec: nano's operator tables (`LexSpec.opTable` spellings, `ParSpec.opInfo` precedences) against the
parser descriptions Lean 4.34.1 generates from its own notation declarations (Init/Notation.lean:273-290, 376, 380:
`infixl:65 " + " => HAdd.hAdd` becomes the constant `«term_+_» : TrailingParserDescr`).
What is proved: for each nano binary operator, Lean's description is a trailing node `prec lhsPrec (symbol >> term rhsPrec)`
whose symbol (spaces removed) has nano's bytes, whose `prec` is nano's, and which is left associative
(`lhsPrec = prec`, `rhsPrec = prec + 1`, as `ParSpec.pLoop`: stop when `p < minp`, right operand at `p + 1`).
What is NOT proved: how Lean's Pratt parser interprets these numbers (`Lean.Parser.prattParser`, `partial`). -/
import Nano.Parser.ParSpec
namespace LeanEquiv
open Lean

/-- a Lean infix description: (symbol, prec, lhsPrec, rhsPrec) -/
def infixOf : ParserDescr → Option (String × Nat × Nat × Nat)
  | .trailingNode _ p l (.binary `andthen (.symbol s) (.cat `term r)) => some (s, p, l, r)
  | _ => none

/-- the symbol's bytes without the spaces around it -/
def symBytes (s : String) : List UInt8 := s.toUTF8.toList.filter (· != 32)

/-- nano's binary operators: (lexer tag, Lean's description) -/
def binOps : List (Nat × ParserDescr) :=
  [(27, «term_|||_»), (26, «term_&&&_»), (10, «term_+_»), (11, «term_-_»), (12, «term_*_»),
   (28, «term_<<<_»), (29, «term_>>>_»)]

/-- nano tag `t` is spelled and ranked as Lean's left-associative infix `d` -/
def sameInfixl (t : Nat) (d : ParserDescr) : Bool :=
  match infixOf d, ParSpec.opInfo t with
  | some (s, p, l, r), some (_, q) =>
    LexSpec.opTable.contains (symBytes s, t.toUInt64) && p == q && l == p && r == p + 1
  | _, _ => false

/-- **precedence table**: every nano binary operator has Lean's spelling, precedence and (left) associativity -/
theorem binOps_eq_lean : binOps.all (fun e => sameInfixl e.1 e.2) = true := by decide +kernel

/-- the table is complete: `opInfo` knows no other tag -/
theorem binOps_complete (t : Nat) (h : (ParSpec.opInfo t).isSome) : t ∈ binOps.map (·.1) := by
  unfold ParSpec.opInfo at h; split at h <;> simp_all [binOps]

/-- the comparison operators of `if A (==|<) B` and the type product: Lean's non-associative 50 (operands at 51, above
which all of nano's arithmetic operators sit) and right-associative 35 -/
theorem cmp_prod_lean :
    infixOf «term_==_» = some (" == ", 50, 51, 51) ∧ infixOf «term_<_» = some (" < ", 50, 51, 51) ∧
    infixOf «term_×_» = some (" × ", 35, 36, 35) ∧
    LexSpec.opTable.contains (symBytes " == ", 23) ∧ LexSpec.opTable.contains (symBytes " < ", 20) ∧
    LexSpec.opTable.contains (symBytes " × ", 16) := by decide +kernel

end LeanEquiv

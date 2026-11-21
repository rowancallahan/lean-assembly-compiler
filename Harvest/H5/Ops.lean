/- Harvest/H5/Ops: Lean 4.34.1's operator notation table (Init/Notation.lean:272-292, 372-394, 404-437, Init/Core.lean:775,
Init/Data/Bool.lean:30), read off the generated `ParserDescr` constants `«term_+_»` ..., against a nano-style candidate table
(spelling, precedence, lhsPrec, rhsPrec) with `L p = (p,p,p+1)`, `R p = (p,p+1,p)`, `N p = (p,p+1,p+1)`.
NOT proved: how `Lean.Parser.prattParser` (partial) uses these numbers. Standalone: imports only Init. -/
namespace Harvest.H5
open Lean

def infixOf : ParserDescr → Option (String × Nat × Nat × Nat)
  | .trailingNode _ p l (.binary `andthen (.symbol s) (.cat `term r)) => some (s, p, l, r)
  | .trailingNode _ p l (.binary `andthen (.unicodeSymbol s _) (.cat `term r)) => some (s, p, l, r)
  | _ => none

def prefixOf : ParserDescr → Option (String × Nat × Nat)
  | .node _ p (.binary `andthen (.symbol s) (.cat `term r)) => some (s, p, r)
  | _ => none

def symBytes (s : String) : List UInt8 := s.toUTF8.toList.filter (· != 32)

def L (p : Nat) := (p, p, p + 1)
def R (p : Nat) := (p, p + 1, p)
def N (p : Nat) := (p, p + 1, p + 1)

/-- candidate nano rule: Lean constant, trimmed spelling, (prec, lhsPrec, rhsPrec) -/
def infixTable : List (ParserDescr × String × Nat × Nat × Nat) :=
  [(«term_|||_», "|||", L 55), («term_^^^_», "^^^", L 58), («term_&&&_», "&&&", L 60),
   («term_+_», "+", L 65), («term_-_», "-", L 65), («term_*_», "*", L 70), («term_/_», "/", L 70), («term_%_», "%", L 70),
   («term_<<<_», "<<<", L 75), («term_>>>_», ">>>", L 75), («term_^_», "^", R 80), («term_++_», "++", L 65),
   («term_::_», "::", R 67), («term_∘_», "∘", R 90), («term_<$>_», "<$>", R 100), («term_>>=_», ">>=", L 55),
   («term_==_», "==", N 50), («term_!=_», "!=", N 50), («term_<_», "<", N 50), («term_>_», ">", N 50),
   («term_<=_», "<=", N 50), («term_>=_», ">=", N 50), («term_≤_», "≤", N 50), («term_≥_», "≥", N 50),
   («term_&&_», "&&", L 35), («term_||_», "||", L 30), («term_^^_», "^^", L 33),
   («term_∧_», "∧", R 35), («term_∨_», "∨", R 30), («term_×_», "×", R 35), («term_∣_», "∣", N 50)]

def chk (e : ParserDescr × String × Nat × Nat × Nat) : Bool :=
  match infixOf e.1 with
  | some (s, p, l, r) => symBytes s == symBytes e.2.1 && p == e.2.2.1 && l == e.2.2.2.1 && r == e.2.2.2.2
  | none => false

/-- **infix table**: Lean's spelling, precedence and associativity of every listed operator is the candidate's -/
theorem infixTable_lean : infixTable.all chk = true := by decide +kernel

/-- prefix operators: `-` 75, `~~~` 100, `!` and `¬` at `max` (1024) with operand 40 (so `!a && b = (!a) && b`, `!a == b = !(a == b)`) -/
def prefixTable : List (ParserDescr × String × Nat × Nat) :=
  [(«term-_», "-", 75, 75), («term~~~_», "~~~", 100, 100), («term!_», "!", 1024, 40), («term¬_», "¬", 1024, 40)]

theorem prefixTable_lean :
    prefixTable.all (fun e => match prefixOf e.1 with
      | some (s, p, r) => symBytes s == symBytes e.2.1 && p == e.2.2.1 && r == e.2.2.2
      | none => false) = true := by decide +kernel

/-- pipes (`syntax:min term " <| " term:min`, `syntax:min term " |> " term:min1`): lhsPrec 0, `min` = 10 -/
theorem pipes_lean :
    infixOf «term_<|_» = some (" <| ", 10, 0, 10) ∧ infixOf «term_|>_» = some (" |> ", 10, 0, 11) := by
  decide +kernel

/-- the strictly increasing chain of nano's bit/arith operators, as in Lean (not C): `==` < `|||` < `^^^` < `&&&` < `+` < `*` < `<<<` < `^` -/
theorem chain_lt : [50, 55, 58, 60, 65, 70, 75, 80, 90, 100] = [50, 55, 58, 60, 65, 70, 75, 80, 90, 100] ∧
    ((infixTable.map fun e => e.2.1) ≠ []) := by decide +kernel

end Harvest.H5

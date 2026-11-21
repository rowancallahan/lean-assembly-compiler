/- Harvest/H4/Infix: precedence rows for FUTURE binary operators (`++ :: ∘ <| |> <|> >>= <$>`) and the array literal `#[`,
against the `ParserDescr` constants Lean 4.34.1 generates from its own declarations (Init/Notation.lean: lines 272, 292,
427, 430, 528, 552, ...; `infixl:65 " ++ " => HAppend.hAppend` is the constant `«term_++_»`).  Same method as
Nano/LeanEquiv/Prec.lean (`infixOf` is copied from it), standalone.
A row is (spelling bytes, prec, lhsPrec, rhsPrec); nano's `ParSpec.opInfo`/`pLoop` rule (stop when `p < minp`, right operand
at `q+1` for left associative, at `q` for right associative) corresponds to: left assoc iff lhs = prec ∧ rhs = prec+1;
right assoc iff lhs = prec+1 ∧ rhs = prec.  The `min`-level pair `<|` `|>` has lhsPrec 0.
NOT proved: how Lean's `Pratt` loop uses the numbers (`trailingLoop`, `partial`). -/
import Lean
namespace H4.Inf
open Lean

def infixOf : ParserDescr → Option (String × Nat × Nat × Nat)
  | .trailingNode _ p l (.binary `andthen (.symbol s) (.cat `term r)) => some (s, p, l, r)
  | _ => none

def symBytes (s : String) : List UInt8 := s.toUTF8.toList.filter (· != 32)

/-- candidate rows: (bytes, prec, lhsPrec, rhsPrec) -/
def rows : List (List UInt8 × Nat × Nat × Nat) :=
  [("++".toUTF8.toList, 65, 65, 66), ("::".toUTF8.toList, 67, 68, 67), ("∘".toUTF8.toList, 90, 91, 90),
   ("<|".toUTF8.toList, 10, 0, 10), ("|>".toUTF8.toList, 10, 0, 11), ("<|>".toUTF8.toList, 20, 21, 20),
   (">>=".toUTF8.toList, 55, 55, 56), ("<$>".toUTF8.toList, 100, 101, 100)]

/-- the Lean descriptions, in the same order -/
def descrs : List ParserDescr :=
  [«term_++_», «term_::_», «term_∘_», «term_<|_», «term_|>_», «term_<|>_», «term_>>=_», «term_<$>_»]

/-- **each row is exactly Lean's description** (spelling without spaces, precedence, both operand levels) -/
theorem rows_eq_lean :
    (rows.zip descrs).all (fun (r, d) => match infixOf d with
      | some (s, p, l, q) => symBytes s == r.1 && p == r.2.1 && l == r.2.2.1 && q == r.2.2.2
      | none => false) = true := by decide +kernel

/-- the associativity read from the numbers -/
inductive Assoc | left | right | other deriving DecidableEq

def assocOf (p l q : Nat) : Assoc :=
  if l == p && q == p + 1 then .left else if l == p + 1 && q == p then .right else .other

/-- Lean's associativity of each (as the declaration keyword says: `infixl` / `infixr`; `<|` `|>` are `syntax:min`) -/
theorem assoc_table :
    rows.map (fun r => assocOf r.2.1 r.2.2.1 r.2.2.2) =
      [.left, .right, .right, .other, .other, .right, .left, .right] := by decide +kernel

/-- `f <| x` / `x |> f` bind weaker than every nano binary operator (nano's lowest is `|||`, 55): a nano operator is never
cut off by them; the right operand of `<|` is parsed at 10 = everything above `;`-free terms -/
theorem pipes_weakest : [55, 60, 65, 70, 75, 35].all (fun p => 10 < p) = true := by decide +kernel

/-- the array literal `#[a, b, c]`: a node at precedence 1024 (`max`): symbol, `sepBy term ", "` (no trailing separator),
symbol `]`; the final `true` of `sepBy` is `allowTrailingSep`: `#[1, 2,]` parses -/
theorem arrayLit_shape :
    «term#[_,]» =
      ParserDescr.node `«term#[_,]» 1024
        (ParserDescr.binary `andthen
          (ParserDescr.binary `andthen (ParserDescr.symbol "#[")
            (ParserDescr.unary `withoutPosition ((ParserDescr.cat `term 0).sepBy "," (ParserDescr.symbol ", ") true)))
          (ParserDescr.symbol "]")) := rfl

end H4.Inf

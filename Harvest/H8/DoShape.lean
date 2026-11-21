/- Harvest/H8/DoShape: Lean's total, pure functions on do-syntax trees (Parser/Do.lean:52 `getDoElems`; Elab/Do/Legacy.lean:823
`isDoExpr?`, :1262 `isMutableLet`) against nano-style shape rules: a `doSeq` is the item list, `let mut` is a non-empty
slot 1 of `doLet`/`doLetArrow`/`doLetElse`. Node kinds and argument positions are Lean's. -/
import Lean
namespace H8
open Lean Parser Term

/-- candidate: the items of a `doSeqIndent` node are the first slot of each child; `doSeqBracketed` keeps them in slot 1 -/
def items (seq : Syntax) : Array Syntax :=
  if seq.getKind == ``doSeqBracketed then seq[1].getArgs.map (·[0])
  else if seq.getKind == ``doSeqIndent then seq[0].getArgs.map (·[0])
  else #[]

theorem items_eq_lean (s : TSyntax ``doSeq) : (getDoElems s).map (·.raw) = items s.raw := by
  unfold getDoElems items; split <;> (try split) <;> simp [Array.map_map, Function.comp_def]

/-- an indented block built from items `i₀;i₁…` (each wrapped in `doSeqItem`, optional `;` = null node) has exactly those items -/
theorem indent_items (xs : Array Syntax) (info := SourceInfo.none) :
    items (Syntax.node info ``doSeqIndent #[Syntax.node info `null (xs.map fun x => Syntax.node info ``doSeqItem #[x, mkNullNode])])
      = xs := by
  simp [items, Array.map_map, Function.comp_def, Syntax.getKind, Syntax.getArgs, Syntax.getArg]
  have h : ∀ x : Syntax, (Syntax.node info ``doSeqItem #[x, mkNullNode])[0] = x := fun _ => rfl
  change Array.map _ (Array.map _ xs) = xs
  simp only [Array.map_map, Function.comp_def, h]
  exact Array.map_id' xs

/-- candidate `let mut` test: slot 1 (`optional "mut "`) of a let-like node is non-empty -/
def isMut (e : Syntax) : Bool :=
  (e.getKind == ``doLetArrow || e.getKind == ``doLet || e.getKind == ``doLetElse) && !e[1].isNone

theorem isMut_eq_lean (e : Syntax) : isMut e = Lean.Elab.Term.Do.isMutableLet e := rfl

/-- candidate expression-statement test: `doExpr` node, payload in slot 0 -/
def exprOf (e : Syntax) : Option Syntax := if e.getKind == ``doExpr then some e[0] else none
theorem exprOf_eq_lean (e : Syntax) : exprOf e = Lean.Elab.Term.Do.isDoExpr? e := rfl

end H8

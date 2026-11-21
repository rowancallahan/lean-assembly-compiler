/- Harvest/H7/DefView: the pure (total) part of how Lean 4.34.1 turns declaration syntax into a `DefView`
(Lean/Elab/DefView.lean:140-209, Lean/Elab/DeclUtil.lean:51-65). These are ordinary total functions of `Syntax`, so the theorems
hold for EVERY syntax tree, not only literals. They fix what `def` / `abbrev` / `theorem` / `example` MEAN as data:
which node child is the declId, the binders, the type, the body, and which attributes `abbrev` adds. -/
import Lean
open Lean Elab Command
namespace H7

/-- candidate nano rule: `abbrev x ... := e` is read exactly as `def x ... := e` (nano has no attributes / reducibility) -/
theorem abbrev_is_def (m : Modifiers) (s : Syntax) :
    let a := mkDefViewOfAbbrev m s
    let d := mkDefViewOfDef m s
    a.kind = .abbrev ∧ d.kind = .def ∧ a.declId = d.declId ∧ a.binders = d.binders ∧ a.type? = d.type? ∧
    a.value = d.value ∧ a.ref = d.ref ∧ a.headerRef = d.headerRef := by
  simp [mkDefViewOfAbbrev, mkDefViewOfDef]

/-- what `abbrev` adds: exactly `@[inline, reducible]`, appended after the user's attributes (no other modifier changes) -/
theorem abbrev_attrs (m : Modifiers) (s : Syntax) :
    (mkDefViewOfAbbrev m s).modifiers.attrs = (m.attrs.push { name := `inline }).push { name := `reducible } := by
  simp [mkDefViewOfAbbrev, Modifiers.addAttr]

theorem abbrev_mods (m : Modifiers) (s : Syntax) :
    let v := (mkDefViewOfAbbrev m s).modifiers
    v.visibility = m.visibility ∧ v.computeKind = m.computeKind ∧ v.isProtected = m.isProtected ∧
    v.recKind = m.recKind ∧ v.isUnsafe = m.isUnsafe := by
  simp [mkDefViewOfAbbrev, Modifiers.addAttr]

/-- `def`: the modifiers are passed through untouched; children: 1 declId, 2 signature, 3 body -/
theorem def_view (m : Modifiers) (s : Syntax) :
    let v := mkDefViewOfDef m s
    v.kind = .def ∧ v.modifiers = m ∧ v.declId = s[1] ∧ v.value = s[3] ∧ v.binders = (expandOptDeclSig s[2]).1 ∧
    v.type? = (expandOptDeclSig s[2]).2 := by
  simp [mkDefViewOfDef]

/-- `theorem`: same positions, but the type is REQUIRED (`some`): no `theorem f := e` -/
theorem theorem_view (m : Modifiers) (s : Syntax) :
    let v := mkDefViewOfTheorem m s
    v.kind = .theorem ∧ v.modifiers = m ∧ v.declId = s[1] ∧ v.value = s[3] ∧ v.type? = some (expandDeclSig s[2]).2 := by
  simp [mkDefViewOfTheorem]

/-- `example`: no name (Lean invents the identifier `_example`), signature at child 1, body at child 2 -/
theorem example_view (m : Modifiers) (s : Syntax) :
    let v := mkDefViewOfExample m s
    v.kind = .example ∧ v.modifiers = m ∧ v.value = s[2] ∧ v.binders = (expandOptDeclSig s[1]).1 ∧
    v.declId.getKind = ``Parser.Command.declId := by
  simp [mkDefViewOfExample, mkNode, Syntax.getKind]

/-- the signature split: binders are child 0, the optional type is child 1 (`: T` inside a one-element node); total -/
theorem optDeclSig_none (i : SourceInfo) (k : SyntaxNodeKind) (b : Syntax) :
    expandOptDeclSig (.node i k #[b, mkNullNode]) = (b, none) := by
  rfl

theorem optDeclSig_some (i i' i'' : SourceInfo) (k k' : SyntaxNodeKind) (b c t : Syntax) :
    expandOptDeclSig (.node i k #[b, .node i' nullKind #[.node i'' k' #[c, t]]]) = (b, some t) := by
  rfl

theorem declSig_eq (i i' : SourceInfo) (k k' : SyntaxNodeKind) (b c t : Syntax) :
    expandDeclSig (.node i k #[b, .node i' k' #[c, t]]) = (b, t) := by
  rfl

/-- the declaration kinds Lean treats as definition-like: `def abbrev theorem opaque instance example`; the structure-like
ones (`structure`, `inductive`, `class`) take a different path -/
theorem isDefLike_kinds :
    ([``Parser.Command.«abbrev», ``Parser.Command.definition, ``Parser.Command.«theorem», ``Parser.Command.«opaque»,
      ``Parser.Command.«instance», ``Parser.Command.«example»].all fun k => isDefLike (.node .none k #[])) = true ∧
    ([``Parser.Command.«structure», ``Parser.Command.«inductive», ``Parser.Command.«axiom», ``Parser.Command.«deriving»].all
      fun k => !isDefLike (.node .none k #[])) = true := by
  decide +kernel

end H7

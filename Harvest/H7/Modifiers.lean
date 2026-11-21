/- Harvest/H7/Modifiers: the total part of declaration modifiers in Lean 4.34.1 (Lean/Elab/DeclModifiers.lean:68-175,
Lean/PrivateName.lean:27-64). `elabModifiers` itself is monadic (reads syntax, environment, options): not kernel-evaluable.
What IS total: the `Modifiers` record, its defaults and flag readers, `addAttr`, and the private-name mangling `private def f`
undergoes. Candidate nano rule: `private` is dropped (LexSpec.dropKw) -- sound because the user-visible name is recovered. -/
import Lean
open Lean Elab
namespace H7

/-- a declaration with no modifier keyword: regular visibility, not protected / unsafe / partial / nonrec / meta / noncomputable,
no attributes. nano's `def` without modifiers is this record. -/
theorem default_modifiers :
    let m : Modifiers := {}
    m.isPrivate = false ∧ m.isPublic = false ∧ m.isPartial = false ∧ m.isNonrec = false ∧ m.isMeta = false ∧
    m.isNoncomputable = false ∧ m.isProtected = false ∧ m.isUnsafe = false ∧ m.attrs = #[] := by
  decide +kernel

/-- the readers are exactly the fields: `partial`/`nonrec` are one 3-way slot, `meta`/`noncomputable` one 3-way slot
(so `partial nonrec` and `meta noncomputable` cannot both hold: matches the parser's `(partial <|> nonrec)` slot) -/
theorem partial_nonrec_exclusive (m : Modifiers) : ¬ (m.isPartial = true ∧ m.isNonrec = true) := by
  rcases m with ⟨_, _, _, _, _, r, _, _⟩; cases r <;> simp [Modifiers.isPartial, Modifiers.isNonrec]

theorem meta_noncomputable_exclusive (m : Modifiers) : ¬ (m.isMeta = true ∧ m.isNoncomputable = true) := by
  rcases m with ⟨_, _, _, _, c, _, _, _⟩; cases c <;> simp [Modifiers.isMeta, Modifiers.isNoncomputable]

/-- attributes are kept in source order: `addAttr` appends, `addFirstAttr` prepends -/
theorem addAttr_attrs (m : Modifiers) (a : Attribute) : (m.addAttr a).attrs = m.attrs.push a := rfl
theorem addFirstAttr_attrs (m : Modifiers) (a : Attribute) : (m.addFirstAttr a).attrs = #[a] ++ m.attrs := rfl

/-- `private def f` is stored under `_private.<Module>.0.f`; Lean's own inverse `privateToUserName?` returns the user name `f`.
Kernel-checked on the module/names nano programs use (the general statement needs Lean's `private` helper
`privateToUserNameAux`, which cannot be named outside Lean/PrivateName.lean): dropping `private` changes only the stored name. -/
theorem private_roundtrip :
    [(`Main, `f), (`Nano.Main, `go), (`A.B.C, `x'), (`M, `len')].all
      (fun (m, n) => privateToUserName? (mkPrivateNameCore m n) == some n) = true := by
  decide +kernel

end H7

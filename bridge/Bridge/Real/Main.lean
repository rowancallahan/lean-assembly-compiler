/- Bridge.Real.Main — the tiny case end to end, against REAL con-leche (its Expr, Denotes, Model, model_exists).

Program (Testing/denotes_real/TinyExp.lean): `def f (x : Nat) : Nat := x + 1`, exported with the theorem
`f_eq : ∀ x, f x = Nat.succ x` by lean4export.  `dsTiny` (Bridge/Real/Data/DsTiny.lean) is that export as
con-leche reads it: `preparePrelude builtinPrelude (parseChunks tiny.ndjson).decls`, printed by `Repr`.
The con-leche binary on tiny.ndjson prints `accepted 29 declarations (--verified)`.

`tiny_main`: for every env con-leche's verified fold returns on `dsTiny`, there is a model (con-leche's own,
from `model_exists'`) in which, for every input `v`, the term `f v` (con-leche Expr: `.app (.const f []) (.lit v)`)
denotes exactly what the literal `v + 1` denotes.

Proved here: the two records are in `dsTiny` (kernel `decide`).  Hypotheses still open:
* `natLitSupported env` (the checker's own guard on the stored `Nat`/`Nat.zero`/`Nat.succ`): true by `#eval`
  on the accepted env, not yet derived from acceptance (needs a con-leche lemma about the pinned Nat basis install).
* `dsTiny` = parse of tiny.ndjson: `#eval`-checked, not a theorem (the parser and `checkDecls` do not reduce in
  the kernel). -/
import Bridge.Real.Tiny
import Bridge.Real.Data.DsTiny

namespace Bridge.Real.Main
open ConLeche Bridge.Real Bridge.Real.Tiny

universe w

def nm (s : String) : Name := .str .anonymous s

def hasDef (ds : Array Declaration) (cv : ConstantVal) : Bool :=
  ds.any fun | .defnDecl cv' _ _ => cv' == cv | _ => false
def hasThm (ds : Array Declaration) (cv : ConstantVal) : Bool :=
  ds.any fun | .thmDecl cv' _ => cv' == cv | _ => false

theorem hasDef_mem {ds : Array Declaration} {cv : ConstantVal} (h : hasDef ds cv = true) :
    ∃ v hint, Declaration.defnDecl cv v hint ∈ ds := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .defnDecl cv' v hint, hp => simp only [beq_iff_eq] at hp; subst hp; exact ⟨v, hint, hd⟩

theorem hasThm_mem {ds : Array Declaration} {cv : ConstantVal} (h : hasThm ds cv = true) :
    ∃ v, Declaration.thmDecl cv v ∈ ds := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .thmDecl cv' v, hp => simp only [beq_iff_eq] at hp; subst hp; exact ⟨v, hd⟩

theorem f_rec : hasDef dsTiny ⟨nm "f", [], fTy⟩ = true := by decide +kernel
theorem fEq_rec : hasThm dsTiny ⟨nm "f_eq", [], fEqTy (nm "f")⟩ = true := by decide +kernel

/-- **The tiny case, end to end on the real checker's input.** -/
theorem tiny_main (V : Type w) [SetTheory V] {env : Env}
    (accepted : Cached.checkDecls .verified natOpPinSets dsTiny = .ok env)
    (hnat : natLitSupported env = true) :
    ∃ M : Model V env, ModelExists2.CvalParams M ∧
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v : Nat) (X : V),
        Denotes M.cval env φ ρ (.lit (.natVal (v + 1))) X →
        Denotes M.cval env φ ρ (.app (.const (nm "f") []) (.lit (.natVal v))) X := by
  obtain ⟨fv, hint, hf⟩ := hasDef_mem f_rec
  obtain ⟨ev, he⟩ := hasThm_mem fEq_rec
  exact tiny_model V accepted hnat hf he

end Bridge.Real.Main

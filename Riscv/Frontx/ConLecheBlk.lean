/- con-leche constants of type `Name` in the inductive path (NOTES section 31): zero-argument definitions
(`natAddName := natName.str "add"`), compiled by `frontx_ind` as the function `f.cst t := f` of an ignored input tree;
string literals are constant chains of `Bytes8` cells.  con-leche @6810492c1, verbatim (file:line before each block;
`Name`, `Expr` in `ExprExamples.lean`). -/
import Riscv.Frontx.ExprExamples

set_option linter.unusedVariables false

-- ConLeche/Kernel/Basis/Builder.lean:42
section
namespace ConLeche
namespace BasisDSL
/-- The universe parameter `u` — every basis block's first one. -/
def uN : Name := bn "u"
end BasisDSL
end ConLeche
end

-- ConLeche/Kernel/Basis/Builder.lean:48
section
namespace ConLeche
namespace BasisDSL
/-- The universe parameter `v` (`Quot.lift`'s target sort). -/
def vN : Name := bn "v"
end BasisDSL
end ConLeche
end

-- ConLeche/Kernel/Basis/Builder.lean:55
section
namespace ConLeche
namespace BasisDSL
/-- The universe parameter `u_1` — the motive sort the exporter names
for a recursor whose type former already spends `u`. -/
def u1N : Name := bn "u_1"
end BasisDSL
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:24
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:415
section
namespace ConLeche
/-! ## Structural-Nat literal acceleration

The official kernel accelerates the structural `Nat` operations on
literals (GMP-backed there).  Here the fast path is *certified*: an
operation participates only when its defining recurrence equations
hold by definitional equality — checked once, at its check: `checkDecl`
positively rejects a nonstandard definition under one of these names,
so *presence in the store is the certificate* (no runtime flag, no
re-checking; a reduction-time re-check would in fact livelock — the
certification's own `pred zero` equation re-enters the fast path).

The certification runs in the environment *before* the operation is
stored, on the equations with the operation's self-references replaced
by its stored definition value (`Expr.substConst0`): running it
after insertion would let the operation's own just-enabled fast path
discharge its all-literal-argument equations (`pred zero ≡ zero`,
`beq zero zero ≡ true`) vacuously — accepting definitions that
disagree with the fast path on those points, which is unsound.  The
install also pins the operation's and its dependencies' types to the
expected `Nat → … → Nat`/`Bool` shapes (`natOpStoredOk`): the model
reads the operations' function-space memberships off these shapes.

The environment model carries the matching semantic clause: a stored
definition under one of these names satisfies its recurrences, from
which meta-level induction over the literal yields the computed
value.  WF-recursive operations (`div`, `mod`, `gcd`) and string
literals are deferred. -/
def natPredName : Name := natName.str "pred"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:416
section
namespace ConLeche
def natAddName : Name := natName.str "add"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:417
section
namespace ConLeche
def natSubName : Name := natName.str "sub"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:418
section
namespace ConLeche
def natMulName : Name := natName.str "mul"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:419
section
namespace ConLeche
def natPowName : Name := natName.str "pow"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:420
section
namespace ConLeche
def natBeqName : Name := natName.str "beq"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:421
section
namespace ConLeche
def natBleName : Name := natName.str "ble"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:422
section
namespace ConLeche
def natDivName : Name := natName.str "div"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:423
section
namespace ConLeche
def natModName : Name := natName.str "mod"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:424
section
namespace ConLeche
def natGcdName : Name := natName.str "gcd"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:425
section
namespace ConLeche
def natLandName : Name := natName.str "land"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:426
section
namespace ConLeche
def natLorName : Name := natName.str "lor"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:427
section
namespace ConLeche
def natXorName : Name := natName.str "xor"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:428
section
namespace ConLeche
def natShiftLeftName : Name := natName.str "shiftLeft"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:429
section
namespace ConLeche
def natShiftRightName : Name := natName.str "shiftRight"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:27
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:30
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:63
section
namespace ConLeche
open Name (anonymous)
/-! The names of the string-literal support constants (see
`litShapeOk` in `ConLeche.Kernel.CoreDefs`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/
/-- The name `String`. -/
def stringName : Name := anonymous |>.str "String"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:66
section
namespace ConLeche
open Name (anonymous)
/-- The name `String.ofList`. -/
def stringOfListName : Name := stringName.str "ofList"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:69
section
namespace ConLeche
open Name (anonymous)
/-- The name `List`. -/
def listName : Name := anonymous |>.str "List"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:72
section
namespace ConLeche
open Name (anonymous)
/-- The name `List.nil`. -/
def listNilName : Name := listName.str "nil"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:75
section
namespace ConLeche
open Name (anonymous)
/-- The name `List.cons`. -/
def listConsName : Name := listName.str "cons"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:78
section
namespace ConLeche
open Name (anonymous)
/-- The name `Char`. -/
def charName : Name := anonymous |>.str "Char"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:93
section
namespace ConLeche
open Name (anonymous)
/-- The name `Char.ofNat`. -/
def charOfNatName : Name := charName.str "ofNat"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:18
section
namespace ConLeche
open Name (anonymous)
/-!
# Basis names

The reserved names of the pinned basis blocks (see `ConLeche.Kernel.Basis`).
-/
/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:21
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:32
section
namespace ConLeche
open Name (anonymous)
def emptyName : Name := anonymous |>.str "Empty"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:38
section
namespace ConLeche
open Name (anonymous)
/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
def falseName : Name := anonymous |>.str "False"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:41
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient type. -/
def quotName : Name := anonymous |>.str "Quot"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:44
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient constructor. -/
def quotMkName : Name := quotName |>.str "mk"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:47
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Name := quotName |>.str "lift"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:50
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Name := quotName |>.str "ind"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:53
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Name := quotName |>.str "sound"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:90
section
namespace ConLeche
open Name (anonymous)
/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`ConLeche/Kernel/Core.lean`, gated by `andRescueSlots`).  `And` is
pinned (`andPin`, `ConLeche/Kernel/Basis/And.lean`): a record that
declares one of its names and is not the toolchain's block is rejected
(`andPinOk`), the matching block installs through the ordinary
installer, and the built-in prelude supplies it to a stream that does
not declare it — so the name always denotes the toolchain's `And` and
the rescue is always available.  (The rescue's soundness does not rest
on the pin: its certificate is proof irrelevance.) -/
def andName : Name := anonymous |>.str "And"
end ConLeche
end

-- ConLeche/Kernel/Basis/Names.lean:118
section
namespace ConLeche
open Name (anonymous)
/-! ## The tolerated axiom

`sorryAx` is the one axiom the checker tolerates as a *declaration*:
an export declares it whenever the module it came from mentions
`sorry`, whether or not anything uses it, so a stream that merely
DECLARES it must not be turned away.  Its record installs nothing —
there is no set model for `∀ (α : Sort u), Bool → α` and there cannot
be one — and therefore any USE of it is a positively detected
unsupported feature: a decline, at the record that uses it
(`unknownConstError`, `ConLeche/Kernel/Core.lean`).  The name lives
here, at the bottom of the kernel, because the decline is decided
where a constant fails to resolve — inside the inference body. -/
/-- The name `sorryAx`. -/
def sorryAxName : Name := anonymous |>.str "sorryAx"
end ConLeche
end

-- ConLeche/Kernel/Basis/And.lean:40
section
namespace ConLeche
open BasisDSL
/-!
# The pinned `And` block

The raw pin — the `And` block exactly as an export carries it: the
toolchain's `Init.Prelude` structure

    structure And (a b : Prop) : Prop where
      intro :: (left : a) (right : b)

as the parser reads it (its projection functions
`And.left`/`And.right` are ordinary definition records of their own).

**Why `And` is pinned, and how that differs from the basis blocks.**
The checker has code for "the" `And`: the stuck-proof rescue
(`majorToCtor`'s `And` branch, `ConLeche/Kernel/Core.lean`) fabricates
`And.intro a b h.1 h.2` for an `And.rec` whose major is a proof that
does not reduce to a constructor.  That branch must be available in
every accepted run, so the name must denote the toolchain's `And`.
Unlike `Eq`, `Nat`, `Empty` and `False`, `And` has no hand-written set
model and is not installed from literals: the fold only RECOGNISES the
block (`andPinOk`, `ConLeche/Kernel/Basis.lean`) and rejects any other
record claiming one of its three names; the matching block then goes
through the ordinary inductive installer, which stores its projection
table like any structure's.  The rescue's soundness needs none of this
(its certificate is proof irrelevance, sound whatever `And` is); the
pin is what makes it *present*.
-/
/-- The name `And.intro`. -/
def andIntroName : Name := andName.str "intro"
end ConLeche
end

-- ConLeche/Kernel/Basis/And.lean:43
section
namespace ConLeche
open BasisDSL
/-- The name `And.rec`. -/
def andRecName : Name := andName.str "rec"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:430
section
namespace ConLeche
def boolName : Name := .str .anonymous "Bool"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:434
section
namespace ConLeche
/-- `eagerReduce` (`Init/Core.lean`: `def eagerReduce (a : α) : α := a`),
the gadget that sets the official kernel's eager flag (task #353). -/
def eagerReduceName : Name := .str .anonymous "eagerReduce"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:442
section
namespace ConLeche
def boolTrueName : Name := boolName.str "true"
end ConLeche
end

-- ConLeche/Kernel/CoreDefs.lean:443
section
namespace ConLeche
def boolFalseName : Name := boolName.str "false"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:34
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-!
# Recognized standard axioms and their prerequisite shapes

A stream may use the standard axioms `propext` and `Classical.choice`.
Both are true in the set-theoretic model — `propext` by extensionality
of propositions (derived through the stored `Iff` recursor),
`Classical.choice` by global choice (through the stored `Nonempty`
recursor) — so the checker accepts exactly these two axioms, after
pinning their types and the *shapes of the inductives they quantify
over* to the toolchain's.  The pins below are hand-written through the
builder in `ConLeche/Kernel/Basis/Builder.lean`.

**Binder annotations (tasks #142, #203, #205).**  A pin carries no
binder name and no binder info — `Expr` has neither field (task #205),
so `propext`'s `{a b : Prop}` and `Classical.choice`'s `{α}` are
`pi`/`piI` for the reader only.  Binders carry no datum either (task
#342), so the comparison `ConstantVal.matchesPin` is plain equality;
`Expr.ErasedEq` — the model's "same denotation" relation, up to `fvar`
type annotations — bridges a hit.
-/
/-- The name `propext`. -/
def propextName : Name := anonymous |>.str "propext"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:37
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Classical.choice`. -/
def choiceName : Name := (anonymous |>.str "Classical") |>.str "choice"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:40
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff`. -/
def iffName : Name := anonymous |>.str "Iff"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:43
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff.intro`. -/
def iffIntroName : Name := iffName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:46
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff.rec`. -/
def iffRecName : Name := iffName |>.str "rec"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:49
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty`. -/
def nonemptyName : Name := anonymous |>.str "Nonempty"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:52
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty.intro`. -/
def nonemptyIntroName : Name := nonemptyName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:55
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty.rec`. -/
def nonemptyRecName : Name := nonemptyName |>.str "rec"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:50
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-!
# The compiler-trust axiom family (task #95)

`Init`'s compiler-trust scaffolding is installed rather than
declined:

* `Lean.trustCompiler : True` is trivially realizable — it is
  installed as an *opaque* (stored `axiomInfo`, exactly like a checked
  `opaque` declaration) with value `True.intro`, over a pinned `True`
  family.  No new meta-axiom: the model is `True.intro`'s own
  interpretation.
* `Lean.reduceNat` / `Lean.reduceBool` then check as ordinary
  `opaque`s (their exported values are identity functions modulo the
  `have := trustCompiler` wrapper); at its check their stored values are
  pinned against the identity function
  (`ConLeche/Kernel/TrustPins.lean`, hand-pinned since task #273 —
  every toolchain's definition after zeta) by definitional equality —
  the task-#47 pattern: drift declines, never silently.
* `Lean.ofReduceNat` / `Lean.ofReduceBool` are pinned axioms over
  those stored opaques (the task-#34 standard-axioms machinery).  With
  the stored reduce operation certified to be the identity (a
  definitional-equality certificate at the operation's own install,
  `checkReducePin`; the axiom's install checks `ofReduceAxOk`),
  `∀ a b, reduceNat a = b → a = b` interprets to
  an inhabited proposition (the hypothesis *is* the conclusion), so
  both axioms are true in the set model with the proof point as value.

`sorryAx` remains the only axiom tolerated as a *declaration*: its
record installs nothing and any use of it declines
(`sorryAxName`, `ConLeche/Kernel/Basis/Names.lean`).

The pins below are hand-written through the builder in
`ConLeche/Kernel/Basis/Builder.lean`.
-/
/-- The name `True`. -/
def trueName : Name := anonymous |>.str "True"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:53
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `True.intro`. -/
def trueIntroName : Name := trueName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:56
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.trustCompiler`. -/
def trustCompilerName : Name := (anonymous |>.str "Lean") |>.str "trustCompiler"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:59
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.reduceNat`. -/
def reduceNatName : Name := (anonymous |>.str "Lean") |>.str "reduceNat"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:62
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.reduceBool`. -/
def reduceBoolName : Name := (anonymous |>.str "Lean") |>.str "reduceBool"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:65
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.ofReduceNat`. -/
def ofReduceNatName : Name := (anonymous |>.str "Lean") |>.str "ofReduceNat"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:68
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.ofReduceBool`. -/
def ofReduceBoolName : Name := (anonymous |>.str "Lean") |>.str "ofReduceBool"
end ConLeche
end

namespace Proven.Frontx.ExprEx

frontx_ind ConLeche.uN on TExpr
frontx_ind ConLeche.vN on TExpr
frontx_ind ConLeche.u1N on TExpr
frontx_ind ConLeche.natName on TExpr
frontx_ind ConLeche.natPredName on TExpr
frontx_ind ConLeche.natAddName on TExpr
frontx_ind ConLeche.natSubName on TExpr
frontx_ind ConLeche.natMulName on TExpr
frontx_ind ConLeche.natPowName on TExpr
frontx_ind ConLeche.natBeqName on TExpr
frontx_ind ConLeche.natBleName on TExpr
frontx_ind ConLeche.natDivName on TExpr
frontx_ind ConLeche.natModName on TExpr
frontx_ind ConLeche.natGcdName on TExpr
frontx_ind ConLeche.natLandName on TExpr
frontx_ind ConLeche.natLorName on TExpr
frontx_ind ConLeche.natXorName on TExpr
frontx_ind ConLeche.natShiftLeftName on TExpr
frontx_ind ConLeche.natShiftRightName on TExpr
frontx_ind ConLeche.natZeroName on TExpr
frontx_ind ConLeche.natSuccName on TExpr
frontx_ind ConLeche.stringName on TExpr
frontx_ind ConLeche.stringOfListName on TExpr
frontx_ind ConLeche.listName on TExpr
frontx_ind ConLeche.listNilName on TExpr
frontx_ind ConLeche.listConsName on TExpr
frontx_ind ConLeche.charName on TExpr
frontx_ind ConLeche.charOfNatName on TExpr
frontx_ind ConLeche.eqName on TExpr
frontx_ind ConLeche.eqReflName on TExpr
frontx_ind ConLeche.emptyName on TExpr
frontx_ind ConLeche.falseName on TExpr
frontx_ind ConLeche.quotName on TExpr
frontx_ind ConLeche.quotMkName on TExpr
frontx_ind ConLeche.quotLiftName on TExpr
frontx_ind ConLeche.quotIndName on TExpr
frontx_ind ConLeche.quotSoundName on TExpr
frontx_ind ConLeche.andName on TExpr
frontx_ind ConLeche.sorryAxName on TExpr
frontx_ind ConLeche.andIntroName on TExpr
frontx_ind ConLeche.andRecName on TExpr
frontx_ind ConLeche.boolName on TExpr
frontx_ind ConLeche.eagerReduceName on TExpr
frontx_ind ConLeche.boolTrueName on TExpr
frontx_ind ConLeche.boolFalseName on TExpr
frontx_ind ConLeche.propextName on TExpr
frontx_ind ConLeche.choiceName on TExpr
frontx_ind ConLeche.iffName on TExpr
frontx_ind ConLeche.iffIntroName on TExpr
frontx_ind ConLeche.iffRecName on TExpr
frontx_ind ConLeche.nonemptyName on TExpr
frontx_ind ConLeche.nonemptyIntroName on TExpr
frontx_ind ConLeche.nonemptyRecName on TExpr
frontx_ind ConLeche.trueName on TExpr
frontx_ind ConLeche.trueIntroName on TExpr
frontx_ind ConLeche.trustCompilerName on TExpr
frontx_ind ConLeche.reduceNatName on TExpr
frontx_ind ConLeche.reduceBoolName on TExpr
frontx_ind ConLeche.ofReduceNatName on TExpr
frontx_ind ConLeche.ofReduceBoolName on TExpr

end Proven.Frontx.ExprEx

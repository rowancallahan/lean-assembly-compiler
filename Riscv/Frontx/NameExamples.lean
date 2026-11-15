/- Strings and names in the inductive path (NOTES section 23): `String` fields (the UTF-8 bytes as a chain of
cells, `Riscv/Frontx/IndStr.lean`), types nested in a shape (`frontx_ind_type T := ty nesting U`: `Level`'s
`param` holds a `Name`), `Decidable`-valued functions (`Name.decEq`, `Level.decEq`: `isTrue` is `1`), `if h : a = b`,
`=` on strings and on values of a declared type (the program's `DecidableEq` function), `==` through a `BEq` instance.

con-leche @6810492, verbatim (`Name`, `Level`, `Name.decEq`, `Level.decEq` and their `DecidableEq` instances are in
`IndExamples.lean` / `Ind2Examples.lean`). -/
import Riscv.Frontx.Ind2Examples

set_option linter.unusedVariables false

namespace ConLeche

-- Kernel/Name.lean:115-117
def Name.beq (a b : Name) : Bool := decide (a = b)

instance : BEq Name := ⟨Name.beq⟩

-- Kernel/Expr.lean:133-135
def Level.beq (a b : Level) : Bool := decide (a = b)

instance : BEq Level := ⟨Level.beq⟩

end ConLeche

namespace Proven.Frontx.IndEx

-- `Name`: `anonymous` (tag 0), `str` (1: the prefix, then the string), `num` (2: the prefix, then 8 bytes); the
-- string's bytes as `Bytes8` (tag 3 = end, tag 4 = one byte follows)
frontx_ind_type NameT := ConLeche.Name

-- `Name.beq` = `decide (a = b)`: the program of `Name.decEq` (and `Bytes8.eqb` for the strings)
frontx_ind ConLeche.Name.beq on NameT

/-- entry: `==` on names (the `BEq Name` instance) -/
def nameBEq (a b : ConLeche.Name) : Bool := a == b
frontx_ind nameBEq on NameT

-- `Level` with its `param` names in the byte format: tags 0-4 `Level`, 5-7 `Name`, 8-9 the strings
frontx_ind_type LevelN := ConLeche.Level nesting ConLeche.Name

-- `Level.beq` = `decide (a = b)`: `Level.decEq`, calling `Name.decEq` for `param`
frontx_ind ConLeche.Level.beq on LevelN

/-- entry: `==` on levels (the `BEq Level` instance) -/
def levelBEq (a b : ConLeche.Level) : Bool := a == b
frontx_ind levelBEq on LevelN

end Proven.Frontx.IndEx

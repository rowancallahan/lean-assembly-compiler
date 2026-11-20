/- Strings and names in the inductive path (NOTES sections 23, 28): `String` fields (in the byte format the length,
8 bytes little-endian, then the UTF-8 bytes, `encString`; in memory a chain of cells, `Riscv/Frontx/IndStr.lean`), types nested in a shape (`frontx_ind_type T := ty nesting U`: `Level`'s
`param` holds a `Name`), `Decidable`-valued functions (`Name.decEq`, `Level.decEq`: `isTrue` is `1`), `if h : a = b`,
`=` on strings and on values of a declared type (the program's `DecidableEq` function), `==` through a `BEq` instance.

con-leche @6810492, verbatim (`Name`, `Level`, `Name.decEq`, `Level.decEq` and their `DecidableEq` instances are in
`IndExamples.lean` / `Ind2Examples.lean`). -/
import Legacy.Riscv.Frontx.Ind2Examples

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

-- `Name`: `anonymous` (tag 0), `str` (1: the prefix, then the string), `num` (2: the prefix, then 8 bytes); in
-- memory the string's bytes as `Bytes8` (tag 3 = end, tag 4 = one byte follows)
frontx_ind_type NameT := ConLeche.Name

open Proven.Frontx.Ind in
/-- **The byte format of `Name`** (the input of the entries below, `NameT.enc`): `anonymous` is `[0]` -/
theorem NameT.enc_anonymous : NameT.enc .anonymous = [0] := rfl

open Proven.Frontx.Ind in
/-- `str p s`: tag `1`, the prefix, then the string (its length, 8 bytes little-endian, then its UTF-8 bytes) -/
theorem NameT.enc_str (p : ConLeche.Name) (s : String) : NameT.enc (.str p s) = 1 :: NameT.enc p ++ encString s := by
  have e := emb_ofList NameT.N1.emb 3 rfl (fun _ _ => rfl) s.toUTF8.data.toList
  simp only [NameT.enc, NameT.emb, Proven.Mach.Ind.C.enc, NameT.sh, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, List.flatMap_cons, List.flatMap_nil, Proven.Mach.Ind.encF, List.append_nil,
    Bytes8.ofString, e, senc_ofString]
  rfl

/-- `num p n`: tag `2`, the prefix, then `n` (8 bytes, little-endian) -/
theorem NameT.enc_num (p : ConLeche.Name) (n : Nat) :
    NameT.enc (.num p n) = 2 :: NameT.enc p ++ Proven.enc (BitVec.ofNat 64 n) := by
  simp only [NameT.enc, NameT.emb, Proven.Mach.Ind.C.enc, NameT.sh, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, List.flatMap_cons, List.flatMap_nil, Proven.Mach.Ind.encF, List.append_nil]
  rfl

-- e.g. `Name.str .anonymous "aλ"`
example : NameT.enc (.str .anonymous "aλ") = [1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0x61, 0xce, 0xbb] := by
  rw [NameT.enc_str]; decide +kernel

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

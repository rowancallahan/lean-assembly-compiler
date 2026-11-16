/- Test cases of the con-leche `Name` constants of `Riscv/Frontx/ConLecheBlk.lean` (NOTES section 31) against executed Lean:
`lake env lean --tstack=4000000 Testing/asm/emit_conleche_blk.lean`, then `python3 Testing/asm/frontx_test.py check 50 blk_<name>`.  Input: any `TExpr` tree (ignored). -/
/- Test cases of the con-leche `Expr` functions (NOTES section 25), against executed Lean:
`lake env lean --tstack=4000000 Testing/asm/emit_expr.lean`, then `bash Testing/scripts/frontx_tests.sh`.
Each `.words`: first line `indw <retLen>`, then the code; each `.cases` line: input bytes, Lean's result bytes, the
work block (`Ind.spaceA m nl (fun _ => cells)` with this input's cells; the theorem's `cellsSup` is at least that). -/
import Riscv.Frontx.ConLecheBlk

open Proven Proven.Frontx.ExprEx

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]

def emitIndW (name : String) (code : List (BitVec 32)) (retLen : Bool) (cases : List (List UInt8 × List UInt8 × Nat)) :
    IO Unit := do
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words"
    (String.intercalate "\n" (s!"indw {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (cases.map fun (x, y, w) => s!"{hx x} {hx y} {w}\n"))
def spW (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length

def strs : List String := ["", "a", "x", "Nat", "succ", "é", "λ", "∀x", "Nat.add", "a\x00b"]
def genN : Nat → Nat → ConLeche.Name
  | 0, _ => .anonymous
  | d + 1, s => match rnd s d % 3 with
    | 0 => .str (genN d (s + 1)) (strs.getD (rnd s 7 % strs.length) "")
    | 1 => .num (genN d (s + 2)) (match rnd s 3 % 4 with | 0 => 0 | 1 => 2 ^ 64 - 1 | 2 => 7 | _ => rnd s 9)
    | _ => .anonymous
def genL : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param (genN (s % 3) s)
  | d + 1, s => match rnd s d % 6 with
    | 0 => .zero | 1 => .param (genN (s % 3) s) | 2 => .succ (genL d (s + 1))
    | 3 => .max (genL d (2 * s)) (genL d (2 * s + 1)) | 4 => .imax (genL d (2 * s)) (genL d (2 * s + 1))
    | _ => .succ .zero
def genLs (n s : Nat) : List ConLeche.Level := (List.range n).map fun j => genL (j % 3) (s + j)
/-- bound-variable indices near the binder depths (`0`, `1`, `2`, `3`) and large ones (`2^64 - 1`) -/
def idx (s : Nat) : Nat := match rnd s 5 % 7 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 2 ^ 64 - 1 | 5 => 5 | _ => rnd s 2 % 9
/-- expressions of depth at most `d`: every constructor, with names, level lists, literals -/
def genE : Nat → Nat → ConLeche.Expr
  | 0, s => match rnd s 0 % 6 with
    | 0 => .bvar (idx s) | 1 => .sort (genL 2 s) | 2 => .const (genN 2 s) (genLs (s % 3) s)
    | 3 => .lit (.natVal (idx (s + 1))) | 4 => .lit (.strVal (strs.getD (s % strs.length) ""))
    | _ => .bvar (s % 3)
  | d + 1, s => match rnd s d % 10 with
    | 0 => .bvar (idx s)
    | 1 => .fvar (idx (s + 3)) (genE d (s + 1))
    | 2 => .app (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 3 => .lam (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 4 => .forallE (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 5 => .letE (genE d (3 * s + 1)) (genE d (3 * s + 2)) (genE d (3 * s + 3))
    | 6 => .proj (genN 2 s) (idx s) (genE d (s + 5))
    | 7 => .const (genN 3 s) (genLs (s % 4) s)
    | 8 => .lit (.strVal (strs.getD (s % strs.length) ""))
    | _ => .app (genE d (2 * s + 3)) (.bvar (s % 4))
def exprs : List ConLeche.Expr := [.bvar 0, .bvar 1, .fvar 0 (.sort .zero), .lam (.sort .zero) (.bvar 0),
  .lam (.sort .zero) (.bvar 1), .letE (.bvar 0) (.bvar 1) (.bvar 2), .proj .anonymous 0 (.bvar 0)] ++
  (List.range 53).map fun i => genE (i % 6 + 1) (i + 1)
def exprPairs : List (ConLeche.Expr × ConLeche.Expr) := exprs.zip
  ((List.range exprs.length).map fun i => match i % 3 with
    | 0 => .fvar 7 (.sort .zero) | 1 => .const (genN 2 i) (genLs 2 i) | _ => genE (i % 3) (i + 9))


#eval do
  emitIndW "blk_natname" ConLeche.natName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natName, spW 1 16 (ConLeche.natName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natpredname" ConLeche.natPredName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natPredName, spW 1 16 (ConLeche.natPredName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_nataddname" ConLeche.natAddName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natAddName, spW 1 16 (ConLeche.natAddName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natsubname" ConLeche.natSubName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natSubName, spW 1 16 (ConLeche.natSubName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natmulname" ConLeche.natMulName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natMulName, spW 1 16 (ConLeche.natMulName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natpowname" ConLeche.natPowName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natPowName, spW 1 16 (ConLeche.natPowName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natbeqname" ConLeche.natBeqName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natBeqName, spW 1 16 (ConLeche.natBeqName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natblename" ConLeche.natBleName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natBleName, spW 1 16 (ConLeche.natBleName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natdivname" ConLeche.natDivName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natDivName, spW 1 16 (ConLeche.natDivName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natmodname" ConLeche.natModName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natModName, spW 1 16 (ConLeche.natModName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natgcdname" ConLeche.natGcdName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natGcdName, spW 1 16 (ConLeche.natGcdName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natlandname" ConLeche.natLandName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natLandName, spW 1 16 (ConLeche.natLandName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natlorname" ConLeche.natLorName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natLorName, spW 1 16 (ConLeche.natLorName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natxorname" ConLeche.natXorName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natXorName, spW 1 16 (ConLeche.natXorName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natshiftleftname" ConLeche.natShiftLeftName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natShiftLeftName, spW 1 16 (ConLeche.natShiftLeftName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natshiftrightname" ConLeche.natShiftRightName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natShiftRightName, spW 1 16 (ConLeche.natShiftRightName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natzeroname" ConLeche.natZeroName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natZeroName, spW 1 16 (ConLeche.natZeroName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_natsuccname" ConLeche.natSuccName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.natSuccName, spW 1 16 (ConLeche.natSuccName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_stringname" ConLeche.stringName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.stringName, spW 1 16 (ConLeche.stringName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_stringoflistname" ConLeche.stringOfListName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.stringOfListName, spW 1 16 (ConLeche.stringOfListName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_listname" ConLeche.listName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.listName, spW 1 16 (ConLeche.listName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_listnilname" ConLeche.listNilName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.listNilName, spW 1 16 (ConLeche.listNilName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_listconsname" ConLeche.listConsName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.listConsName, spW 1 16 (ConLeche.listConsName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_charname" ConLeche.charName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.charName, spW 1 16 (ConLeche.charName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_charofnatname" ConLeche.charOfNatName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.charOfNatName, spW 1 16 (ConLeche.charOfNatName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_eqname" ConLeche.eqName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.eqName, spW 1 16 (ConLeche.eqName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_eqreflname" ConLeche.eqReflName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.eqReflName, spW 1 16 (ConLeche.eqReflName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_emptyname" ConLeche.emptyName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.emptyName, spW 1 16 (ConLeche.emptyName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_falsename" ConLeche.falseName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.falseName, spW 1 16 (ConLeche.falseName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_quotname" ConLeche.quotName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.quotName, spW 1 16 (ConLeche.quotName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_quotmkname" ConLeche.quotMkName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.quotMkName, spW 1 16 (ConLeche.quotMkName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_quotliftname" ConLeche.quotLiftName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.quotLiftName, spW 1 16 (ConLeche.quotLiftName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_quotindname" ConLeche.quotIndName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.quotIndName, spW 1 16 (ConLeche.quotIndName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_quotsoundname" ConLeche.quotSoundName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.quotSoundName, spW 1 16 (ConLeche.quotSoundName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_andname" ConLeche.andName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.andName, spW 1 16 (ConLeche.andName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_sorryaxname" ConLeche.sorryAxName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.sorryAxName, spW 1 16 (ConLeche.sorryAxName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_boolname" ConLeche.boolName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.boolName, spW 1 16 (ConLeche.boolName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_eagerreducename" ConLeche.eagerReduceName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.eagerReduceName, spW 1 16 (ConLeche.eagerReduceName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_booltruename" ConLeche.boolTrueName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.boolTrueName, spW 1 16 (ConLeche.boolTrueName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "blk_boolfalsename" ConLeche.boolFalseName.cst.code true (exprs.map fun e =>
    (TExpr.enc e, TExpr.N2.enc ConLeche.boolFalseName, spW 1 16 (ConLeche.boolFalseName.cst.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))


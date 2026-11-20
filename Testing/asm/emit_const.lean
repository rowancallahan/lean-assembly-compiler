/- Test cases of the constants folded as data (`frontx_const`, `Riscv/Frontx/ConstExamples.lean`, NOTES section 36)
against executed Lean: `lake env lean --tstack=4000000 Testing/asm/emit_const.lean`, then
`python3 Testing/asm/frontx_test.py check 60 cst_<name>`.  Input: any `TExpr` tree (ignored) or raw bytes (ignored);
work block 15 bytes (the theorem's space). -/
import Legacy.Riscv.Frontx.ConstExamples

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



def rawIns : List (List UInt8) := (List.range 60).map fun i => (List.range (i % 17)).map fun j => UInt8.ofNat (rnd i j)

#eval do
  emitIndW "cst_natname" ConLeche.natName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natName), 15))
  emitIndW "cst_natpredname" ConLeche.natPredName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natPredName), 15))
  emitIndW "cst_nataddname" ConLeche.natAddName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natAddName), 15))
  emitIndW "cst_natsubname" ConLeche.natSubName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natSubName), 15))
  emitIndW "cst_natmulname" ConLeche.natMulName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natMulName), 15))
  emitIndW "cst_natpowname" ConLeche.natPowName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natPowName), 15))
  emitIndW "cst_natbeqname" ConLeche.natBeqName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natBeqName), 15))
  emitIndW "cst_natblename" ConLeche.natBleName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natBleName), 15))
  emitIndW "cst_natdivname" ConLeche.natDivName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natDivName), 15))
  emitIndW "cst_natmodname" ConLeche.natModName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natModName), 15))
  emitIndW "cst_natgcdname" ConLeche.natGcdName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natGcdName), 15))
  emitIndW "cst_natlandname" ConLeche.natLandName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natLandName), 15))
  emitIndW "cst_natlorname" ConLeche.natLorName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natLorName), 15))
  emitIndW "cst_natxorname" ConLeche.natXorName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natXorName), 15))
  emitIndW "cst_natshiftleftname" ConLeche.natShiftLeftName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natShiftLeftName), 15))
  emitIndW "cst_natshiftrightname" ConLeche.natShiftRightName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natShiftRightName), 15))
  emitIndW "cst_natzeroname" ConLeche.natZeroName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natZeroName), 15))
  emitIndW "cst_natsuccname" ConLeche.natSuccName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.natSuccName), 15))
  emitIndW "cst_stringname" ConLeche.stringName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.stringName), 15))
  emitIndW "cst_stringoflistname" ConLeche.stringOfListName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.stringOfListName), 15))
  emitIndW "cst_listname" ConLeche.listName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.listName), 15))
  emitIndW "cst_listnilname" ConLeche.listNilName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.listNilName), 15))
  emitIndW "cst_listconsname" ConLeche.listConsName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.listConsName), 15))
  emitIndW "cst_charname" ConLeche.charName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.charName), 15))
  emitIndW "cst_charofnatname" ConLeche.charOfNatName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.charOfNatName), 15))
  emitIndW "cst_eqname" ConLeche.eqName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.eqName), 15))
  emitIndW "cst_eqreflname" ConLeche.eqReflName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.eqReflName), 15))
  emitIndW "cst_emptyname" ConLeche.emptyName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.emptyName), 15))
  emitIndW "cst_falsename" ConLeche.falseName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.falseName), 15))
  emitIndW "cst_quotname" ConLeche.quotName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.quotName), 15))
  emitIndW "cst_quotmkname" ConLeche.quotMkName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.quotMkName), 15))
  emitIndW "cst_quotliftname" ConLeche.quotLiftName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.quotLiftName), 15))
  emitIndW "cst_quotindname" ConLeche.quotIndName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.quotIndName), 15))
  emitIndW "cst_quotsoundname" ConLeche.quotSoundName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.quotSoundName), 15))
  emitIndW "cst_andname" ConLeche.andName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.andName), 15))
  emitIndW "cst_sorryaxname" ConLeche.sorryAxName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.sorryAxName), 15))
  emitIndW "cst_boolname" ConLeche.boolName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.boolName), 15))
  emitIndW "cst_eagerreducename" ConLeche.eagerReduceName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.eagerReduceName), 15))
  emitIndW "cst_booltruename" ConLeche.boolTrueName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.boolTrueName), 15))
  emitIndW "cst_boolfalsename" ConLeche.boolFalseName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.boolFalseName), 15))
  emitIndW "cst_basisdsl_prop" ConLeche.BasisDSL.prop.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.BasisDSL.prop), 15))
  emitIndW "cst_basisdsl_type1" ConLeche.BasisDSL.type1.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.BasisDSL.type1), 15))
  emitIndW "cst_cached_instccapc" ConLeche.Cached.instCCapC.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Cached.instCCapC), 15))
  emitIndW "cst_cached_natcountmax" ConLeche.Cached.natCountMax.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Cached.natCountMax), 15))
  emitIndW "cst_cached_peelfuel" ConLeche.Cached.peelFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Cached.peelFuel), 15))
  emitIndW "cst_display_maxlen" ConLeche.Display.maxLen.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Display.maxLen), 15))
  emitIndW "cst_expr_bvarpoolsize" ConLeche.Expr.bvarPoolSize.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Expr.bvarPoolSize), 15))
  emitIndW "cst_level_defaultfuel" ConLeche.Level.defaultFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.Level.defaultFuel), 15))
  emitIndW "cst_andintroname" ConLeche.andIntroName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.andIntroName), 15))
  emitIndW "cst_andrecminor" ConLeche.andRecMinor.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.andRecMinor), 15))
  emitIndW "cst_andrecmotive" ConLeche.andRecMotive.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.andRecMotive), 15))
  emitIndW "cst_andrecname" ConLeche.andRecName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.andRecName), 15))
  emitIndW "cst_bindersfuel" ConLeche.bindersFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.bindersFuel), 15))
  emitIndW "cst_checkfuel" ConLeche.checkFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.checkFuel), 15))
  emitIndW "cst_choicename" ConLeche.choiceName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.choiceName), 15))
  emitIndW "cst_defeqloopfuel" ConLeche.defeqLoopFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.defeqLoopFuel), 15))
  emitIndW "cst_eqrecmotive" ConLeche.eqRecMotive.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.eqRecMotive), 15))
  emitIndW "cst_fuelslack" ConLeche.fuelSlack.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.fuelSlack), 15))
  emitIndW "cst_iffname" ConLeche.iffName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.iffName), 15))
  emitIndW "cst_iffintroname" ConLeche.iffIntroName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.iffIntroName), 15))
  emitIndW "cst_iffrecname" ConLeche.iffRecName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.iffRecName), 15))
  emitIndW "cst_natt" ConLeche.natT.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.natT), 15))
  emitIndW "cst_natrecmotive" ConLeche.natRecMotive.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.natRecMotive), 15))
  emitIndW "cst_natrecsucc" ConLeche.natRecSucc.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.natRecSucc), 15))
  emitIndW "cst_nonemptyname" ConLeche.nonemptyName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.nonemptyName), 15))
  emitIndW "cst_nonemptyintroname" ConLeche.nonemptyIntroName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.nonemptyIntroName), 15))
  emitIndW "cst_nonemptyrecname" ConLeche.nonemptyRecName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.nonemptyRecName), 15))
  emitIndW "cst_ofreduceboolname" ConLeche.ofReduceBoolName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.ofReduceBoolName), 15))
  emitIndW "cst_ofreducenatname" ConLeche.ofReduceNatName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.ofReduceNatName), 15))
  emitIndW "cst_propextname" ConLeche.propextName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.propextName), 15))
  emitIndW "cst_quotindmk" ConLeche.quotIndMk.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.quotIndMk), 15))
  emitIndW "cst_quotindmotive" ConLeche.quotIndMotive.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.quotIndMotive), 15))
  emitIndW "cst_quotliftf" ConLeche.quotLiftF.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.quotLiftF), 15))
  emitIndW "cst_quotlifth" ConLeche.quotLiftH.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.quotLiftH), 15))
  emitIndW "cst_quotrel" ConLeche.quotRel.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.quotRel), 15))
  emitIndW "cst_reducebooldeclpin" ConLeche.reduceBoolDeclPin.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.reduceBoolDeclPin), 15))
  emitIndW "cst_reduceboolname" ConLeche.reduceBoolName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.reduceBoolName), 15))
  emitIndW "cst_reducenatdeclpin" ConLeche.reduceNatDeclPin.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.enc ConLeche.reduceNatDeclPin), 15))
  emitIndW "cst_satrange" ConLeche.satRange.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.satRange), 15))
  emitIndW "cst_truename" ConLeche.trueName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.trueName), 15))
  emitIndW "cst_trueintroname" ConLeche.trueIntroName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.trueIntroName), 15))
  emitIndW "cst_trustcompilername" ConLeche.trustCompilerName.data.code true (exprs.map fun e => (TExpr.enc e, (TExpr.N2.enc ConLeche.trustCompilerName), 15))
  emitIndW "cst_unitlikefuel" ConLeche.unitLikeFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.unitLikeFuel), 15))
  emitIndW "cst_whnfcoreloopfuel" ConLeche.whnfCoreLoopFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.whnfCoreLoopFuel), 15))
  emitIndW "cst_whnfloopfuel" ConLeche.whnfLoopFuel.data.code true (exprs.map fun e => (TExpr.enc e, (Proven.Frontx.Const.encWord ConLeche.whnfLoopFuel), 15))
  emitIndW "cst_ir_r0" Proven.Ir.R0.data.code true (rawIns.map fun x => (x, Proven.Frontx.Const.encFin Proven.Ir.R0, 15))
  emitIndW "cst_ir_r1" Proven.Ir.R1.data.code true (rawIns.map fun x => (x, Proven.Frontx.Const.encFin Proven.Ir.R1, 15))
  emitIndW "cst_ir_rlim" Proven.Ir.RLim.data.code true (rawIns.map fun x => (x, Proven.Frontx.Const.encFin Proven.Ir.RLim, 15))

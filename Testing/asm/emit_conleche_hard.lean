/- Test cases of the con-leche functions of `Riscv/Frontx/ConLecheHard.lean` (NOTES section 36) against executed
Lean: `lake env lean --tstack=4000000 Testing/asm/emit_conleche_hard.lean`, then
`python3 Testing/asm/frontx_test.py check 50 hard_<name>`.  Expressions from `emit_expr.lean`'s generator plus the
cases each function distinguishes (the constants it compares with, nested literals, `∀` chains).  Work block:
the theorem's bound with this input's cells (`Pg.al`). -/
import Riscv.Frontx.ConLecheHard

open Proven Proven.Frontx.ExprEx Proven.Frontx.ConLecheHard

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

/-- the constants the functions compare with, with and without levels, and near misses -/
def consts : List ConLeche.Expr := [.const ConLeche.natZeroName [], .const ConLeche.natZeroName [.zero],
  .const ConLeche.natName [], .const (.str .anonymous "zero") [], .const ConLeche.boolTrueName [],
  .const ConLeche.boolTrueName [.zero], .const ConLeche.boolFalseName [], .const ConLeche.natSuccName [],
  .const ConLeche.eagerReduceName [], .lit (.natVal 0), .lit (.natVal 1), .lit (.natVal (2 ^ 64 - 1)),
  .lit (.strVal ""), .lit (.strVal "zero"),
  .app (.app (.const ConLeche.eagerReduceName []) (.bvar 0)) (.bvar 1),
  .app (.app (.const ConLeche.eagerReduceName [.zero]) (.sort .zero)) (.lit (.natVal 3)),
  .app (.app (.const ConLeche.natName []) (.bvar 0)) (.bvar 1),
  .app (.const ConLeche.eagerReduceName []) (.bvar 1),
  .app (.const ConLeche.natSuccName []) (.lit (.natVal 4)), .app (.const ConLeche.natSuccName [.zero]) (.bvar 0),
  .app (.const ConLeche.natName []) (.bvar 0)]
def cases0 : List ConLeche.Expr := consts ++ exprs
/-- `∀` chains of length `n` over a body -/
def pis : Nat → ConLeche.Expr → ConLeche.Expr
  | 0, b => b
  | n + 1, b => .forallE (genE 1 n) (pis n b)
def piCases : List (ConLeche.Expr × Nat) := (List.range 30).map (fun i => (pis (i % 5) (genE (i % 3) i), i % 7)) ++
  (exprs.take 30).map (fun e => (e, rnd 3 e.sizeF % 3))
def small (n : Nat) : Nat := match n % 5 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 5 | _ => 1000

def spA (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length

#eval do
  emitIndW "hard_lift1" lift1.code true ((cases0.zip (List.range cases0.length)).map fun (e, i) =>
    let x := TExpr.enc e ++ leN 8 (small i)
    (x, TExpr.enc (lift1 e (small i)), spA 1 19 (lift1.ind.pg.al (TExpr.emb e) (BitVec.ofNat 64 (small i)) .z) x))
  emitIndW "hard_abs0" abs0.code true ((cases0.zip (List.range cases0.length)).map fun (e, i) =>
    let x := TExpr.enc e ++ leN 8 (small (i + 2))
    (x, TExpr.enc (abs0 e (small (i + 2))), spA 1 19 (abs0.ind.pg.al (TExpr.emb e) (BitVec.ofNat 64 (small (i + 2))) .z) x))
  emitIndW "hard_isstrlit" ConLeche.Expr.isStrLit.code false (cases0.map fun e =>
    (TExpr.enc e, boolB e.isStrLit, Proven.Frontx.Ind.space ConLeche.Expr.isStrLit.ind.pg.M (TExpr.enc e).length))
  emitIndW "hard_isnatzero" ConLeche.Expr.isNatZero.code false (cases0.map fun e =>
    (TExpr.enc e, boolB e.isNatZero, spA 6 20 (ConLeche.Expr.isNatZero.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "hard_isbooltrue" ConLeche.Expr.isBoolTrue.code false (cases0.map fun e =>
    (TExpr.enc e, boolB e.isBoolTrue, spA 6 20 (ConLeche.Expr.isBoolTrue.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "hard_peeln" peelN.code true (piCases.map fun (e, k) =>
    let x := TExprF.enc e ++ leN 8 k
    (x, TExprF.N6.enc (peelN e k), Proven.Frontx.Ind.spaceA 1 16 (fun n => peelN.ind.pg.M * n) x.length))
  emitIndW "hard_domn" domN.code true (piCases.map fun (e, k) =>
    let x := TExprF.enc e ++ leN 8 k
    (x, TExprF.N6.enc (domN e k), Proven.Frontx.Ind.spaceA 1 16 (fun n => domN.ind.pg.M * n) x.length))
#eval (cases0.length, (cases0.map ConLeche.Expr.isNatZero).count true, (cases0.map ConLeche.Expr.isBoolTrue).count true,
  (cases0.map ConLeche.Expr.isStrLit).count true, (piCases.map fun (e, k) => (peelN e k).isSome).count true)

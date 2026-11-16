/- Test cases of the con-leche `Expr` functions (NOTES section 25), against executed Lean:
`lake env lean --tstack=4000000 Testing/asm/emit_expr.lean`, then `bash Testing/scripts/frontx_tests.sh`.
Each `.words`: first line `indw <retLen>`, then the code; each `.cases` line: input bytes, Lean's result bytes, the
work block (`Ind.spaceA m nl (fun _ => cells)` with this input's cells; the theorem's `cellsSup` is at least that). -/
import Riscv.Frontx.ConLecheS2

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
  emitIndW "expr_hasfvar" ConLeche.Expr.hasFvar.code false (exprs.map fun e =>
    (TExpr.enc e, boolB e.hasFvar, spW 1 16 (ConLeche.Expr.hasFvar.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "expr_closed0" closed0.code false (exprs.map fun e =>
    (TExpr.enc e, boolB (closed0 e), spW 1 16 (closed0.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitIndW "expr_inst1" inst1.code true (exprPairs.map fun p =>
    (TExpr.enc2 p, TExpr.enc (inst1 p.1 p.2), spW 1 19 (inst1.ind.pg.al (TExpr.emb p.1) 0 (TExpr.emb p.2)) (TExpr.enc2 p)))
/-- the words of the depth argument of `scopedD`: around the indices of `exprs` -/
def depths : List Nat := (List.range exprs.length).map fun i => match i % 5 with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 ^ 64 - 1 | _ => rnd i 1 % 8
def w1 (e : ConLeche.Expr) (b : Bool) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, boolB b, spW 1 16 pg (TExpr.enc e))
def wN (e : ConLeche.Expr) (n : Nat) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, leN 8 n, spW 1 16 pg (TExpr.enc e))
def wT (e r : ConLeche.Expr) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, TExpr.enc r, spW 1 16 pg (TExpr.enc e))
#eval do
  emitIndW "conleche_iscompound" ConLeche.Expr.isCompound.code false (exprs.map fun e =>
    w1 e e.isCompound (ConLeche.Expr.isCompound.ind.pg.al (TExpr.emb e) 0 .z))
  emitIndW "conleche_iscompoundf" ConLeche.Expr.isCompoundF.code false (exprs.map fun e =>
    w1 e e.isCompoundF (ConLeche.Expr.isCompoundF.ind.pg.al (TExpr.emb e) 0 .z))

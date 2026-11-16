/- Test vectors of the compiled rows of `Riscv/Frontx/BookS1.lean` (book survey 3, first third; BOOK_S1.md): for each
`frontx_ind` entry the code, the input format `T.enc` (`frontx_ind_type`) and Lean's result, written to
`Testing/asm/frontx-words/<name>.{words,cases}` in the format of `emit_frontx.lean` (`ind A B L` first line).
Run: `lake env lean Testing/asm/emit_books1.lean`, then `python3 Testing/asm/frontx_test.py check 50 <name>`
(QEMU + Sail; pending: run at merge). -/
import Riscv.Frontx.BookS1
open Proven Proven.Frontx

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]

def emitInd (name : String) (code : List (BitVec 32)) (M : Nat) (retLen : Bool) (cases : List (List UInt8 × List UInt8)) :
    IO Unit := do
  let A := Proven.Frontx.Ind.space M 0
  let B := Proven.Frontx.Ind.space M 1 - A
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words"
    (String.intercalate "\n" (s!"ind {A} {B} {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases" (String.join (cases.map fun (x, y) => s!"{hx x} {hx y}\n"))

open Proven.Frontx.BookS1.R320 in
def finiteCases : List Finite :=
  [.unit, .bool, .pair .unit .unit, .pair .bool .unit, .arr .unit .unit, .arr .unit .bool,
   .pair (.arr .bool .unit) .unit, .arr (.pair .unit .unit) .bool, .arr (.arr .unit .unit) .unit,
   .pair .unit (.pair .unit .unit), .arr .bool (.arr .unit .bool)]

#eval do
  emitInd "finite_issingleton" Proven.Frontx.BookS1.R320.Finite.isSingleton.code
    Proven.Frontx.BookS1.R320.Finite.isSingleton.ind.pg.M false
    (finiteCases.map fun x => (Proven.Frontx.BookS1.R320.TT320_0.enc x, boolB (Proven.Frontx.BookS1.R320.Finite.isSingleton x)))

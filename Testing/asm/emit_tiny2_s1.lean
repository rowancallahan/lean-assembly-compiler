import Riscv.Frontx.TinyS1
open Proven Proven.Frontx Proven.Frontx.Tiny2S1
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def genE : Nat → Nat → Ex
  | 0, s => if rnd s 1 % 3 == 0 then .var else .lit (UInt64.ofNat (rnd s 2 % (if s % 2 == 0 then 100 else 2^64)))
  | d + 1, s => match rnd s d % 5 with
    | 0 => .lit (UInt64.ofNat (rnd s 3 % 1000)) | 1 => .var
    | _ => .bin (UInt64.ofNat (rnd s 4 % 3)) (genE d (2 * s + 1)) (genE d (2 * s + 2))
def exprs : List Ex := [.lit 7, .var, .bin 0 .var (.lit 1)] ++ (List.range 47).map fun i => genE (i % 6 + 1) (i + 3)
def xs : List UInt64 := [0, 1, 5, 0xFFFFFFFFFFFFFFFF, 123456789]
#eval do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s1.words"
    (String.intercalate "\n" ("indw 1" :: comp.code.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s1.cases" (String.join (exprs.map fun e =>
    let x := ExT.enc e
    s!"{hx x} {hx (InsT.enc (comp e))} {Ind.spaceA 2 20 (fun _ => comp.ind.pg.al (ExT.emb e) 0 .z) x.length}\n"))
  -- (hex of source, input x, Lean value of the source at x)
  IO.FS.writeFile "Testing/asm/tiny2/s1.run" (String.join (exprs.flatMap fun e => xs.map fun x =>
    s!"{hx (ExT.enc e)} {x} {e.eval x}\n"))
  -- the reference stack machine on Lean's compiled code agrees with eval
  IO.println (exprs.all fun e => xs.all fun x => (comp e).run x [] == e.eval x)

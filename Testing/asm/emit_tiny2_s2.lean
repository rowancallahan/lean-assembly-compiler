import Riscv.Frontx.TinyS2
open Proven Proven.Frontx Proven.Frontx.Tiny2S2
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- well-formed sources: bin 0..4, seq 5, set 6 (b = nil), cnd 7 (a = alt node `bin 8 t e`, b = condition) -/
def genE : Nat → Nat → T
  | 0, s => if rnd s 1 % 3 == 0 then .var else .lit (UInt64.ofNat (rnd s 2 % (if s % 2 == 0 then 6 else 2^64)))
  | d + 1, s => match rnd s d % 9 with
    | 0 => .lit (UInt64.ofNat (rnd s 3 % 1000)) | 1 => .var
    | 2 => .bin 5 (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 3 => .bin 6 (genE d (2 * s + 1)) .nil
    | 4 => .bin 7 (.bin 8 (genE d (4 * s + 1)) (genE d (4 * s + 2))) (genE d (4 * s + 3))
    | _ => .bin (UInt64.ofNat (rnd s 4 % 5)) (genE d (2 * s + 1)) (genE d (2 * s + 2))
def exprs : List T := [.lit 7, .var, .bin 3 .var (.lit 5), .bin 7 (.bin 8 (.lit 1) (.lit 2)) (.bin 4 .var (.lit 5))] ++
  (List.range 46).map fun i => genE (i % 6 + 1) (i + 3)
def xs : List UInt64 := [0, 1, 5, 0xFFFFFFFFFFFFFFFF, 123456789]
#eval do
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s2.words"
    (String.intercalate "\n" ("indw 1" :: compile.code.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s2.cases" (String.join (exprs.map fun e =>
    let x := TT.enc e
    s!"{hx x} {hx (TT.enc (compile e))} {Ind.spaceA 1 16 (fun n => compile.ind.pg.M * n) x.length}\n"))
  IO.FS.writeFile "Testing/asm/tiny2/s2.run" (String.join (exprs.flatMap fun e => xs.map fun x =>
    s!"{hx (TT.enc e)} {x} {eval e x}\n"))
  IO.println (exprs.all fun e => xs.all fun x => run (compile e) x [] == eval e x)

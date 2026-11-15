import Riscv.Frontx.TinyS5
open Proven Proven.Frontx Proven.Frontx.Tiny2S5
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def leaf (s : Nat) : T := if rnd s 1 % 3 == 0 then .var else .lit ((rnd s 2 % 2048) * 1048576)
/-- left-deep: bin k e leaf, k ∈ {add 0, sub 2^30, xor 2^14, sltu 3·2^12} -/
def genE : Nat → Nat → T
  | 0, s => leaf s
  | d + 1, s => .bin ([0, 1073741824, 16384, 12288].getD (rnd s 4 % 4) 0) (genE d (2 * s + 1)) (leaf (2 * s + 2))
def exprs : List T := [.lit 1048576, .var, .bin 0 .var (.lit 5242880)] ++ (List.range 47).map fun i => genE (i % 7) (i + 3)
def xs : List UInt64 := [0, 1, 5, 0xFFFFFFFFFFFFFFFF, 123456789]
#eval do
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s5.words"
    (String.intercalate "\n" ("indw 1" :: compile.code.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/frontx-words/tiny2_s5.cases" (String.join (exprs.map fun e =>
    let x := TT.enc e
    s!"{hx x} {hx (TT.enc (compile e))} {Ind.spaceA 1 16 (fun n => compile.ind.pg.M * n) x.length}\n"))
  IO.FS.writeFile "Testing/asm/tiny2/s5.run" (String.join (exprs.flatMap fun e => xs.map fun x =>
    s!"{hx (TT.enc e)} {x} {Tiny2S5.eval x e}\n"))
  IO.println "ok" 

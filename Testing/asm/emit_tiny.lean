import Legacy.Riscv.Frontx.TinySelf
import Legacy.Riscv.Frontx.TinySmall
open Proven Proven.Frontx Proven.Frontx.Tiny
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
-- tiny programs (op, arg) pairs
def P1 : List UInt8 := [5,0, 6,9, 2,0, 1,0x55, 3,0, 7,0, 8,0, 9,0, 5,0, 4,0xF9]  -- xor every input byte with 0x55
def P2 : List UInt8 := [5,0, 3,0, 8,0]                                          -- output the length (mod 256)
def P3 : List UInt8 := [5,0, 6,9, 2,0, 0,1, 3,0, 7,0, 8,0, 9,0, 5,0, 4,0xF9]    -- input bytes + 1
def P4 : List UInt8 := [5,0, 6,5, 3,0, 8,0, 0,0xFF, 4,0xFD]                    -- n, n-1, .., 1
def P5 : List UInt8 := [5,0, 6,10, 2,0, 4,2, 0,0x80, 3,0, 7,0, 8,0, 9,0, 5,0, 4,0xF8] -- P1-like, JNZ skips an ADDI
def progs : List (List UInt8) := [P1, P2, P3, P4, P5]
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def inputs : List (List UInt8) := [[], [0], [1, 2, 3], [255, 0, 7, 128], "hello, world".toUTF8.data.toList] ++
  (List.range 12).map fun i => (List.range (rnd i 5 % 200)).map fun j => UInt8.ofNat (rnd i j % 256)
-- random byte strings as programs for the compiler-vs-compiler comparison (tinyCompile is total)
def junk : List (List UInt8) := (List.range 40).map fun i => (List.range (rnd i 11 % 60)).map fun j => UInt8.ofNat (rnd i j % (if i % 2 == 0 then 8 else 256))
#eval do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile "Testing/asm/frontx-words/tinycompile.cases"
    (String.join ((progs ++ junk ++ [[], [4]]).map fun p => s!"{hx p} {hx (tinyCompile ⟨p.toArray⟩)}\n"))
  IO.FS.writeFile "Testing/asm/tiny/run.cases"
    (String.join ((progs.flatMap fun p => inputs.map fun i => s!"{hx p} {hx i} {hx (tinyRun p i)} {hx (tinyCompile ⟨p.toArray⟩)}\n")))
#eval do
  IO.FS.writeFile "Testing/asm/frontx-words/tinycompile.words"
    (String.intercalate "\n" (toString tinyCompile.slots :: tinyCompile.code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
-- the 12-slot subset (TinySmall): same cases, its own words file
open Proven.Frontx.TinySm in
#eval do
  IO.FS.writeFile "Testing/asm/frontx-words/tinysm.words"
    (String.intercalate "\n" (toString tinySm.slots :: tinySm.code.map fun w =>
      let s := String.ofList (Nat.toDigits 16 (BitVec.toNat w)); "".pushn '0' (8 - s.length) ++ s) ++ "\n")
  IO.FS.writeFile "Testing/asm/frontx-words/tinysm.cases"
    (String.join ((progs ++ junk ++ [[], [4]]).map fun p => s!"{hx p} {hx (tinySm ⟨p.toArray⟩)}\n"))

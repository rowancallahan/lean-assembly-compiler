/- Words and cases of the list-front-end entry points with multiply / divide (`Riscv/Frontx/MulExamples.lean`,
NOTES section 22) for `frontx_test.py` (`fx_<name>.words`: first line the slots, `fx_<name>.cases`).
Run: `lake env lean --tstack=400000 Testing/asm/emit_mul.lean`. -/
import Legacy.Riscv.Frontx.MulExamples
open Proven Proven.Frontx Proven.Frontx.Mul
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def le64 (n : Nat) : List UInt8 := (List.range 8).map fun j => UInt8.ofNat (n / 256 ^ j % 256)
/-- two 64-bit words: divisor `0`, `1`, large, `2^63`, `2^64 - 1`, equal, shift amounts around 32 / 64, then random
(some with small divisors), and short inputs (missing bytes read as `0`) -/
def inputs : List (List UInt8) :=
  [[], [5], [0, 0, 0, 0, 0, 0, 0, 0, 7]] ++
  ([(0, 0), (7, 0), (2^64 - 1, 0), (2^64 - 1, 1), (2^64 - 1, 2^64 - 1), (2^63, 3), (2^63, 2^63), (12345, 63),
    (12345, 64), (12345, 65), (2^32 + 5, 31), (2^32 + 5, 32), (1836311903, 1134903170), (1134903170, 1836311903),
    (2^62, 2^31 - 1), (100, 7)] ++
   (List.range 34).map fun i => (rnd i 3, if i % 3 = 0 then rnd i 5 % 1000 else rnd i 5)).map
    fun (a, b) => le64 a ++ le64 b
def emit (name : String) (slots : Nat) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval emit "fx_ops64" ops64E.slots ops64E.code (enc ops64E)
#eval emit "fx_ops32" ops32E.slots ops32E.code (enc ops32E)
#eval emit "fx_opsn" opsNE.slots opsNE.code (enc opsNE)
#eval emit "fx_gcd" gcdE.slots gcdE.code (enc gcdE)

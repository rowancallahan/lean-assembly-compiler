/- Words and cases of the BookS4 entry points (`Riscv/Frontx/BookS4.lean`, BOOK_S4.md) for `frontx_test.py`
(`s4_<name>.words`: first line the slots, `s4_<name>.cases`: input, result bytes computed by Lean).
Run: `lake env lean --tstack=400000 Testing/asm/emit_s4.lean`. -/
import Riscv.Frontx.BookS4
open Proven Proven.Frontx Proven.Frontx.IntEx Proven.Frontx.BookS4
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
/-- 8 bytes little-endian, two's complement -/
def le64 (x : Int) : List UInt8 := (List.range 8).map fun j => UInt8.ofNat ((x % 2 ^ 64).toNat / 256 ^ j % 256)
/-- the `Int` range edges (`isEven` needs `-2^63 ≤ i < 2^63`), then pseudo-random values -/
def edges : List Int := [0, 1, -1, 2, -2, 3, -3, 4, 127, 128, -128, 255, 256, -255, 2^31 - 1, -2^31, 2^32 + 1,
  2^63 - 1, -2^63, 2^63 - 2, -2^63 + 1, 1073741825, -1073741823]
def rnd (i : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + i * i * 0xD1B54A32D192ED03) % 2^64
def rndI (i : Nat) : Int := let w := rnd i; if w < 2 ^ 63 then w else (w : Int) - 2 ^ 64
def inputs : List (List UInt8) :=
  [[]] ++ edges.map le64 ++ (List.range 40).map fun i => le64 (rndI i)
def emit (name : String) (slots : Nat) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval emit "s4_iseven" isEvenE.slots isEvenE.code (enc isEvenE)

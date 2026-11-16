/- Words and cases of the lean-zip rows in `Riscv/Frontx/ZipS2.lean` (list front end) for `frontx_test.py`
(`frontx-words/<name>.words` / `.cases`, the first line = slots).  Run: `lake env lean --tstack=400000 Testing/asm/emit_zip2.lean`. -/
import Riscv.Frontx.ZipS2
open Proven Proven.Frontx Proven.Frontx.ZipS2
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def inputs : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7], "123456789".toUTF8.data.toList,
   "The quick brown fox\njumps over the lazy dog".toUTF8.data.toList, List.replicate 64 255] ++
  (List.range 40).map fun i =>
    let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
    (List.range L).map fun j => UInt8.ofNat (match i % 4 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
def emitF (name : String) (hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval emitF "zip2_adler" (toString adlerE.slots) adlerE.code (enc adlerE)

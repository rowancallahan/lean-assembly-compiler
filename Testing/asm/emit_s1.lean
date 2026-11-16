/- Words and cases of the word-array entry points (`Riscv/Frontx/WaLeanZip.lean`, NOTES section 20) for
`frontx_test.py`: `wa_<name>.words` (first line `wa A N B L`: `8 (A + B n) + 8 (N + 1) + 7` work bytes, `L = 1`:
byte-list result with its length in `a1`), `wa_<name>.cases` (input, result bytes computed by Lean).
Run: `lake env lean --tstack=400000 Testing/asm/emit_wa.lean`. -/
import Riscv.Frontx.ZipS1
open Proven Proven.WA Proven.WA.ZipS1
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def inputs : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7], "123456789".toUTF8.data.toList,
   "The quick brown fox\njumps over the lazy dog".toUTF8.data.toList, List.replicate 64 255,
   -- section 22: divisor 0, large operands, 2^63, 2^32 - 1 (words at bytes 0 and 4 / 0 and 8)
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [255, 255, 255, 255, 255, 255, 255, 255, 3, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 128, 255, 255, 255, 255, 255, 255, 255, 127],
   [255, 255, 255, 255, 1, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0], [60, 0, 0, 0, 255, 255, 255, 255]] ++
  (List.range 40).map fun i =>
    let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
    (List.range L).map fun j => UInt8.ofNat (match i % 5 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | 3 => rnd i j % 17 | _ => 255 - rnd i j % 5)
def emit (name : String) (hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/wa_{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/wa_{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
#eval emit "s1countlengths" s!"wa {wholeW s1countlengths.wa [inLoc]} {wholeNA s1countlengths.wa} 0 1" s1countlengths.code
  (fun xs => encArr (.arr .nat) (s1countlengths xs))
#eval emit "s1kraft" s!"wa {wholeW s1kraft.wa [inLoc]} {wholeN s1kraft.wa 7} 0 0" s1kraft.code
  (fun xs => Frontx.Res.enc (s1kraft xs))
#eval emit "s1nextcodes" s!"wa {wholeW s1nextcodes.wa [inLoc]} {wholeNA s1nextcodes.wa} 0 1" s1nextcodes.code
  (fun xs => encArr (.arr .u32) (s1nextcodes xs))

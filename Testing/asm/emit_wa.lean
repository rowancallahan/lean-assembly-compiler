/- Words and cases of the word-array entry points (`Riscv/Frontx/WaLeanZip.lean`, NOTES section 20) for
`frontx_test.py`: `wa_<name>.words` (first line `wa A N B L`: `8 (A + B n) + 8 (N + 1) + 7` work bytes, `L = 1`:
byte-list result with its length in `a1`), `wa_<name>.cases` (input, result bytes computed by Lean).
Run: `lake env lean --tstack=400000 Testing/asm/emit_wa.lean`. -/
import Legacy.Riscv.Frontx.WaMul
import Legacy.Riscv.Frontx.MixHash
open Proven Proven.WA Proven.WA.LeanZip
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
#eval emit "crc32" s!"wa {wholeW crc32E.wa [inLoc]} {wholeN crc32E.wa 3} 0 0" crc32E.code
  (fun xs => Frontx.Res.enc (crc32E xs))
#eval emit "crcupdate" s!"wa {wholeW crcUpdateE.wa [inLoc]} {wholeN crcUpdateE.wa 3} 0 0" crcUpdateE.code
  (fun xs => Frontx.Res.enc (crcUpdateE xs))
#eval emit "countlengths" s!"wa {wholeW countLengthsE.wa [inLoc]} {wholeNA countLengthsE.wa} 0 1" countLengthsE.code
  (fun xs => encArr (.arr .nat) (countLengthsE xs))
#eval emit "countlengths7" s!"wa {wholeW countLengths7E.wa [inLoc]} {wholeNA countLengths7E.wa} 0 1"
  countLengths7E.code (fun xs => encArr (.arr .nat) (countLengths7E xs))
-- NOTES section 22 (multiply / divide / remainder / variable shifts, `Riscv/Frontx/WaMul.lean`)
#eval emit "gcd" s!"wa {wholeW Core.gcdE.wa [inLoc]} {wholeN Core.gcdE.wa 7} 0 0" Core.gcdE.code
  (fun xs => Frontx.Res.enc (Core.gcdE xs))
#eval emit "kraft" s!"wa {wholeW kraftE.wa [inLoc]} {wholeN kraftE.wa 7} 0 0" kraftE.code
  (fun xs => Frontx.Res.enc (kraftE xs))
#eval emit "nextcodes" s!"wa {wholeW nextCodesE.wa [inLoc]} {wholeNA nextCodesE.wa} 0 1" nextCodesE.code
  (fun xs => encArr (.arr .u32) (nextCodesE xs))
#eval emit "ops64" s!"wa {wholeW Ops.ops64E.wa [inLoc]} {wholeN Ops.ops64E.wa 7} 0 0" Ops.ops64E.code
  (fun xs => Frontx.Res.enc (Ops.ops64E xs))
#eval emit "ops32" s!"wa {wholeW Ops.ops32E.wa [inLoc]} {wholeN Ops.ops32E.wa 3} 0 0" Ops.ops32E.code
  (fun xs => Frontx.Res.enc (Ops.ops32E xs))
#eval emit "opsn" s!"wa {wholeW Ops.opsNE.wa [inLoc]} {wholeN Ops.opsNE.wa 7} 0 0" Ops.opsNE.code
  (fun xs => Frontx.Res.enc (Ops.opsNE xs))
-- mixHash port (`Riscv/Frontx/MixHash.lean`): 16-byte inputs (h, k little-endian), 25 edge pairs + 40 random pairs
open Proven.WA.MixHash
def mixLe8 (x : UInt64) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (x.toNat / 2 ^ (8 * i) % 256)
def mixInputs : List (List UInt8) :=
  let edges : List UInt64 := [0, 1, 9223372036854775808, 18446744073709551615, 0xc6a4a7935bd1e995]
  (edges.flatMap fun h => edges.map fun k => mixLe8 h ++ mixLe8 k) ++
    (List.range 40).map fun i => mixLe8 (UInt64.ofNat (rnd i 1)) ++ mixLe8 (UInt64.ofNat (rnd i 2))
def emitIn (name hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8) (ins : List (List UInt8)) :
    IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/wa_{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/wa_{name}.cases"
    (String.join (ins.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
#eval emitIn "mixhash" s!"wa {wholeW mixHashE.wa [inLoc]} {wholeN mixHashE.wa 7} 0 0" mixHashE.code
  (fun xs => Frontx.Res.enc (mixHashE xs)) mixInputs

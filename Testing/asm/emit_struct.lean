/- Words and cases of the structure entry points (NOTES section 32: `Riscv/Frontx/StructExamples.lean`,
`Riscv/Frontx/WaStruct.lean`) for `frontx_test.py` (`frontx-words/<name>.words` / `.cases`, see `emit_frontx.lean`
and `emit_wa.lean`).  Run: `lake env lean --tstack=400000 Testing/asm/emit_struct.lean`. -/
import Legacy.Riscv.Frontx.StructExamples
import Legacy.Riscv.Frontx.WaStruct
open Proven Proven.Frontx Proven.Frontx.Structs Proven.WA Proven.WA.Struct
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- fixed inputs, then pseudo-random ones (some up to 3000 bytes) -/
def inputs : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7], "123456789".toUTF8.data.toList,
   "The quick brown fox\njumps over the lazy dog".toUTF8.data.toList, List.replicate 64 255,
   [255, 0, 1, 1, 1, 0, 0, 0], [128, 128, 0, 1, 255, 255, 255, 1, 7, 15, 3]] ++
  (List.range 40).map fun i =>
    let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
    (List.range L).map fun j => UInt8.ofNat (match i % 5 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | 3 => rnd i j % 2 | _ => 255 - rnd i j % 5)
def emitF (name : String) (hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
-- list front end (first line: slots)
#eval do
  emitF "st_rgba" (toString rgbaE.slots) rgbaE.code (fun xs => rgbaE.enc (rgbaE xs))
  emitF "st_hdr" (toString hdrE.slots) hdrE.code (fun xs => hdrE.enc (hdrE xs))
  emitF "st_rgbag" (toString rgbaGE.slots) rgbaGE.code (enc rgbaGE)
  emitF "st_interlace" (toString interlaceE.slots) interlaceE.code (enc interlaceE)
  emitF "st_canvash" (toString canvasHE.slots) canvasHE.code (enc canvasHE)
  emitF "st_compoundvalid" (toString compoundValidE.slots) compoundValidE.code (enc compoundValidE)
  emitF "st_setlig" (toString setLigE.slots) setLigE.code (fun xs => setLigE.enc (setLigE xs))
  emitF "st_lignumcomps" (toString ligNumCompsE.slots) ligNumCompsE.code (enc ligNumCompsE)
  emitF "st_isignorable" (toString isIgnorableE.slots) isIgnorableE.code (enc isIgnorableE)
  emitF "st_rgbahdr" (toString rgbaHdrE.slots) rgbaHdrE.code (fun xs => rgbaHdrE.enc (rgbaHdrE xs))
-- word-array front end (first line: `wa A N B L`)
#eval emitF "wa_entryat" s!"wa {wholeW entryAtE.wa [inLoc]} {wholeN entryAtE.wa 3} 0 0" entryAtE.code (enc entryAtE)
#eval emitF "wa_lenat" s!"wa {wholeW lenAtE.wa [inLoc]} {wholeN lenAtE.wa 0} 0 0" lenAtE.code (enc lenAtE)
#eval emitF "wa_symat" s!"wa {wholeW symAtE.wa [inLoc]} {wholeN symAtE.wa 1} 0 0" symAtE.code (enc symAtE)

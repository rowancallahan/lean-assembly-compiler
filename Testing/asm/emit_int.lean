/- Words and cases of the `Int` entry points (`Riscv/Frontx/IntExamples.lean`, NOTES section 26) for
`frontx_test.py` (`int_<name>.words`: first line the slots, `int_<name>.cases`: input, result bytes computed by Lean).
Run: `lake env lean --tstack=400000 Testing/asm/emit_int.lean`. -/
import Legacy.Riscv.Frontx.IntExamples
import Legacy.Riscv.Frontx.WaInt
open Proven Proven.Frontx Proven.Frontx.IntEx
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- 8 bytes little-endian, two's complement -/
def le64 (x : Int) : List UInt8 := (List.range 8).map fun j => UInt8.ofNat ((x % 2 ^ 64).toNat / 256 ^ j % 256)
/-- edge values: `0`, `±1`, the 8- / 16- / 31- / 32-bit and 63-bit boundaries, `Fx.maxVal` and `linMax` with neighbours,
multiples of 256 and halves, then random words (all 64 bits, and reduced to 32 and 17 bits) -/
def edges : List Int :=
  [0, 1, -1, 2, -2, 127, 128, 255, 256, -256, -255, 257, 383, 384, -128, -129, 32767, 32768, -32768, -32769,
   65535, 65536, 2^31 - 1, -2^31, 2^31, 2^32 - 1, 2^63 - 1, -2^63, 1073741824, 1073741825, -1073741824,
   -1073741825, 268435456, 268435457, -268435457, 2^30 * 3, -(2^40) - 5]
def rndI (i j : Nat) : Int := let w := rnd i j; if w < 2 ^ 63 then w else (w : Int) - 2 ^ 64
def inputs : List (List UInt8) :=
  [[], [5], [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 7]] ++
  (edges.zip (edges.reverse)).map (fun (a, b) => le64 a ++ le64 b) ++
  (List.range 30).map fun i =>
    let a := rndI i 3; let b := rndI i 5
    let (a, b) := if i % 3 = 0 then (a % 2 ^ 32, b % 2 ^ 17) else if i % 3 = 1 then (a % 2 ^ 20 - 2 ^ 19, b % 300 - 150) else (a, b)
    le64 a ++ le64 b
def emit (name : String) (slots : Nat) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval IO.println s!"{inputs.length} inputs"
#eval emit "int_clamp" clampE.slots clampE.code (enc clampE)
#eval emit "int_inrange" inRangeE.slots inRangeE.code (enc inRangeE)
#eval emit "int_ofnat" ofNatE.slots ofNatE.code (enc ofNatE)
#eval emit "int_mul" mulE.slots mulE.code (enc mulE)
#eval emit "int_floor" floorE.slots floorE.code (enc floorE)
#eval emit "int_ceil" ceilE.slots ceilE.code (enc ceilE)
#eval emit "int_round" roundE.slots roundE.code (enc roundE)
#eval emit "int_abs" absE.slots absE.code (enc absE)
#eval emit "int_min" minE.slots minE.code (enc minE)
#eval emit "int_max" maxE.slots maxE.code (enc maxE)
#eval emit "int_scale16" scale16E.slots scale16E.code (enc scale16E)
#eval emit "int_clamplin" clampLinE.slots clampLinE.code (enc clampLinE)
#eval emit "int_lininrange" linInRangeE.slots linInRangeE.code (enc linInRangeE)
#eval emit "int_clampix" clampIxE.slots clampIxE.code (enc clampIxE)
#eval emit "int_round32" round32E.slots round32E.code (enc round32E)
#eval emit "int_fitsi16" fitsI16E.slots fitsI16E.code (enc fitsI16E)
#eval emit "int_insidew" insideWE.slots insideWE.code (enc insideWE)
#eval emit "int_norm2" norm2E.slots norm2E.code (enc norm2E)
#eval emit "int_clampto" clampToE.slots clampToE.code (enc clampToE)
#eval emit "int_morphceil" morphCeilE.slots morphCeilE.code (enc morphCeilE)
-- word arrays (`Riscv/Frontx/WaInt.lean`): header `wa A N B L` as `emit_wa.lean`
def emitW (name : String) (hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
#eval emitW "wa_int_iops" s!"wa {WA.wholeW WA.IntOps.iopsE.wa [WA.inLoc]} {WA.wholeN WA.IntOps.iopsE.wa 7} 0 0"
  WA.IntOps.iopsE.code (fun xs => Res.enc (WA.IntOps.iopsE xs))
#eval emitW "wa_int_icmp" s!"wa {WA.wholeW WA.IntOps.icmpE.wa [WA.inLoc]} {WA.wholeN WA.IntOps.icmpE.wa 7} 0 0"
  WA.IntOps.icmpE.code (fun xs => Res.enc (WA.IntOps.icmpE xs))
#eval emitW "wa_int_fxrounds" s!"wa {WA.wholeW WA.IntOps.fxRoundsE.wa [WA.inLoc]} {WA.wholeN WA.IntOps.fxRoundsE.wa 7} 0 0"
  WA.IntOps.fxRoundsE.code (fun xs => Res.enc (WA.IntOps.fxRoundsE xs))
#eval emitW "wa_int_sumdev" s!"wa {WA.wholeW WA.IntOps.sumDevE.wa [WA.inLoc]} {WA.wholeN WA.IntOps.sumDevE.wa 7} 0 0"
  WA.IntOps.sumDevE.code (fun xs => Res.enc (WA.IntOps.sumDevE xs))

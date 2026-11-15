/- lean-svg leaf functions, copied VERBATIM (rowancallahan/lean-svg @ df8e663), each from `file:line`.
   Nothing is restated.  Lean-version API edits: none unless listed in `Testing/notes/LEANSVG_VERBATIM.md`.
   Each `frontx_compile` / `frontx_implements` line is the unmodified front end on the unmodified definition. -/
import Riscv.Frontx.Translate
import Riscv.Frontx.Impl1


/-! ### at': LeanSvg/Bytes.lean:15@df8e663 -/
namespace LeanSvg.Bytes
@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0
end LeanSvg.Bytes

/-! ### isWs: LeanSvg/Bytes.lean:18@df8e663 -/
namespace LeanSvg.Bytes
@[inline] def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13
end LeanSvg.Bytes

/-! ### isDigit: LeanSvg/Bytes.lean:19@df8e663 -/
namespace LeanSvg.Bytes
@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
end LeanSvg.Bytes

/-! ### div255: LeanSvg/Canvas.lean:38@df8e663 -/
namespace LeanSvg.Canvas
@[inline] def div255 (x : Nat) : Nat := (x + 255) >>> 8
end LeanSvg.Canvas

/-! ### premul: LeanSvg/Canvas.lean:47@df8e663 -/
namespace LeanSvg.Canvas
@[inline] def premul (c a : Nat) : Nat := (c * a + 127) / 255
end LeanSvg.Canvas

/-! ### unpremul: LeanSvg/Canvas.lean:55@df8e663 -/
namespace LeanSvg.Canvas
@[inline] def unpremul (c a : Nat) : Nat :=
  if a == 0 then 0 else Nat.min 255 ((c * 510 + a) / (2 * a))
end LeanSvg.Canvas

/-! ### pack: LeanSvg/Canvas.lean:68@df8e663 -/
namespace LeanSvg.Canvas
@[inline] def pack (r g b a : Nat) : Nat :=
  (r * 16777216) ||| (g * 65536) ||| (b * 256) ||| a
end LeanSvg.Canvas

/-! ### premulU8: LeanSvg/Image.lean:236@df8e663 -/
namespace LeanSvg.Image
@[inline] def premulU8 (c a : Nat) : Nat :=
  let p := c * a + 128
  (p + (p >>> 8)) >>> 8
end LeanSvg.Image

/-! ### b64Val: LeanSvg/Image.lean:93@df8e663 -/
namespace LeanSvg.Image
@[inline] def b64Val (c : UInt8) : Nat :=
  if 65 ≤ c && c ≤ 90 then c.toNat - 65
  else if 97 ≤ c && c ≤ 122 then c.toNat - 71
  else if 48 ≤ c && c ≤ 57 then c.toNat + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 64
end LeanSvg.Image

/-! ### Fx: LeanSvg/Fixed.lean:17@df8e663 -/
namespace LeanSvg
abbrev Fx := Int
end LeanSvg

/-! ### one: LeanSvg/Fixed.lean:21@df8e663 -/
namespace LeanSvg.Fx
def one : Fx := 256
end LeanSvg.Fx

/-! ### maxVal: LeanSvg/Fixed.lean:25@df8e663 -/
namespace LeanSvg.Fx
def maxVal : Fx := 1073741824
end LeanSvg.Fx

/-! ### clamp: LeanSvg/Fixed.lean:27@df8e663 -/
namespace LeanSvg.Fx
def clamp (a : Fx) : Fx :=
  if a > maxVal then maxVal else if a < -maxVal then -maxVal else a
end LeanSvg.Fx

/-! ### floor: LeanSvg/Fixed.lean:38@df8e663 -/
namespace LeanSvg.Fx
def floor (a : Fx) : Int := Int.ediv a 256
end LeanSvg.Fx

/-! ### round: LeanSvg/Fixed.lean:40@df8e663 -/
namespace LeanSvg.Fx
def round (a : Fx) : Int := Int.ediv (a + 128) 256
end LeanSvg.Fx

/-! ### abs: LeanSvg/Fixed.lean:41@df8e663 -/
namespace LeanSvg.Fx
def abs (a : Fx) : Fx := if a < 0 then -a else a
end LeanSvg.Fx

/-! ### toFDot6: LeanSvg/Raster.lean:531@df8e663 -/
namespace LeanSvg.Raster
@[inline] def toFDot6 (a : Fx) : Int := Int.tdiv a 4
end LeanSvg.Raster

/-! ### divRound: LeanSvg/Raster.lean:534@df8e663 -/
namespace LeanSvg.Raster
@[inline] def divRound (n d : Int) : Int :=
  if d ≤ 0 then 0
  else if n ≥ 0 then Int.ediv (2 * n + d) (2 * d)
  else -(Int.ediv (2 * (-n) + d) (2 * d))
end LeanSvg.Raster

/-! ### paeth: LeanSvg/PngDecode.lean:142@df8e663 -/
namespace LeanSvg.PngDecode
@[inline] def paeth (a b c : Nat) : Nat :=
  let pa := if b ≥ c then b - c else c - b
  let pb := if a ≥ c then a - c else c - a
  let pc := if a + b ≥ 2 * c then a + b - 2 * c else 2 * c - (a + b)
  if pa ≤ pb && pa ≤ pc then a else if pb ≤ pc then b else c
end LeanSvg.PngDecode

/-! ### to8: LeanSvg/PngDecode.lean:226@df8e663 -/
namespace LeanSvg.PngDecode
@[inline] def to8 (d v : Nat) : UInt8 :=
  if d == 16 then (v >>> 8).toUInt8
  else if d == 8 then v.toUInt8
  else (v * (255 / ((1 <<< d) - 1))).toUInt8
end LeanSvg.PngDecode

/-! ### utf8Len: LeanSvg/ShapeText.lean:63@df8e663 -/
namespace LeanSvg.ShapeText
def utf8Len (cp : Nat) : Nat := if cp < 0x80 then 1 else if cp < 0x800 then 2 else if cp < 0x10000 then 3 else 4
end LeanSvg.ShapeText

/-! ### hexVal: LeanSvg/Svg.lean:690@df8e663 -/
namespace LeanSvg.Svg
open LeanSvg.Bytes   -- context: Svg.lean opens Bytes (not part of the definition)
def hexVal (c : UInt8) : Option Nat :=
  if isDigit c then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none
end LeanSvg.Svg

/-! ### roundDiv14: LeanSvg/Font.lean:134@df8e663 -/
namespace LeanSvg.Font
@[inline] def roundDiv14 (n : Int) : Int := Int.ediv (n + 8192) 16384
end LeanSvg.Font

/-! ### fmtFixed: LeanSvg/Use.lean:151@df8e663 -/
namespace LeanSvg.Use
def fmtFixed (v : Int) (bits : Nat) : String :=
  let a := v.natAbs
  let digits := toString ((a % 2 ^ bits) * 5 ^ bits)
  (if v < 0 then "-" else "") ++ toString (a / 2 ^ bits) ++ "." ++
    String.ofList (List.replicate (bits - digits.length) '0') ++ digits
end LeanSvg.Use

/-! ### degToRad16: LeanSvg/Geom.lean:34@df8e663 -/
namespace LeanSvg
def degToRad16 (deg : Fx) : Int :=
  let d := Int.emod deg (360 * 256)
  Int.ediv (d * 205887) 46080
end LeanSvg

/-! ## The unmodified front end on each definition (`frontx_compile`; an error line below is the rejection) -/
-- div255
frontx_compile LeanSvg.Canvas.div255
-- premul
frontx_compile LeanSvg.Canvas.premul
-- unpremul
frontx_compile LeanSvg.Canvas.unpremul
-- pack
frontx_compile LeanSvg.Canvas.pack
-- premulU8
frontx_compile LeanSvg.Image.premulU8
-- b64Val
frontx_compile LeanSvg.Image.b64Val
-- hexVal
frontx_compile LeanSvg.Svg.hexVal
-- Fx.clamp
frontx_compile LeanSvg.Fx.clamp
-- Fx.floor
frontx_compile LeanSvg.Fx.floor
-- Fx.round
frontx_compile LeanSvg.Fx.round
-- Fx.abs
frontx_compile LeanSvg.Fx.abs
-- toFDot6
frontx_compile LeanSvg.Raster.toFDot6
-- divRound
frontx_compile LeanSvg.Raster.divRound
-- paeth
frontx_compile LeanSvg.PngDecode.paeth
-- to8
frontx_compile LeanSvg.PngDecode.to8
-- utf8Len
frontx_compile LeanSvg.ShapeText.utf8Len
-- roundDiv14
frontx_compile LeanSvg.Font.roundDiv14
-- degToRad16
frontx_compile LeanSvg.degToRad16
-- fmtFixed
frontx_compile LeanSvg.Use.fmtFixed
-- isWs
frontx_compile LeanSvg.Bytes.isWs
-- isDigit
frontx_compile LeanSvg.Bytes.isDigit
-- at'
frontx_compile LeanSvg.Bytes.at'

/-! (Tried and not kept: `At.hexVal` = `match Svg.hexVal c with …` — `frontx: unsupported Bool` (a `match` on the Option result of a call);
`At.utf8Len` with a 3-byte argument — `(deterministic) timeout at whnf` even at 2000000 heartbeats.  Their leaves are compiled above; only the machine entry is missing.) -/

/-! ## Entry points (new code, only to give the machine theorem a `ByteArray` input; the leaf is called unmodified).
As in `BookExamples.lean`: `At.f xs i` calls the leaf on bytes read at `i` and is compiled by `frontx_compile`;
`Entry.f xs := At.f xs 0` is the entry point. -/
namespace LeanSvg.At
open LeanSvg LeanSvg.Bytes
def b64Val (xs : ByteArray) (i : Nat) : Nat := Image.b64Val (at' xs i)
def hexVal (xs : ByteArray) (i : Nat) : Nat := match Svg.hexVal (at' xs i) with | none => 255 | some v => v
def utf8Len (xs : ByteArray) (i : Nat) : Nat := ShapeText.utf8Len ((at' xs i).toNat + 256 * (at' xs (i + 1)).toNat + 65536 * (at' xs (i + 2)).toNat)
def isWs (xs : ByteArray) (i : Nat) : Bool := Bytes.isWs (at' xs i)
def isDigit (xs : ByteArray) (i : Nat) : Bool := Bytes.isDigit (at' xs i)
def pack (xs : ByteArray) (i : Nat) : Nat := Canvas.pack (at' xs i).toNat (at' xs (i + 1)).toNat (at' xs (i + 2)).toNat (at' xs (i + 3)).toNat
end LeanSvg.At
open Proven Proven.Frontx in
frontx_compile LeanSvg.At.b64Val requires fun _ i => i + 8 < 2 ^ 64
open Proven Proven.Frontx in
frontx_compile LeanSvg.At.isWs requires fun _ i => i + 8 < 2 ^ 64
open Proven Proven.Frontx in
frontx_compile LeanSvg.At.isDigit requires fun _ i => i + 8 < 2 ^ 64
open Proven Proven.Frontx in
frontx_compile LeanSvg.At.pack requires fun _ i => i + 8 < 2 ^ 64
namespace LeanSvg.Entry
open LeanSvg LeanSvg.Bytes
def b64Val (xs : ByteArray) : Nat := At.b64Val xs 0
def isWs (xs : ByteArray) : Bool := At.isWs xs 0
def isDigit (xs : ByteArray) : Bool := At.isDigit xs 0
def at3 (xs : ByteArray) : UInt8 := at' xs 3
def pack (xs : ByteArray) : Nat := At.pack xs 0
end LeanSvg.Entry
open Proven Proven.Frontx in
frontx_entry LeanSvg.Entry.b64Val
open Proven Proven.Frontx in
frontx_implements LeanSvg.Entry.b64Val
open Proven Proven.Frontx in
frontx_entry LeanSvg.Entry.isWs
open Proven Proven.Frontx in
frontx_implements LeanSvg.Entry.isWs
open Proven Proven.Frontx in
frontx_entry LeanSvg.Entry.isDigit
open Proven Proven.Frontx in
frontx_implements LeanSvg.Entry.isDigit
open Proven Proven.Frontx in
frontx_entry LeanSvg.Entry.at3
open Proven Proven.Frontx in
frontx_implements LeanSvg.Entry.at3
open Proven Proven.Frontx in
frontx_entry LeanSvg.Entry.pack
open Proven Proven.Frontx in
frontx_implements LeanSvg.Entry.pack

/-! ## Executed-Lean cases (frontx-words `.cases` format: `input-hex result-hex` per line)

The input bytes encode the arguments of the verbatim function: `Nat` as 16-bit LE (`byte` where the argument is a
channel), `Int` as 32-bit two's complement LE, `UInt8` as one byte, `UInt8`-bytes of `at'` as the array.
Result: `Nat` = 8 bytes LE, `Int` = 8 bytes two's complement LE, `UInt8` = 1 byte, `Bool` = 1 byte,
`Option Nat` = tag byte ++ 8 bytes LE (0 for `none`), `String` = its UTF-8 bytes (length implied). Computed by
`#eval` of the unmodified definitions (interpreter). -/
namespace LeanSvg.Cases
open LeanSvg LeanSvg.Canvas LeanSvg.Image LeanSvg.Raster LeanSvg.PngDecode LeanSvg.ShapeText LeanSvg.Svg LeanSvg.Font LeanSvg.Use
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def le (n w : Nat) : List UInt8 := (List.range w).map fun i => UInt8.ofNat (n / 256 ^ i % 256)
def eN (n : Nat) : List UInt8 := le n 8
def eI (i : Int) : List UInt8 := le (i % 2 ^ 64).toNat 8
def iN (n : Nat) (w : Nat) : List UInt8 := le n w
def iI (i : Int) : List UInt8 := le (i % 2 ^ 32).toNat 4
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2 ^ 64
def rs (n : Nat) (m : Nat) (k : Nat) : List Nat := (List.range n).map fun i => rnd i k % m
def ri (n : Nat) (m : Nat) (k : Nat) : List Int := (List.range n).map fun i => (rnd i k % (2 * m) : Nat) - (m : Int)
def emitC (name : String) (cs : List (List UInt8 × List UInt8)) : IO Unit := do
  IO.FS.createDirAll "Testing/leansvg/cases"
  IO.FS.writeFile s!"Testing/leansvg/cases/{name}.cases" (String.join (cs.map fun (a, r) => s!"{hx a} {hx r}\n"))
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
/-- cases of an entry point: assert that the `.cases` result equals `Res.enc (entry xs)`, then write `.words` too -/
def emitE {β : Type} [Proven.Frontx.Res β] (name : String) (slots : Nat) (code : List (BitVec 32)) (e : ByteArray → β)
    (cs : List (List UInt8 × List UInt8)) : IO Unit := do
  for (a, r) in cs do
    unless Proven.Frontx.Res.enc (e ⟨a.toArray⟩) = r do throw (IO.userError s!"{name}: case {hx a} disagrees with the entry point")
  IO.FS.createDirAll "Testing/leansvg/words"
  IO.FS.writeFile s!"Testing/leansvg/words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  emitC name cs
def n1 (f : Nat → Nat) (xs : List Nat) := xs.map fun a => (iN a 2, eN (f a))
def n2 (f : Nat → Nat → Nat) (xs : List Nat) (ys : List Nat) := (xs.zip ys).map fun (a, b) => (iN a 2 ++ iN b 2, eN (f a b))
def edge : List Nat := [0, 1, 2, 127, 128, 254, 255, 256, 257, 4095, 65535]
def edge8 : List Nat := [0, 1, 2, 127, 128, 254, 255]
def charIn : List Nat := (List.range 256)
#eval emitC "div255" (n1 div255 (edge ++ rs 40 65536 1))
#eval emitC "premul" (n2 premul (edge8 ++ rs 40 256 2) (edge8.reverse ++ rs 40 256 3))
#eval emitC "unpremul" (n2 unpremul (edge8 ++ rs 40 256 4) (edge8.reverse ++ rs 40 256 5))
#eval emitE "pack" LeanSvg.Entry.pack.slots LeanSvg.Entry.pack.code LeanSvg.Entry.pack ((rs 50 256 6).zip ((rs 50 256 7).zip ((rs 50 256 8).zip (rs 50 256 9))) |>.map fun (r, g, b, a) =>
  (iN r 1 ++ iN g 1 ++ iN b 1 ++ iN a 1, eN (pack r g b a)))
#eval emitC "premulU8" (n2 premulU8 (edge8 ++ rs 40 256 10) (edge8.reverse ++ rs 40 256 11))
#eval emitE "b64Val" LeanSvg.Entry.b64Val.slots LeanSvg.Entry.b64Val.code LeanSvg.Entry.b64Val (charIn.map fun c => ([UInt8.ofNat c], eN (b64Val (UInt8.ofNat c))))
#eval emitC "hexVal" (charIn.map fun c => ([UInt8.ofNat c], match hexVal (UInt8.ofNat c) with | none => eN 255 | some v => eN v))
def fxIn : List Int := [0, 1, -1, 255, 256, -256, 1073741823, 1073741824, 1073741825, -1073741824, -1073741825, 2147483647, -2147483648] ++ ri 40 1100000000 12
def i1 (f : Int → Int) := fxIn.map fun a => (iI a, eI (f a))
#eval emitC "Fx.clamp" (i1 Fx.clamp)
#eval emitC "Fx.floor" (i1 Fx.floor)
#eval emitC "Fx.round" (i1 Fx.round)
#eval emitC "Fx.abs" (i1 Fx.abs)
#eval emitC "toFDot6" (i1 toFDot6)
#eval emitC "roundDiv14" (i1 roundDiv14)
#eval emitC "degToRad16" (i1 degToRad16)
#eval emitC "divRound" ((fxIn.zip (fxIn.reverse ++ ri 40 1000 13)).map fun (n, d) => (iI n ++ iI d, eI (divRound n d)))
#eval emitC "paeth" (n2 (fun a b => paeth a b 77) (edge8 ++ rs 40 256 14) (edge8.reverse ++ rs 40 256 15) |>.map fun (i, _) =>
  let a := i[0]!.toNat + 256 * i[1]!.toNat; let b := i[2]!.toNat + 256 * i[3]!.toNat
  (i ++ iN 77 2, eN (paeth a b 77)))
#eval emitC "to8" (([1, 2, 4, 8, 16].flatMap fun d => (edge8 ++ rs 20 (2 ^ d) 16).map fun v => (d, v % 2 ^ d)).map fun (d, v) =>
  (iN d 1 ++ iN v 2, [to8 d v]))
#eval emitC "utf8Len" (([0, 1, 127, 128, 2047, 2048, 65535, 65536, 1114111] ++ rs 40 1114112 17).map fun a => (iN a 3, eN (utf8Len a)))
#eval emitC "fmtFixed" (((ri 30 3000000 18).zip ((rs 30 20 19).map (· + 1))).map fun (v, b) =>
  (iI v ++ iN b 1, (fmtFixed v b).toUTF8.data.toList))
#eval emitE "isWs" LeanSvg.Entry.isWs.slots LeanSvg.Entry.isWs.code LeanSvg.Entry.isWs (charIn.map fun c => ([UInt8.ofNat c], [if LeanSvg.Bytes.isWs (UInt8.ofNat c) then 1 else 0]))
#eval emitE "isDigit" LeanSvg.Entry.isDigit.slots LeanSvg.Entry.isDigit.code LeanSvg.Entry.isDigit (charIn.map fun c => ([UInt8.ofNat c], [if LeanSvg.Bytes.isDigit (UInt8.ofNat c) then 1 else 0]))
#eval emitC "at'" (((List.range 12).map fun n => (List.range n).map fun j => UInt8.ofNat (rnd n j % 256)).flatMap fun bs =>
  (List.range 14).map fun i => (iN i 2 ++ bs, [LeanSvg.Bytes.at' ⟨bs.toArray⟩ i]))
#eval emitE "at3" LeanSvg.Entry.at3.slots LeanSvg.Entry.at3.code LeanSvg.Entry.at3 (((List.range 12).map fun n => (List.range n).map fun j => UInt8.ofNat (rnd n j % 256)).map fun bs =>
  (bs, [LeanSvg.Bytes.at' ⟨bs.toArray⟩ 3]))
end LeanSvg.Cases

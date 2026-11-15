/- lean-svg leaf functions, VERBATIM, run through the front end unmodified (`frontx_compile f`, no `with`/`requires`).
Source: https://github.com/rowancallahan/lean-svg @ df8e663 (Lean 4.34.0).  Provenance `file:line` before each.
Edits to the sources: only namespaces (`LeanSvg.X` -> `LeanSvgOrig.X`), `open Bytes (at')` added where the file opens it,
and the `Fx` abbreviation copied from Fixed.lean:17 (`abbrev Fx := Int`).  No API edits were needed for Lean 4.29.
Each `frontx_compile` is one attempt; its exact result (success or error) is recorded in `LEANSVG_VERBATIM.md`
from `Testing/leansvg/b/run.sh`.  The `-- F<n>` markers let `run.sh` attribute a message to a function. -/
import Riscv.Frontx.Machine

namespace LeanSvgOrig
open Proven Proven.Frontx

namespace Bytes
-- Bytes.lean:15
@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0
-- Bytes.lean:19
@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
-- Bytes.lean:23
@[inline] def toLower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c
end Bytes
-- F1
frontx_compile Bytes.at'
-- F2
frontx_compile Bytes.isDigit
-- F3
frontx_compile Bytes.toLower

namespace Font
-- Font.lean:554
@[inline] def b64Digit (c : UInt8) : UInt32 :=
  if 65 ≤ c && c ≤ 90 then c.toUInt32 - 65
  else if 97 ≤ c && c ≤ 122 then c.toUInt32 - 71
  else if 48 ≤ c && c ≤ 57 then c.toUInt32 + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 64
end Font
-- F4
frontx_compile Font.b64Digit

namespace Image
-- Image.lean:66
@[inline] def hexDigit (c : UInt8) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none
-- Image.lean:421
@[inline] def chans (v : Nat) : Nat × Nat × Nat × Nat :=
  ((v >>> 24) &&& 255, (v >>> 16) &&& 255, (v >>> 8) &&& 255, v &&& 255)
-- Image.lean:426
@[inline] def round32 (s : Int) : Nat :=
  if s ≤ 0 then 0 else Nat.min 255 ((s.toNat + 2147483648) >>> 32)
end Image
-- F5
frontx_compile Image.hexDigit
-- F6
frontx_compile Image.chans
-- F7
frontx_compile Image.round32

namespace Canvas
-- Canvas.lean:38
@[inline] def div255 (x : Nat) : Nat := (x + 255) >>> 8
-- Canvas.lean:47
@[inline] def premul (c a : Nat) : Nat := (c * a + 127) / 255
-- Canvas.lean:68
@[inline] def pack (r g b a : Nat) : Nat :=
  (r * 16777216) ||| (g * 65536) ||| (b * 256) ||| a
-- Canvas.lean:147
@[inline] def div65025 (x : Nat) : Nat := (x * 67636241) >>> 42
end Canvas
-- F8
frontx_compile Canvas.div255
-- F9
frontx_compile Canvas.premul
-- F10
frontx_compile Canvas.pack
-- F11
frontx_compile Canvas.div65025

namespace PngDecode
open Bytes (at')
-- PngDecode.lean:36
@[inline] def be32 (b : ByteArray) (i : Nat) : Nat :=
  ((at' b i).toNat <<< 24) ||| ((at' b (i + 1)).toNat <<< 16) |||
    ((at' b (i + 2)).toNat <<< 8) ||| (at' b (i + 3)).toNat
-- PngDecode.lean:51
def channels (ct : Nat) : Nat :=
  if ct == 2 then 3 else if ct == 4 then 2 else if ct == 6 then 4 else 1
-- PngDecode.lean:54
def validDepth (ct d : Nat) : Bool :=
  if ct == 0 then d == 1 || d == 2 || d == 4 || d == 8 || d == 16
  else if ct == 3 then d == 1 || d == 2 || d == 4 || d == 8
  else if ct == 2 || ct == 4 || ct == 6 then d == 8 || d == 16
  else false
-- PngDecode.lean:129
@[inline] def passLen (n o d : Nat) : Nat := if n > o then (n - o + d - 1) / d else 0
-- PngDecode.lean:142
@[inline] def paeth (a b c : Nat) : Nat :=
  let pa := if b ≥ c then b - c else c - b
  let pb := if a ≥ c then a - c else c - a
  let pc := if a + b ≥ 2 * c then a + b - 2 * c else 2 * c - (a + b)
  if pa ≤ pb && pa ≤ pc then a else if pb ≤ pc then b else c
end PngDecode
-- F12
frontx_compile PngDecode.be32
-- F13
frontx_compile PngDecode.channels
-- F14
frontx_compile PngDecode.validDepth
-- F15
frontx_compile PngDecode.passLen
-- F16
frontx_compile PngDecode.paeth

-- ShapeText.lean:63
namespace ShapeText
def utf8Len (cp : Nat) : Nat := if cp < 0x80 then 1 else if cp < 0x800 then 2 else if cp < 0x10000 then 3 else 4
end ShapeText
-- F17
frontx_compile ShapeText.utf8Len

namespace Text
-- Text.lean:119
def isHan (cp : Nat) : Bool :=
  (0x3400 ≤ cp && cp ≤ 0x4DBF) || (0x4E00 ≤ cp && cp ≤ 0x9FFF) ||
  (0xF900 ≤ cp && cp ≤ 0xFAFF) || (0x20000 ≤ cp && cp ≤ 0x3134F)
end Text
-- F18
frontx_compile Text.isHan

namespace Grad
-- Shader.lean:163
@[inline] def clampTo (lim a : Int) : Int := if a > lim then lim else if a < -lim then -lim else a
end Grad
-- F19
frontx_compile Grad.clampTo

abbrev Fx := Int   -- Fixed.lean:17
namespace Fx
-- Fixed.lean:41-43
def abs (a : Fx) : Fx := if a < 0 then -a else a
def min (a b : Fx) : Fx := if a ≤ b then a else b
end Fx
-- F20
frontx_compile Fx.abs
-- F21
frontx_compile Fx.min

namespace Png
-- Png.lean:113
def adlerChunk (rgba : ByteArray) (i fuel : Nat) (a b : UInt64) : UInt64 × UInt64 :=
  match fuel with
  | 0 => (a, b)
  | fuel' + 1 =>
    let a' := a + (if _ : i < rgba.size then rgba[i].toUInt64 else 0)
    adlerChunk rgba (i + 1) fuel' a' (b + a')
end Png
-- F22
frontx_compile Png.adlerChunk


/-! ## executed-Lean cases (`#eval` of each function) -> Testing/leansvg/b/cases/<fn>.cases
line: `<args> => <result>`; ByteArray = hex (`-` empty), numbers decimal, Option `none`/`some n`, tuples `(a, b)` -/
namespace Gen
def hx (b : ByteArray) : String := if b.isEmpty then "-" else String.join (b.toList.map fun c => (if c.toNat < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 c.toNat))
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def rnd (n : Nat) : List Nat := (List.range n).foldl (fun (acc : List Nat × Nat) _ => let s := lcg acc.2; ((s >>> 20) % 2 ^ 64 :: acc.1, s)) ([], 12345) |>.1
def edgesN : List Nat := [0, 1, 2, 3, 7, 8, 15, 16, 100, 127, 128, 254, 255, 256, 257, 4095, 65535, 65536, 2^24, 2^31, 2^32 - 1, 2^32, 2^32 + 1, 2^63 - 1, 2^63, 2^64 - 2, 2^64 - 1, 2^64, 2^70]
def nats : List Nat := edgesN ++ rnd 30 ++ (rnd 20).map (· % 70000)
def smallN : List Nat := (List.range 20) ++ [31, 32, 33, 255, 256, 65535, 65536, 1000000]
def ints : List Int := (edgesN.map (Int.ofNat ·)) ++ (edgesN.map (fun n => -(Int.ofNat n))) ++ (rnd 20).map fun n => (Int.ofNat n) - 2 ^ 63
def bytes : List UInt8 := (List.range 256).map UInt8.ofNat
def bas : List ByteArray := [ByteArray.empty, ⟨#[0]⟩, ⟨#[255]⟩, ⟨#[1, 2, 3]⟩, ⟨#[1, 2, 3, 4]⟩, ⟨#[1, 2, 3, 4, 5]⟩, ⟨#[0xFF, 0xFF, 0xFF, 0xFF]⟩, ⟨#[0xDE, 0xAD, 0xBE, 0xEF, 0x12, 0x34]⟩, ⟨(List.range 40).toArray.map fun i => UInt8.ofNat (i * 37)⟩]
def put (name : String) (ls : List String) : IO Unit := do
  IO.FS.createDirAll "Testing/leansvg/b/cases"; IO.FS.writeFile s!"Testing/leansvg/b/cases/{name}.cases" (String.join (ls.map (· ++ "\n")))
def un {α β} [ToString α] [ToString β] (name : String) (xs : List α) (f : α → β) : IO Unit := put name (xs.map fun x => s!"{x} => {f x}")
def bi {α β γ} [ToString α] [ToString β] [ToString γ] (name : String) (xs : List α) (ys : List β) (f : α → β → γ) : IO Unit :=
  put name (xs.flatMap fun x => ys.map fun y => s!"{x} {y} => {f x y}")
def tri {α β γ δ} [ToString α] [ToString β] [ToString γ] [ToString δ] (name : String) (xs : List α) (ys : List β) (zs : List γ) (f : α → β → γ → δ) : IO Unit :=
  put name (xs.flatMap fun x => ys.flatMap fun y => zs.map fun z => s!"{x} {y} {z} => {f x y z}")
def run : IO Unit := do
  let ixs : List Nat := (List.range 12) ++ [2^63, 2^64 - 1, 2^64, 2^64 + 3]
  put "Bytes.at'" (bas.flatMap fun b => ixs.map fun i => s!"{hx b} {i} => {Bytes.at' b i}")
  un "Bytes.isDigit" bytes Bytes.isDigit
  un "Bytes.toLower" bytes Bytes.toLower
  un "Font.b64Digit" bytes Font.b64Digit
  un "Image.hexDigit" bytes Image.hexDigit
  un "Image.chans" nats Image.chans
  un "Image.round32" ints Image.round32
  un "Canvas.div255" nats Canvas.div255
  bi "Canvas.premul" nats nats Canvas.premul
  tri "Canvas.pack" smallN smallN smallN (fun r g b => Canvas.pack r g b 255)
  un "Canvas.div65025" nats Canvas.div65025
  put "PngDecode.be32" (bas.flatMap fun b => ixs.map fun i => s!"{hx b} {i} => {PngDecode.be32 b i}")
  un "PngDecode.channels" smallN PngDecode.channels
  bi "PngDecode.validDepth" (List.range 8) (List.range 20) PngDecode.validDepth
  tri "PngDecode.passLen" smallN [0, 1, 2, 4] [1, 2, 4, 8] PngDecode.passLen
  tri "PngDecode.paeth" smallN smallN [0, 1, 5, 255] PngDecode.paeth
  un "ShapeText.utf8Len" nats ShapeText.utf8Len
  un "Text.isHan" (nats ++ [0x3400, 0x4DBF, 0x4DC0, 0x4E00, 0x9FFF, 0xA000, 0xF900, 0xFAFF, 0x20000, 0x3134F, 0x31350]) Text.isHan
  bi "Grad.clampTo" ints ints Grad.clampTo
  un "Fx.abs" ints Fx.abs
  bi "Fx.min" ints ints Fx.min
  put "Png.adlerChunk" (bas.flatMap fun b => [0, 1, 2, 5].flatMap fun i => [0, 1, 3, 8].flatMap fun f => [0, 1, 65520, 2^32, 2^64 - 1].map fun a =>
    s!"{hx b} {i} {f} {a} 7 => {Png.adlerChunk b i f (UInt64.ofNat a) 7}")
  IO.println "cases written"
#eval run
end Gen
end LeanSvgOrig

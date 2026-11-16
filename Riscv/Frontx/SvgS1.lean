/- SvgS1: lean-svg functions marked "possibly unblocked" by NOTES §22 (variable `*` / `/` `%`), retried VERBATIM
with `frontx_compile` (`Testing/notes/LEANSVG_TARGETS.md` §2). Source: github.com/rowancallahan/lean-svg @ df8e663.
Each block is copied from the file line named in its comment (doc comments not copied). The constants it refers to
are copied verbatim above it under the same namespace. No requires clauses. -/
import Riscv.Frontx.Machine

namespace LeanSvg.Svg
-- Svg.lean:73@df8e663
def opacityOne : Nat := 1000000000000000000
end LeanSvg.Svg

namespace LeanSvg.Canvas
-- Canvas.lean:137@df8e663
def opGrid : Nat := 65280
end LeanSvg.Canvas

namespace LeanSvg.Grad
-- Shader.lean:127@df8e663
def opacityOne : Nat := 1000000000000000000
end LeanSvg.Grad

namespace LeanSvg.Grad
-- Shader.lean:728@df8e663
def recipShift : Nat := 44
end LeanSvg.Grad

namespace LeanSvg.Grad
-- Shader.lean:889@df8e663
def opacityCube : Nat := opacityOne * opacityOne * opacityOne
end LeanSvg.Grad

namespace LeanSvg.Lighting
-- Filter/Lighting.lean:207@df8e663
def S : Nat := 2 ^ 80
end LeanSvg.Lighting

namespace LeanSvg.Bytes
-- Bytes.lean:15@df8e663
@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0
end LeanSvg.Bytes

namespace LeanSvg.Jpeg
-- Jpeg/Huffman.lean:19@df8e663
@[inline] def byteAt (bs : ByteArray) (i : Nat) : Nat :=
  if h : i < bs.size then bs[i].toNat else 0
end LeanSvg.Jpeg

namespace LeanSvg.Clip
-- Clip.lean:106@df8e663
@[inline] def cov16 (a : Nat) : Nat := (a * 65536 + 254) / 255
frontx_compile cov16
end LeanSvg.Clip

namespace LeanSvg.Grad
-- Shader.lean:731@df8e663
def recipOf (den : Nat) : Nat :=
  if den == 0 then 0 else (1 <<< recipShift) / (2 * den) + 1
frontx_compile recipOf
end LeanSvg.Grad

namespace LeanSvg.Image
-- Image.lean:236@df8e663
@[inline] def premulU8 (c a : Nat) : Nat :=
  let p := c * a + 128
  (p + (p >>> 8)) >>> 8
frontx_compile premulU8
end LeanSvg.Image

namespace LeanSvg.PngDecode
open LeanSvg.Bytes (at')
-- PngDecode.lean:226@df8e663
@[inline] def to8 (d v : Nat) : UInt8 :=
  if d == 16 then (v >>> 8).toUInt8
  else if d == 8 then v.toUInt8
  else (v * (255 / ((1 <<< d) - 1))).toUInt8
frontx_compile to8
end LeanSvg.PngDecode

namespace LeanSvg.Jpeg
-- Jpeg/Huffman.lean:26@df8e663
@[inline] def peekBits (d : ByteArray) (pos n : Nat) : Nat :=
  let b := pos / 8
  let w : UInt32 := (byteAt d b).toUInt32 * 65536 + (byteAt d (b + 1)).toUInt32 * 256 +
    (byteAt d (b + 2)).toUInt32
  ((w >>> (24 - pos % 8 - n).toUInt32) &&& (((1 : UInt32) <<< n.toUInt32) - 1)).toNat
frontx_compile peekBits
end LeanSvg.Jpeg

namespace LeanSvg.Grad
-- Shader.lean:896@df8e663
def stopAlpha8 (alpha stopOp fillOp groupOp : Nat) : Nat :=
  Nat.min 255 ((alpha * stopOp * fillOp * groupOp * 2 / opacityCube + 1) / 2)
frontx_compile stopAlpha8
end LeanSvg.Grad

namespace LeanSvg.Pat
-- PatternRender.lean:204@df8e663
def opacityQ (o : Nat) : Nat :=
  if o ≥ Svg.opacityOne then Canvas.opGrid
  else (o * Canvas.opGrid * 2 / Svg.opacityOne + 1) / 2
frontx_compile opacityQ
end LeanSvg.Pat

namespace LeanSvg.Svg
-- Svg.lean:1025@df8e663
def mulOpacity (a b : Nat) : Nat := (a * b * 2 / opacityOne + 1) / 2
frontx_compile mulOpacity
end LeanSvg.Svg

namespace LeanSvg.Canvas
-- Canvas.lean:47@df8e663
@[inline] def premul (c a : Nat) : Nat := (c * a + 127) / 255
frontx_compile premul
end LeanSvg.Canvas

namespace LeanSvg.Canvas
-- Canvas.lean:55@df8e663
@[inline] def unpremul (c a : Nat) : Nat :=
  if a == 0 then 0 else Nat.min 255 ((c * 510 + a) / (2 * a))
frontx_compile unpremul
end LeanSvg.Canvas

namespace LeanSvg.Inflate
open LeanSvg.Bytes (at')
-- Inflate.lean:27@df8e663
@[inline] def peek (inp : ByteArray) (bp n : Nat) : Nat :=
  let i := bp / 8
  let v := (at' inp i).toNat ||| ((at' inp (i + 1)).toNat <<< 8) |||
    ((at' inp (i + 2)).toNat <<< 16) ||| ((at' inp (i + 3)).toNat <<< 24)
  (v >>> (bp % 8)) % (1 <<< n)
frontx_compile peek
end LeanSvg.Inflate

namespace LeanSvg.Lighting
-- Filter/Lighting.lean:294@df8e663
def mulQ (a b : Nat) : Nat :=
  let ah := a >>> 22
  let al := a &&& 4194303
  let bh := b >>> 22
  let bl := b &&& 4194303
  ah * bh + ((ah * bl + al * bh) >>> 22) + ((al * bl) >>> 44)
frontx_compile mulQ
end LeanSvg.Lighting

namespace LeanSvg.Png
-- Png.lean:166@df8e663
def zlibLen (rowBytes h : Nat) : Nat :=
  let raw := h * (rowBytes + 1)
  let nblocks := if raw == 0 then 1 else (raw + 65534) / 65535
  2 + nblocks * 5 + raw + 4
frontx_compile zlibLen
end LeanSvg.Png

namespace LeanSvg.PngDecode
open LeanSvg.Bytes (at')
-- PngDecode.lean:216@df8e663
@[inline] def sample (raw : ByteArray) (d ch rs x c : Nat) : Nat :=
  if d == 8 then (at' raw (rs + x * ch + c)).toNat
  else if d == 16 then
    let i := rs + 2 * (x * ch + c)
    (at' raw i).toNat * 256 + (at' raw (i + 1)).toNat
  else
    let bit := x * d
    ((at' raw (rs + bit / 8)).toNat >>> (8 - d - bit % 8)) % (1 <<< d)
frontx_compile sample
end LeanSvg.PngDecode

namespace LeanSvg.FilterApply
-- FilterApply.lean:387@df8e663
def iirCoeffs (s16 : Nat) : Nat × Nat :=
  let S : Nat := 4294967296
  let L := s16 * s16 / 8
  if L == 0 then (0, S)
  else
    let sq := Nat.sqrt ((S + 4 * L) * S)
    let dnu := (S + 2 * L - sq) * S / (2 * L)
    let R := dnu * S / L
    (dnu, R * R / S * R / S * R / S)
frontx_compile iirCoeffs
end LeanSvg.FilterApply

namespace LeanSvg.Grad
-- Shader.lean:763@df8e663
@[inline] def lerpDown (cl cr back den recip : Nat) : Nat :=
  if cl == cr then cl
  else if cr ≥ cl then
    let base := (2 * cl + 1) * den
    let d := 2 * (cr - cl) * back
    if d ≥ base then 0 else Nat.min 255 (((base - d) * recip) >>> recipShift)
  else
    let v := (2 * cl + 1) * den + 2 * (cl - cr) * back
    if v ≥ 510 * den then 255 else (v * recip) >>> recipShift
frontx_compile lerpDown
end LeanSvg.Grad

namespace LeanSvg.Render
-- Render.lean:471@df8e663
def opacityQ (o : Nat) : Nat :=
  if o ≥ Svg.opacityOne then Canvas.opGrid
  else (o * Canvas.opGrid * 2 / Svg.opacityOne + 1) / 2
frontx_compile opacityQ
end LeanSvg.Render

namespace LeanSvg.PngDecode
open LeanSvg.Bytes (at')
-- PngDecode.lean:129@df8e663
@[inline] def passLen (n o d : Nat) : Nat := if n > o then (n - o + d - 1) / d else 0
frontx_compile passLen
end LeanSvg.PngDecode

namespace LeanSvg.Lighting
-- Filter/Lighting.lean:211@df8e663
def atanh2 (n d : Nat) : Nat := Id.run do
  let z := n * S / d
  let z2 := (z * z) >>> 80
  let mut t := z
  let mut acc := 0
  for i in [0:28] do
    acc := acc + t / (2 * i + 1)
    t := (t * z2) >>> 80
  return 2 * acc
frontx_compile atanh2
end LeanSvg.Lighting

namespace LeanSvg.Svg
-- Svg.lean:1040@df8e663
def opacityToU8 (alpha fillOp groupOp : Nat) : Nat :=
  Nat.min 255 ((alpha * fillOp * groupOp * 2 / (opacityOne * opacityOne) + 1) / 2)
frontx_compile opacityToU8
end LeanSvg.Svg

namespace LeanSvg.Grad
-- Shader.lean:752@df8e663
@[inline] def lerpUp (cl cr num den recip : Nat) : Nat :=
  if cl == cr then cl
  else
    let base := (2 * cl + 1) * den
    -- `0 ≤ num < den`, so `v ≤ 511·den`: neither clamp can bite.
    let v := if cr ≥ cl then base + 2 * (cr - cl) * num
             else base - 2 * (cl - cr) * num
    Nat.min 255 ((v * recip) >>> recipShift)
frontx_compile lerpUp
end LeanSvg.Grad

namespace LeanSvg.Lighting
-- Filter/Lighting.lean:226@df8e663
def expS (f : Nat) : Nat := Id.run do
  let mut t := S
  let mut acc := 0
  for i in [0:28] do
    acc := acc + t
    t := ((t * f) >>> 80) / (i + 1)
  return acc
frontx_compile expS
end LeanSvg.Lighting


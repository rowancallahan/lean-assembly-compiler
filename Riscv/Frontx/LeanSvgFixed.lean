/- lean-svg (github.com/rowancallahan/lean-svg @df8e663, Lean v4.34.0 there; these lines check unchanged on v4.29.0):
fixed-point and `Int` helpers copied VERBATIM, one doc comment per definition giving `file:line` (the original doc
comments are not copied).  Compiled by the list front end (`IntExamples.lean`) and the word-array front end
(`WaInt.lean`), NOTES section 26. -/

/-! ## lean-svg @df8e663, verbatim -/

namespace LeanSvg

/-- Fixed-point number with 8 fractional bits. (`LeanSvg/Fixed.lean:17`) -/
abbrev Fx := Int

namespace Fx

/-- `LeanSvg/Fixed.lean:21` -/
def one : Fx := 256

/-- `LeanSvg/Fixed.lean:25` -/
def maxVal : Fx := 1073741824

/-- `LeanSvg/Fixed.lean:27` -/
def clamp (a : Fx) : Fx :=
  if a > maxVal then maxVal else if a < -maxVal then -maxVal else a

/-- `LeanSvg/Fixed.lean:32` -/
@[inline] def inRange (a : Fx) : Bool := -maxVal ≤ a && a ≤ maxVal

/-- `LeanSvg/Fixed.lean:34` -/
def ofNat (n : Nat) : Fx := clamp ((n : Int) * 256)

/-- `LeanSvg/Fixed.lean:37-43` -/
def mul (a b : Fx) : Fx := clamp (Int.ediv (a * b) 256)
def floor (a : Fx) : Int := Int.ediv a 256
def ceil (a : Fx) : Int := -(Int.ediv (-a) 256)
def round (a : Fx) : Int := Int.ediv (a + 128) 256
def abs (a : Fx) : Fx := if a < 0 then -a else a
def min (a b : Fx) : Fx := if a ≤ b then a else b
def max (a b : Fx) : Fx := if a ≤ b then b else a

/-- `LeanSvg/Fixed.lean:50` -/
def scale16 (a : Fx) (s : Int) : Fx := clamp (Int.ediv (a * s) 65536)

end Fx

/-- `LeanSvg/Geom.lean:73-82` -/
def linMax : Int := 268435456
def clampLin (v : Int) : Int := if v > linMax then linMax else if v < -linMax then -linMax else v
@[inline] def linInRange (v : Int) : Bool := -linMax ≤ v && v ≤ linMax

namespace Image
/-- `LeanSvg/Image.lean:406` -/
@[inline] def clampIx (i : Int) (n : Nat) : Nat :=
  if i ≤ 0 then 0 else if i.toNat ≥ n then n - 1 else i.toNat

/-- `LeanSvg/Image.lean:410` -/
@[inline] def bicNear (t : Int) : Int :=
  let a := -21 * t + 27 * 65536
  let b := Int.ediv (a * t) 65536 + 9 * 65536
  Int.ediv (Int.ediv (b * t) 65536 + 65536) 18

/-- `LeanSvg/Image.lean:416` -/
@[inline] def bicFar (t : Int) : Int :=
  let t2 := Int.ediv (t * t) 65536
  Int.ediv (Int.ediv (t2 * (7 * t - 6 * 65536)) 65536) 18

/-- `LeanSvg/Image.lean:426` -/
@[inline] def round32 (s : Int) : Nat :=
  if s ≤ 0 then 0 else Nat.min 255 ((s.toNat + 2147483648) >>> 32)
end Image

namespace Woff
/-- `LeanSvg/Woff.lean:175` -/
def fitsI16 (v : Int) : Bool := -32768 ≤ v && v ≤ 32767
end Woff

namespace Raster
/-- `LeanSvg/Raster.lean:85` -/
@[inline] def insideW (evenOdd : Bool) (w : Int) : Bool :=
  if evenOdd then Int.emod w 2 != 0 else w != 0
end Raster

namespace Grad
/-- `LeanSvg/Shader.lean:153` -/
@[inline] def norm2 (x y : Int) : Int :=
  Int.ofNat ((x.natAbs * x.natAbs + y.natAbs * y.natAbs) >>> 16)

/-- `LeanSvg/Shader.lean:163` -/
@[inline] def clampTo (lim a : Int) : Int := if a > lim then lim else if a < -lim then -lim else a
end Grad

namespace Filter
/-- `LeanSvg/Filter/Morphology.lean:110` -/
def morphCeil (r : Int) (sc : Nat) : Nat :=
  if r ≤ 0 || sc == 0 then 0
  else
    let a := r.toNat * sc
    (a + 4294967295) / 4294967296
end Filter

end LeanSvg

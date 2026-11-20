/- lean-svg rows of LEANSVG_TARGETS.md (@ `origin/leansvg-targets`) blocked by user structures and `Int`/`Fx`
(NOTES sections 26 and 32).  Source: github.com/rowancallahan/lean-svg @ df8e663, copied VERBATIM with `file:line`
per block; doc comments dropped, nothing else changed. -/
import Legacy.Riscv.Frontx.IntExamples
import Legacy.Riscv.Frontx.StructExamples
-- Lean 4.34.1: as IntExamples (the generated proofs compare instance arguments, old check)
set_option backward.isDefEq.respectTransparency false

namespace LeanSvg

-- LeanSvg/Geom.lean:12@df8e663
structure Pt where
  x : Fx
  y : Fx
deriving Repr, Inhabited, BEq

namespace Pt
-- LeanSvg/Geom.lean:18@df8e663
def add (p q : Pt) : Pt := ⟨Fx.clamp (p.x + q.x), Fx.clamp (p.y + q.y)⟩
-- LeanSvg/Geom.lean:19@df8e663
def sub (p q : Pt) : Pt := ⟨Fx.clamp (p.x - q.x), Fx.clamp (p.y - q.y)⟩
-- LeanSvg/Geom.lean:20@df8e663
def neg (p : Pt) : Pt := ⟨-p.x, -p.y⟩
end Pt

-- LeanSvg/Geom.lean:61@df8e663
structure Mat where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Fx
  f : Fx
deriving Repr, Inhabited, BEq

-- LeanSvg/Geom.lean:332@df8e663
structure Box where
  x0 : Fx
  y0 : Fx
  x1 : Fx
  y1 : Fx
deriving Repr, Inhabited

-- LeanSvg/Units.lean:40@df8e663
structure Metrics where
  upem : Nat
  zero : Nat
  ideo : Nat
  cap : Int
  xHeight : Int
  ascent : Int
  descent : Int
  lineGap : Int
deriving Inhabited

namespace Mat
-- LeanSvg/Geom.lean:73@df8e663
def linMax : Int := 268435456
-- LeanSvg/Geom.lean:74@df8e663
def clampLin (v : Int) : Int := if v > linMax then linMax else if v < -linMax then -linMax else v
end Mat

namespace Box
-- LeanSvg/Geom.lean:349@df8e663
def meets (b : Box) (lox loy hix hiy : Fx) : Bool :=
  b.x1 ≥ lox && b.y1 ≥ loy && b.x0 < hix && b.y0 < hiy
end Box

end LeanSvg

namespace Proven.Frontx.SvgS2
open Proven Proven.Frontx Proven.Frontx.Book LeanSvg

/-! ## Constructors and projections (source level: `f.exec`) -/

frontx_compile LeanSvg.Pt.mk
frontx_compile LeanSvg.Pt.x
frontx_compile LeanSvg.Pt.y
frontx_compile LeanSvg.Mat.mk
frontx_compile LeanSvg.Mat.e
frontx_compile LeanSvg.Mat.a
frontx_compile LeanSvg.Box.mk
frontx_compile LeanSvg.Box.x1
frontx_compile LeanSvg.Metrics.mk
frontx_compile LeanSvg.Metrics.cap
frontx_compile LeanSvg.Metrics.upem

/-! ## Functions over `Pt` (structure parameters and results, `Fx.clamp` of `IntExamples`) -/

frontx_compile LeanSvg.Pt.neg
frontx_compile LeanSvg.Pt.sub requires fun p q => -2 ^ 63 ≤ p.x - q.x ∧ p.x - q.x < 2 ^ 63 ∧ -2 ^ 63 ≤ p.y - q.y ∧ p.y - q.y < 2 ^ 63
frontx_compile LeanSvg.Pt.add requires fun p q => -2 ^ 63 ≤ p.x + q.x ∧ p.x + q.x < 2 ^ 63 ∧ -2 ^ 63 ≤ p.y + q.y ∧ p.y + q.y < 2 ^ 63

frontx_compile LeanSvg.Mat.clampLin requires fun v => -2 ^ 63 ≤ v ∧ v < 2 ^ 63
frontx_compile LeanSvg.Box.meets requires fun b lox loy hix hiy => -2 ^ 63 ≤ b.x0 ∧ b.x0 < 2 ^ 63 ∧ -2 ^ 63 ≤ b.y0 ∧ b.y0 < 2 ^ 63 ∧ -2 ^ 63 ≤ b.x1 ∧ b.x1 < 2 ^ 63 ∧ -2 ^ 63 ≤ b.y1 ∧ b.y1 < 2 ^ 63 ∧ -2 ^ 63 ≤ lox ∧ lox < 2 ^ 63 ∧ -2 ^ 63 ≤ loy ∧ loy < 2 ^ 63 ∧ -2 ^ 63 ≤ hix ∧ hix < 2 ^ 63 ∧ -2 ^ 63 ≤ hiy ∧ hiy < 2 ^ 63

/-! ## Entry points (glue: the arguments are signed 32-bit words / bytes of the input; not library code) -/

open Proven.Frontx.IntEx in
def ptNegAt (xs : ByteArray) (i : Nat) : Pt := Pt.neg ⟨i32At xs i, i32At xs (i + 8)⟩
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def ptAddAt (xs : ByteArray) (i : Nat) : Pt := Pt.add ⟨i32At xs i, i32At xs (i + 8)⟩ ⟨i32At xs (i + 16), i32At xs (i + 24)⟩
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def ptSubAt (xs : ByteArray) (i : Nat) : Pt := Pt.sub ⟨i32At xs i, i32At xs (i + 8)⟩ ⟨i32At xs (i + 16), i32At xs (i + 24)⟩
open Proven.Frontx.IntEx in
def matAAt (xs : ByteArray) (i : Nat) : Int := Mat.a ⟨i32At xs i, i32At xs (i + 8), i32At xs (i + 16), i32At xs (i + 24), i32At xs (i + 32), i32At xs (i + 40)⟩
open Proven.Frontx.IntEx in
def matEAt (xs : ByteArray) (i : Nat) : Int := Mat.e ⟨i32At xs i, i32At xs (i + 8), i32At xs (i + 16), i32At xs (i + 24), i32At xs (i + 32), i32At xs (i + 40)⟩
open Proven.Frontx.IntEx in
def boxX1At (xs : ByteArray) (i : Nat) : Int := Box.x1 ⟨i32At xs i, i32At xs (i + 8), i32At xs (i + 16), i32At xs (i + 24)⟩
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def metricsCapAt (xs : ByteArray) (i : Nat) : Int :=
  Metrics.cap ⟨(byteAt xs i).toNat, (byteAt xs (i + 1)).toNat, (byteAt xs (i + 2)).toNat, i32At xs (i + 8), i32At xs (i + 16),
   i32At xs (i + 24), i32At xs (i + 32), i32At xs (i + 40)⟩
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def metricsUpemAt (xs : ByteArray) (i : Nat) : Nat :=
  Metrics.upem ⟨(byteAt xs i).toNat, (byteAt xs (i + 1)).toNat, (byteAt xs (i + 2)).toNat, i32At xs (i + 8), i32At xs (i + 16),
   i32At xs (i + 24), i32At xs (i + 32), i32At xs (i + 40)⟩

frontx_compile ptNegAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile ptAddAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile ptSubAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile matAAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile matEAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile boxX1At requires fun _ i => i + 64 < 2 ^ 64
frontx_compile metricsCapAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile metricsUpemAt requires fun _ i => i + 64 < 2 ^ 64

def ptNegE (xs : ByteArray) : Pt := ptNegAt xs 0
frontx_entry ptNegE
frontx_implements_bytes ptNegE
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def ptAddXAt (xs : ByteArray) (i : Nat) : Int := Pt.x (Pt.add ⟨i32At xs i, i32At xs (i + 8)⟩ ⟨i32At xs (i + 16), i32At xs (i + 24)⟩)
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def ptAddYAt (xs : ByteArray) (i : Nat) : Int := Pt.y (Pt.add ⟨i32At xs i, i32At xs (i + 8)⟩ ⟨i32At xs (i + 16), i32At xs (i + 24)⟩)
open Proven.Frontx.IntEx in
set_option maxHeartbeats 2000000 in
def ptSubXAt (xs : ByteArray) (i : Nat) : Int := Pt.x (Pt.sub ⟨i32At xs i, i32At xs (i + 8)⟩ ⟨i32At xs (i + 16), i32At xs (i + 24)⟩)
frontx_compile ptAddXAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile ptAddYAt requires fun _ i => i + 64 < 2 ^ 64
frontx_compile ptSubXAt requires fun _ i => i + 64 < 2 ^ 64
def ptAddXE (xs : ByteArray) : Int := ptAddXAt xs 0
frontx_entry ptAddXE
frontx_implementsC ptAddXE
def ptAddYE (xs : ByteArray) : Int := ptAddYAt xs 0
frontx_entry ptAddYE
frontx_implementsC ptAddYE
def ptSubXE (xs : ByteArray) : Int := ptSubXAt xs 0
frontx_entry ptSubXE
frontx_implementsC ptSubXE
def matAE (xs : ByteArray) : Int := matAAt xs 0
frontx_entry matAE
frontx_implementsC matAE
def matEE (xs : ByteArray) : Int := matEAt xs 0
frontx_entry matEE
frontx_implementsC matEE
def boxX1E (xs : ByteArray) : Int := boxX1At xs 0
frontx_entry boxX1E
frontx_implementsC boxX1E
def metricsCapE (xs : ByteArray) : Int := metricsCapAt xs 0
frontx_entry metricsCapE
frontx_implementsC metricsCapE
def metricsUpemE (xs : ByteArray) : Nat := metricsUpemAt xs 0
frontx_entry metricsUpemE
frontx_implements metricsUpemE

open Proven.Frontx.IntEx in
def clampLinAt (xs : ByteArray) (i : Nat) : Int := Mat.clampLin (i32At xs i)
frontx_compile clampLinAt requires fun _ i => i + 64 < 2 ^ 64
def clampLinE (xs : ByteArray) : Int := clampLinAt xs 0
frontx_entry clampLinE
frontx_implementsC clampLinE

end Proven.Frontx.SvgS2

/- `Int` scalars in the list front end (`frontx_compile`, NOTES section 26): lean-svg's fixed-point helpers
(`abbrev Fx := Int`), copied verbatim with their source lines (lean-svg @df8e663), compiled with machine theorems
through `frontx_implementsC` (signed `div` / `rem` are M-extension words: checked words `compBFC`). -/
import Riscv.Frontx.MulExamples
import Riscv.Frontx.LeanSvgFixed
-- Lean 4.34.1: the generated proofs compare instance arguments (old check)
set_option backward.isDefEq.respectTransparency false

/-! ## glue: signed words from the input (two's complement, little-endian, `0` past the end) -/

namespace Proven.Frontx.IntEx
open Proven.Frontx.Scal

/-- the 64-bit word at byte `i`, signed -/
def i64At (xs : ByteArray) (i : Nat) : Int :=
  if (u64At xs i).toNat < 2 ^ 63 then ((u64At xs i).toNat : Int) else ((u64At xs i).toNat : Int) - 2 ^ 64

/-- the low 32 bits of the word at byte `i`, signed -/
def i32At (xs : ByteArray) (i : Nat) : Int :=
  if (u64At xs i).toNat % 2 ^ 32 < 2 ^ 31 then (((u64At xs i).toNat % 2 ^ 32 : Nat) : Int)
  else (((u64At xs i).toNat % 2 ^ 32 : Nat) : Int) - 2 ^ 32

end Proven.Frontx.IntEx

/-! ## the functions themselves (range hypotheses as `requires`) -/

frontx_compile LeanSvg.Fx.clamp requires fun a => -2 ^ 63 ≤ a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Fx.inRange requires fun a => -2 ^ 63 ≤ a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Fx.ofNat requires fun n => n < 2 ^ 32
frontx_compile LeanSvg.Fx.mul requires fun a b => -2 ^ 63 ≤ a * b ∧ a * b < 2 ^ 63
frontx_compile LeanSvg.Fx.floor requires fun a => -2 ^ 63 ≤ a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Fx.ceil requires fun a => -2 ^ 63 < a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Fx.round requires fun a => -2 ^ 63 ≤ a ∧ a + 128 < 2 ^ 63
frontx_compile LeanSvg.Fx.abs requires fun a => -2 ^ 63 ≤ a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Fx.min requires fun a b => -2 ^ 63 ≤ a ∧ a < 2 ^ 63 ∧ -2 ^ 63 ≤ b ∧ b < 2 ^ 63
frontx_compile LeanSvg.Fx.max requires fun a b => -2 ^ 63 ≤ a ∧ a < 2 ^ 63 ∧ -2 ^ 63 ≤ b ∧ b < 2 ^ 63
frontx_compile LeanSvg.Fx.scale16 requires fun a s => -2 ^ 63 ≤ a * s ∧ a * s < 2 ^ 63
frontx_compile LeanSvg.clampLin requires fun v => -2 ^ 63 ≤ v ∧ v < 2 ^ 63
frontx_compile LeanSvg.linInRange requires fun v => -2 ^ 63 ≤ v ∧ v < 2 ^ 63
frontx_compile LeanSvg.Image.clampIx requires fun i n => -2 ^ 63 ≤ i ∧ i < 2 ^ 63 ∧ n < 2 ^ 64
frontx_compile LeanSvg.Image.bicFar requires fun t => 0 ≤ t ∧ t < 2 ^ 17
frontx_compile LeanSvg.Image.round32 requires fun s => -2 ^ 63 ≤ s ∧ s < 2 ^ 63
frontx_compile LeanSvg.Woff.fitsI16 requires fun v => -2 ^ 63 ≤ v ∧ v < 2 ^ 63
frontx_compile LeanSvg.Raster.insideW requires fun _ w => -2 ^ 63 ≤ w ∧ w < 2 ^ 63
frontx_compile LeanSvg.Grad.norm2 requires fun x y => -2 ^ 31 ≤ x ∧ x ≤ 2 ^ 31 ∧ -2 ^ 31 ≤ y ∧ y ≤ 2 ^ 31
frontx_compile LeanSvg.Grad.clampTo requires fun lim a => -2 ^ 63 < lim ∧ lim < 2 ^ 63 ∧ -2 ^ 63 ≤ a ∧ a < 2 ^ 63
frontx_compile LeanSvg.Filter.morphCeil requires fun r sc => -2 ^ 63 ≤ r ∧ r < 2 ^ 31 ∧ sc < 2 ^ 32

namespace Proven.Frontx.IntEx
open Proven.Frontx.Scal

/-! ## entry points: the arguments as 8-byte words of the input -/

def clampAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.clamp (i64At xs (i + 0))
frontx_compile clampAt requires fun _ i => i + 32 < 2 ^ 64
def clampE (xs : ByteArray) : Int := clampAt xs 0
frontx_entry clampE
frontx_implementsC clampE

def inRangeAt (xs : ByteArray) (i : Nat) : Bool := LeanSvg.Fx.inRange (i64At xs (i + 0))
frontx_compile inRangeAt requires fun _ i => i + 32 < 2 ^ 64
def inRangeE (xs : ByteArray) : Bool := inRangeAt xs 0
frontx_entry inRangeE
frontx_implementsC inRangeE

def ofNatAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.ofNat ((u64At xs (i + 0)).toNat % 2 ^ 32)
frontx_compile ofNatAt requires fun _ i => i + 32 < 2 ^ 64
def ofNatE (xs : ByteArray) : Int := ofNatAt xs 0
frontx_entry ofNatE
frontx_implementsC ofNatE

def mulAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.mul (i32At xs (i + 0)) (i32At xs (i + 8))
frontx_compile mulAt requires fun _ i => i + 32 < 2 ^ 64
def mulE (xs : ByteArray) : Int := mulAt xs 0
frontx_entry mulE
frontx_implementsC mulE

def floorAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.floor (i64At xs (i + 0))
frontx_compile floorAt requires fun _ i => i + 32 < 2 ^ 64
def floorE (xs : ByteArray) : Int := floorAt xs 0
frontx_entry floorE
frontx_implementsC floorE

def ceilAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.ceil (i32At xs (i + 0))
frontx_compile ceilAt requires fun _ i => i + 32 < 2 ^ 64
def ceilE (xs : ByteArray) : Int := ceilAt xs 0
frontx_entry ceilE
frontx_implementsC ceilE

def roundAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.round (i32At xs (i + 0))
frontx_compile roundAt requires fun _ i => i + 32 < 2 ^ 64
def roundE (xs : ByteArray) : Int := roundAt xs 0
frontx_entry roundE
frontx_implementsC roundE

def absAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.abs (i64At xs (i + 0))
frontx_compile absAt requires fun _ i => i + 32 < 2 ^ 64
def absE (xs : ByteArray) : Int := absAt xs 0
frontx_entry absE
frontx_implementsC absE

def minAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.min (i64At xs (i + 0)) (i64At xs (i + 8))
frontx_compile minAt requires fun _ i => i + 32 < 2 ^ 64
def minE (xs : ByteArray) : Int := minAt xs 0
frontx_entry minE
frontx_implementsC minE

def maxAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.max (i64At xs (i + 0)) (i64At xs (i + 8))
frontx_compile maxAt requires fun _ i => i + 32 < 2 ^ 64
def maxE (xs : ByteArray) : Int := maxAt xs 0
frontx_entry maxE
frontx_implementsC maxE

def scale16At (xs : ByteArray) (i : Nat) : Int := LeanSvg.Fx.scale16 (i32At xs (i + 0)) (i32At xs (i + 8))
frontx_compile scale16At requires fun _ i => i + 32 < 2 ^ 64
def scale16E (xs : ByteArray) : Int := scale16At xs 0
frontx_entry scale16E
frontx_implementsC scale16E

def clampLinAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.clampLin (i64At xs (i + 0))
frontx_compile clampLinAt requires fun _ i => i + 32 < 2 ^ 64
def clampLinE (xs : ByteArray) : Int := clampLinAt xs 0
frontx_entry clampLinE
frontx_implementsC clampLinE

def linInRangeAt (xs : ByteArray) (i : Nat) : Bool := LeanSvg.linInRange (i64At xs (i + 0))
frontx_compile linInRangeAt requires fun _ i => i + 32 < 2 ^ 64
def linInRangeE (xs : ByteArray) : Bool := linInRangeAt xs 0
frontx_entry linInRangeE
frontx_implementsC linInRangeE

def clampIxAt (xs : ByteArray) (i : Nat) : Nat := LeanSvg.Image.clampIx (i64At xs (i + 0)) ((u64At xs (i + 8)).toNat % 2 ^ 32)
frontx_compile clampIxAt requires fun _ i => i + 32 < 2 ^ 64
def clampIxE (xs : ByteArray) : Nat := clampIxAt xs 0
frontx_entry clampIxE
frontx_implementsC clampIxE

def round32At (xs : ByteArray) (i : Nat) : Nat := LeanSvg.Image.round32 (i64At xs (i + 0))
frontx_compile round32At requires fun _ i => i + 32 < 2 ^ 64
def round32E (xs : ByteArray) : Nat := round32At xs 0
frontx_entry round32E
frontx_implementsC round32E

def fitsI16At (xs : ByteArray) (i : Nat) : Bool := LeanSvg.Woff.fitsI16 (i64At xs (i + 0))
frontx_compile fitsI16At requires fun _ i => i + 32 < 2 ^ 64
def fitsI16E (xs : ByteArray) : Bool := fitsI16At xs 0
frontx_entry fitsI16E
frontx_implementsC fitsI16E

def insideWAt (xs : ByteArray) (i : Nat) : Bool := LeanSvg.Raster.insideW (((u64At xs (i + 0)).toNat % 2 == 1)) (i64At xs (i + 8))
frontx_compile insideWAt requires fun _ i => i + 32 < 2 ^ 64
def insideWE (xs : ByteArray) : Bool := insideWAt xs 0
frontx_entry insideWE
frontx_implementsC insideWE

def norm2At (xs : ByteArray) (i : Nat) : Int := LeanSvg.Grad.norm2 (i32At xs (i + 0)) (i32At xs (i + 8))
frontx_compile norm2At requires fun _ i => i + 32 < 2 ^ 64
def norm2E (xs : ByteArray) : Int := norm2At xs 0
frontx_entry norm2E
frontx_implementsC norm2E

def clampToAt (xs : ByteArray) (i : Nat) : Int := LeanSvg.Grad.clampTo (i32At xs (i + 0)) (i64At xs (i + 8))
frontx_compile clampToAt requires fun _ i => i + 32 < 2 ^ 64
def clampToE (xs : ByteArray) : Int := clampToAt xs 0
frontx_entry clampToE
frontx_implementsC clampToE

def morphCeilAt (xs : ByteArray) (i : Nat) : Nat := LeanSvg.Filter.morphCeil (i32At xs (i + 0)) ((u64At xs (i + 8)).toNat % 2 ^ 32)
frontx_compile morphCeilAt requires fun _ i => i + 32 < 2 ^ 64
def morphCeilE (xs : ByteArray) : Nat := morphCeilAt xs 0
frontx_entry morphCeilE
frontx_implementsC morphCeilE

end Proven.Frontx.IntEx

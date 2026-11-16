/- `Int` scalars in the word-array front end (`wa_compile`, NOTES section 26): `+ - *`, `/` and `%` (Lean's
`Int.ediv` / `Int.emod`, from the machine's signed `div` / `rem`), `-x`, comparisons (signed), `Int.toNat`,
`Nat` → `Int`, lean-svg's `Fx.floor` / `Fx.ceil` / `Fx.round` (`LeanSvgFixed.lean`, verbatim), an `Int` loop state.
The loops and the byte readers are entry glue (not library code). -/
import Riscv.Frontx.WaMul
import Riscv.Frontx.LeanSvgFixed

namespace WaGlue
/-- a signed 32-bit little-endian number from bytes `o .. o + 3` -/
def rdI32 (xs : ByteArray) (o : Nat) : Int :=
  if rd32 xs o < 2147483648 then (rd32 xs o : Int) else (rd32 xs o : Int) - 4294967296

/-- the `Int` arithmetic on two signed words -/
def iops (a b : Int) : Int := a * b + a / b * 7 - a % b + (-a) + Int.ediv a 3 - Int.emod b 5

/-- `Int` comparisons and `Int.toNat` -/
def icmp (a b : Int) : Nat := (if a < b then 1 else 0) + (if a ≤ b then 2 else 0) + a.toNat

/-- the signed sum of `byte - 100` over the bytes (an `Int` loop state) -/
def sGo (xs : ByteArray) (i : Nat) (acc : Int) : Int :=
  if h : i < xs.size then sGo xs (i + 1) (acc + (xs[i].toNat : Int) - 100) else acc
termination_by xs.size - i
end WaGlue

namespace Proven.WA.IntOps
open Proven.WA WaGlue

def iopsE (xs : ByteArray) : Int := iops (rdI32 xs 0) (rdI32 xs 4)
wa_compile iopsE

def icmpE (xs : ByteArray) : Nat := icmp (rdI32 xs 0) (rdI32 xs 4)
wa_compile icmpE

/-- `Fx.floor`, `Fx.ceil`, `Fx.round` (lean-svg `Fixed.lean:38-40`) of the signed word at byte 0 -/
def fxRoundsE (xs : ByteArray) : Int :=
  LeanSvg.Fx.floor (rdI32 xs 0) * 3 + LeanSvg.Fx.ceil (rdI32 xs 0) * 5 + LeanSvg.Fx.round (rdI32 xs 0)
wa_compile fxRoundsE

def sumDevE (xs : ByteArray) : Int := sGo xs 0 0
wa_compile sumDevE
  invariant fun (xs : ByteArray) (i : Nat) (acc : Int) => i ≤ xs.size ∧ xs.size < 2 ^ 32 ∧
    -100 * (i : Int) ≤ acc ∧ acc ≤ 155 * (i : Int)
  measure fun (xs : ByteArray) (i : Nat) (_acc : Int) => xs.size - i

end Proven.WA.IntOps

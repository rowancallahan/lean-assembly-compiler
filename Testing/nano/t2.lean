import Legacy.Nano.Gen
open Nano
namespace P1
def src : String := "def sq (x : UInt64) : UInt64 := x * x\ndef f (x y : UInt64) : UInt64 := let z := sq x + 3; z * y - 1 - sq (y - 2)"
def sq (x : UInt64) : UInt64 := x * x
def f (x y : UInt64) : UInt64 := let z := sq x + 3; z * y - 1 - sq (y - 2)
theorem bytes_eq : src.toUTF8.toList = src.toList.map (fun c => c.toNat.toUInt8) := by decide +kernel
theorem agree1 : ∀ x y, (nanoElab (src.toList.map (fun c => c.toNat.toUInt8))).bind (·.eval [x, y]) = some (f x y) := by
  intro x y; with_unfolding_all rfl
end P1

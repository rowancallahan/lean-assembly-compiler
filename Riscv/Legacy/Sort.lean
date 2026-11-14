/- The merge sort of `asm/sort.S` against the spec.  `sort_ok` is STATED ONLY (`sorry`). -/
import Riscv.Legacy.SortSteps

namespace Proven

/-- the `sort` function of `asm/sort.S` (words from `asm/sort.dis`, `0x8000003c..0x80000124`) -/
def sortCode : List (BitVec 32) := [
  0x00000293#32, 0x00b2fe63#32, 0x00550333#32, 0x00034383#32, 0x00568333#32, 0x00730023#32,
  0x00128293#32, 0xfe9ff06f#32, 0x00068e13#32, 0x00060e93#32, 0x00100f13#32, 0x08bf7c63#32,
  0x00000f93#32, 0x06bffe63#32, 0x01ef8733#32, 0x00e5f463#32, 0x00058713#32, 0x01e707b3#32,
  0x00f5f463#32, 0x00058793#32, 0x000f8293#32, 0x00070313#32, 0x000f8393#32, 0x04f3f663#32,
  0x02e2f663#32, 0x00f37c63#32, 0x005e0833#32, 0x00084803#32, 0x006e08b3#32, 0x0008c883#32,
  0x0108ea63#32, 0x005e0833#32, 0x00084803#32, 0x00128293#32, 0x0100006f#32, 0x006e0833#32,
  0x00084803#32, 0x00130313#32, 0x007e88b3#32, 0x01088023#32, 0x00138393#32, 0xfb9ff06f#32,
  0x00078f93#32, 0xf89ff06f#32, 0x000e0813#32, 0x000e8e13#32, 0x00080e93#32, 0x001f1f13#32,
  0xf6dff06f#32, 0x02de0263#32, 0x00000293#32, 0x00b2fe63#32, 0x005e0333#32, 0x00034383#32,
  0x00568333#32, 0x00730023#32, 0x00128293#32, 0xfe9ff06f#32, 0x00008067#32]

/-- NOT PROVED (`sorry`): the statement of the goal. -/
theorem sort_ok : Implements sortCode (List.mergeSort (le := fun a b : UInt8 => a ≤ b)) := by
  sorry

end Proven

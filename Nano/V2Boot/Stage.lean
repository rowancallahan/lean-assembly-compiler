/- B₁ (branch nano-v2-boot): moving a stage theorem from the S3 twin to the v2 source function on the inputs the
theorem admits (`x.length ≤ maxLen`). -/
import Spec.Implements1

namespace Nano.V2B
open Proven

theorem implements_congr {code : List (BitVec 32)} {f g : ByteArray → List UInt8} {space : Nat → Nat} {maxLen : Nat}
    {retLen : Bool} (hfg : ∀ a : ByteArray, a.data.toList.length ≤ maxLen → f a = g a)
    (h : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) code f space maxLen retLen) :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) code g space maxLen retLen := by
  intro a s entry ra input output work
  have := h a s entry ra input output work
  intro x y codeR hx
  have hf := hfg a hx
  simp only [x, y, codeR, ← hf] at hx ⊢
  exact this hx

end Nano.V2B

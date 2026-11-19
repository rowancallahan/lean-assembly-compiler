/- Opus box E: the statement `ShiftInv` that the exact out-of-memory threshold (`CompileRunsL`) needs (proof: box D).
`RS p x T hb u` is the kinded meaning of C's main run with heap base `hb` (= work base + 16) and `u` usable bytes above
it (stack top `hb + u`).  `ShiftInv`: whether the run runs out of room does not depend on WHERE the 8-aligned block
lies (in the RAM range the calling convention allows), only on its usable size. -/
import Nano.V2Self.Proof.Machine.NdTop
import Nano.V2Self.Proof.Bridge.SemX
import Nano.V2Self.Proof.Bridge.MainBridge
namespace NanoMain
open Templates ParSpec

/-- C's main run at heap base `hb` with `u` usable bytes -/
def RS (p : List DefA) (x : List UInt8) (T : Buf) (hb u : Nat) : Except Fail (List UInt64 × Hp) :=
  semAtF (pcOf κC hb (UInt64.ofNat x.length) (inpW x) T) p (p.length - 1) [] (hb + u) ⟨hb, fun _ => none⟩

/-- **shift invariance of running out of room** (for parsed linear programs, inputs ≤ 2^20 bytes) -/
def ShiftInv : Prop :=
  ∀ (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 → LinearK p →
  ∀ (x : List UInt8), x.length ≤ 2 ^ 20 → ∀ (T : Buf) (hb hb' u : Nat), hb % 8 = 0 → hb' % 8 = 0 →
    2 ^ 31 ≤ hb → 2 ^ 31 ≤ hb' → hb + u ≤ 2 ^ 32 → hb' + u ≤ 2 ^ 32 →
    (RS p x T hb u = .error .room ↔ RS p x T hb' u = .error .room)

end NanoMain

/- nano-closeA's stages plugged into the six-stage composition (`selfHosted_parse6`, Nano/SelfHostSplit.lean):
stage 1a `vBE` (validator), stage 1b `eBE` (emitter), the expander `nanoExpM` (= `mexp` via `mexp_eq_mx`) and the
assembler `nanoAsm`, all compiled by our front end with their machine theorems.  What remains: stage 2 and the
inliner (box nano-closeB). -/
import Nano.SelfHostSplit
import Nano.ElabBVSelf
import Nano.ElabBESelf
import Nano.ExpandMSelf

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Nano Nano.Link Nano.B Nano.PB

set_option maxRecDepth 100000 in
theorem eBE_code_len : Nano.Self.eBE.code.length < 2 ^ 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem nanoExpM_code_len : Nano.Self.nanoExpM.code.length < 2 ^ 17 := by decide +kernel

theorem vBE_f (x : List UInt8) : Nano.Self.vBE (ofL x) = vB x := rfl
theorem eBE_f (x : List UInt8) : Nano.Self.eBE (ofL x) = eB x := rfl
theorem nanoExpM_f (x : List UInt8) : Nano.Self.nanoExpM (ofL x) = mexp x := (Nano.MX.mexp_eq_mx x).symm

/-- the work-space functions of the compiled stages of box A -/
abbrev s1aA : Nat → Nat := fun _ => 8 * (Nano.Self.vBE.slots + 1) + 7
abbrev s1bA : Nat → Nat := fun _ => 8 * (Nano.Self.eBE.slots + 1) + 7
abbrev smA : Nat → Nat := fun _ => 8 * (Nano.Self.nanoExpM.slots + 1) + 7
abbrev saA : Nat → Nat := fun _ => 8 * (Nano.Self.nanoAsm.slots + 1) + 7

/-- **nano self-hosting, box A's stages compiled**: what remains are the machine theorems of stage 2 and of the
inliner (with their code-size bounds and the conditions `P2`, `Pi` under which they equal `stage2`, `inlB`) -/
theorem selfHosted_closeA {c2 ci : List (BitVec 32)} {f2 fi : ByteArray → List UInt8} {s2 si : Nat → Nat}
    {P2 Pi : List UInt8 → Prop} (K : Nat)
    (h2 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2 f2 s2 (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hc2 : c2.length < 2 ^ 17) (hci : ci.length < 2 ^ 17)
    (hf2 : ∀ x, P2 x → f2 (ofL x) = stage2 x) (hfi : ∀ x, Pi x → fi (ofL x) = U.inlB x) :
    SelfHosted (link (link (link (link (link Nano.Self.vBE.code Nano.Self.eBE.code) c2) ci) Nano.Self.nanoExpM.code)
        Nano.Self.nanoAsm.code)
      (fun _ => space6 K) (Sized6 K s1aA s1bA s2 si smA saA P2 Pi) nanoCompileA :=
  selfHosted_parse6 K Nano.Self.vBE.implements1 Nano.Self.eBE.implements1 h2 hi Nano.Self.nanoExpM.implements1
    Nano.Self.nanoAsm.implements1 eBE_code_len hc2 hci nanoExpM_code_len nanoAsm_code_len vBE_f eBE_f hf2 hfi
    nanoExpM_f (fun _ => rfl)

end Nano.SelfHost

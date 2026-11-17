/- **B₁, hybrid stage set** (branch nano-v2-boot, Testing/notes/NANO_V2_BOOT.md): nano v1's self-hosting composition
`selfHosted_lexA` (Nano/SelfHostFinal.lean) with the inliner, expander and assembler compiled by S3 from the nano v2
SOURCES (`Nano.V2.inlV`, `mexpV`, `asmV`, through their S3 twins); lexA and stage 2b are still the v1 S3 stages until
their v2 sources land on nano-v2-src. Bridges used: twin = v2 source (Nano/V2Boot/*S3.lean), v2 source = v1 function
(worker 3: `asmV_eq`, `mexpV_eq`, `InlP.inlV_eq`), on every input of ≤ 2^20 bytes. -/
import Nano.SelfHostS3
import Nano.V2.InlProof
import Nano.V2Boot.AsmS3Stage
import Nano.V2Boot.ExpandS3Stage
import Nano.V2Boot.InlS3Stage

namespace Nano.V2B
open Proven Nano.Link Nano.SelfHost

/-- the v2 stages, stated for the v1 functions -/
theorem asmB_v1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words AsmB.P)
    (fun xs => Nano.asm xs.data.toList) (Nano.S3Stage.spaceP AsmB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => (asmVS_eq _ (by omega)).trans (Nano.V2.asmV_eq _ (by omega))) asmB_implementsS
theorem expB_v1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ExpB.P)
    (fun xs => Nano.mexp xs.data.toList) (Nano.S3Stage.spaceP ExpB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => (mexpVS_eq _ (by omega)).trans (Nano.V2.mexpV_eq _ (by omega))) expB_implementsS
theorem inlB_v1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words InlB.P)
    (fun xs => Nano.U.inlB xs.data.toList) (Nano.S3Stage.spaceP InlB.P) (2 ^ 20) true :=
  implements_congr (fun _ h => (inlVS_eq _ (by omega)).trans (Nano.V2.InlP.inlV_eq _ (by omega))) inlB_implementsS

noncomputable abbrev siB : Nat → Nat := Nano.S3Stage.spaceP InlB.P
noncomputable abbrev smB : Nat → Nat := Nano.S3Stage.spaceP ExpB.P
noncomputable abbrev saB : Nat → Nat := Nano.S3Stage.spaceP AsmB.P

/-- **B₁ (hybrid)**: v1 lexA, v1 stage 2b, then the v2 inliner, expander, assembler -/
noncomputable def binaryB1 : List (BitVec 32) :=
  link (link (link (link (S3.words Nano.LS.LexA.P) (S3.words Nano.PS.Stage2B.P)) (S3.words InlB.P))
    (S3.words ExpB.P)) (S3.words AsmB.P)

def DomainB1 (K : Nat) (src : List UInt8) : Prop := SizedL K sLex s2bF siB smB saB src ∧ LeanLimits src

end Nano.V2B

namespace Nano
open Proven Nano.SelfHost Nano.V2B

/-- **`Nano.selfHostedB1`**: the hybrid B₁ is a nano compiler on `DomainB1 K` (Sail model) -/
theorem selfHostedB1 (K : Nat) : SelfHosted binaryB1 (fun _ => space5 K) (DomainB1 K) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_lexA K Nano.LS.lexA_implements Nano.PS.stage2B_implements inlB_v1 expB_v1 asmB_v1
      Nano.PS.stage2B_code_len inlB_code_len expB_code_len asmB_code_len Nano.LS.lexA_f (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    fun _ h => h.1

end Nano

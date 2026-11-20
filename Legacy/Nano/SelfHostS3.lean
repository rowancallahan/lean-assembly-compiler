/- **`Nano.selfHostedS3`** (branch nano-s3-all, ROADMAP ORDER step 2): nano self-hosting with ALL FIVE stages compiled
by the S3 compiler (proved once; per stage only a Lean bridge and kernel evaluation of the compiler on the program):
1. `lexA` = `stage2a ∘ lexB` (`Nano.LS.lexA_implements`, Nano/LexS3Stage.lean);
2. `stage2b` (`Nano.PS.stage2B_implements`, Nano/ParseS3BStage.lean);
3. the inliner `inlB` (`Nano.IS.inlS3_implements`, Nano/InlS3Stage.lean);
4. the expander `mexp`, verbatim (`Nano.XS.expS3_implements`, Nano/ExpS3Stage.lean);
5. the assembler `asm` via `asmS` (`asmS_eq`) (`Nano.AS.asmS3_implements`, Nano/AsmS3Stage.lean).
The composition is `selfHosted_lexA` (Nano/SelfHostFinal.lean), the same statement shape as `Nano.selfHosted`; the
domain `DomainS3 K` is explicit: the size bounds of every intermediate result and work space (`SizedL`, with the S3
stages' work spaces) and `LeanLimits`. -/
import Legacy.Nano.SelfHostFinal
import Legacy.Nano.ExpS3Stage
import Legacy.Nano.AsmS3Stage

namespace Nano.SelfHost
open Proven Nano.Link

/-- the work spaces of the S3 expander and assembler -/
noncomputable abbrev smS : Nat → Nat := Nano.S3Stage.spaceP Nano.XS.ExpS3.P
noncomputable abbrev saS : Nat → Nat := Nano.S3Stage.spaceP Nano.AS.AsmS3.P

/-- **the self-hosted nano compiler, every stage through S3, as one RISC-V binary** -/
noncomputable def binaryS3 : List (BitVec 32) :=
  link (link (link (link (Proven.S3.words Nano.LS.LexA.P) (Proven.S3.words Nano.PS.Stage2B.P))
    (Proven.S3.words Nano.IS.InlS3.P)) (Proven.S3.words Nano.XS.ExpS3.P)) (Proven.S3.words Nano.AS.AsmS3.P)

/-- the domain: the size bounds of every stage (`K` bounds every intermediate result and work space) and the limits of
Lean's own elaborator -/
def DomainS3 (K : Nat) (src : List UInt8) : Prop := SizedL K sLex s2bF siF smS saS src ∧ LeanLimits src

end Nano.SelfHost

namespace Nano
open Proven Nano.SelfHost Nano.Link

/-- **`Nano.selfHostedS3`**: the binary `binaryS3` (five stages, each compiled by the S3 compiler, linked) is a nano
compiler: on every source in `DomainS3 K` it computes, on the Sail RV64 model, exactly what `nanoCompileA` produces for
the program the specification elaborator reads from the source. -/
theorem selfHostedS3 (K : Nat) : SelfHosted binaryS3 (fun _ => space5 K) (DomainS3 K) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_lexA K Nano.LS.lexA_implements Nano.PS.stage2B_implements Nano.IS.inlS3_implements
      Nano.XS.expS3_implements Nano.AS.asmS3_implements Nano.PS.stage2B_code_len Nano.IS.inlS3_code_len
      Nano.XS.expS3_code_len Nano.AS.asmS3_code_len Nano.LS.lexA_f (fun _ => rfl) Nano.IS.inlS3_f
      Nano.XS.expS3_f Nano.AS.asmS3_f)
    fun _ h => h.1

end Nano

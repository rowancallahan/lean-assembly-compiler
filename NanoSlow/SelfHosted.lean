/- **`Nano.selfHosted`** (pending: NOT in the default build): the instance of `selfHosted_s3` (Nano/SelfHostS3.lean)
with the S3-compiled front stage `lexA` (NanoSlow/LexS3Stage.lean). It is here, not in `Nano`, because the S3 compile
of `lexA` (NanoSlow/LexS3Self.lean, `s3_compileF`) did not finish within 10 min (owner rule: ≤ 5 min per stage);
box nano-final owns the speed-up / split of `lexA`. Once it builds in ≤ 5 min, the three files move back to `Nano/`. -/
import Nano.SelfHostS3
import NanoSlow.LexS3Stage

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link

/-- the work space of the S3-compiled front stage -/
noncomputable abbrev sAS3 : Nat → Nat := Nano.S3Stage.spaceP Nano.LS.LexA.P

/-- the self-hosted binary: front (lexer + parser 2a), parser 2b, inliner (all three through S3), expander,
assembler -/
noncomputable abbrev binary : List (BitVec 32) :=
  link (link (link (link (Proven.S3.words Nano.LS.LexA.P) (Proven.S3.words Nano.PS.Stage2B.P))
    (Proven.S3.words Nano.IS.InlS3.P)) Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code

/-- the explicit domain: the size conditions of the five stages (`Sized5S`) and the limits of Lean's elaborator -/
def Domain (K : Nat) (src : List UInt8) : Prop := Sized5S K sAS3 s2bS3 siS3 smE saE src ∧ LeanLimits src

end Nano.SelfHost

namespace Nano
open Nano.SelfHost

/-- **nano is self-hosted** (no hypotheses; the domain is explicit): `binary` (five compiled stages, three of them
through S3), run on the Sail model on a source in `Domain K`, emits `nanoGen p`, and that code computes `p.eval`
(`SelfHosted`, Nano/SelfHost.lean) -/
theorem selfHosted (K : Nat) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA :=
  selfHosted_s3 K Nano.LS.lexA_implements Nano.LS.lexA_f

end Nano

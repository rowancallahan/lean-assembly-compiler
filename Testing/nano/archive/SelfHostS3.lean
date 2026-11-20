/- nano self-hosting, FIVE stages (`selfHosted_parse5S`, Nano/SelfHostSplit5.lean): the front end `lexA` (lexer + parser
2a, `stage2a ∘ lexB`, box nano-final, S3), the parser machine 2b (`stage2b`, THROUGH S3:
`Nano.PS.stage2B_implements`), the inliner (THROUGH S3: `Nano.IS.inlS3_implements`), the expander
(`Nano.Self.nanoExpM`) and the assembler (`Nano.Self.nanoAsm`). `Testing/notes/NANO_PARSE_S3.md`, NANO_MANIFEST.md.

The domain also states the limits of Lean's own elaborator (owner's request, NANO.md "RESOURCE LIMITS": Lean fails
on ≥ 512 nested `let`s, ≥ 256 nested calls, chains of ≥ ~3000 operands): `LeanLimits src` bounds the elaborated
program's nesting (lets, calls at cost 2, right-nested operands) by 400 and its left operator chains by 2500. It only
narrows the domain (`SelfHosted.mono`); `nanoElab` (the spec) is unchanged. -/
import Legacy.Nano.SelfHostSplit5
import Legacy.Nano.ParseS3BStage
import Legacy.Nano.InlS3Stage
import Legacy.Nano.ExpandMSelf
import Legacy.Nano.ParseBSelfHost
import Legacy.Nano.LeanLimits

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.B Nano.PB

set_option maxRecDepth 100000 in
theorem nanoExpM_code_len_s3 : Nano.Self.nanoExpM.code.length < 2 ^ 17 := by decide +kernel

theorem nanoExpM_f_s3 (x : List UInt8) : Nano.Self.nanoExpM (ofL x) = mexp x := (Nano.MX.mexp_eq_mx x).symm

/-- the work spaces of the compiled stages -/
noncomputable abbrev s2bS3 : Nat → Nat := Nano.S3Stage.spaceP Nano.PS.Stage2B.P
noncomputable abbrev siS3 : Nat → Nat := Nano.S3Stage.spaceP Nano.IS.InlS3.P
abbrev smE : Nat → Nat := fun _ => 8 * (Nano.Self.nanoExpM.slots + 1) + 7
abbrev saE : Nat → Nat := fun _ => 8 * (Nano.Self.nanoAsm.slots + 1) + 7

/-- **nano self-hosting, parser 2b and the inliner through S3**: what remains is the front stage's machine theorem
(lexer + parser 2a: `= stage2a ∘ lexB` on every input) -/
theorem selfHosted_s3 {cA : List (BitVec 32)} {fA : ByteArray → List UInt8} {sA : Nat → Nat} (K : Nat)
    (hA : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cA fA sA (2 ^ 20) true)
    (hfA : ∀ x, fA (ofL x) = Nano.PS.stage2a (lexB x)) :
    SelfHosted (link (link (link (link cA (Proven.S3.words Nano.PS.Stage2B.P)) (Proven.S3.words Nano.IS.InlS3.P))
        Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code)
      (fun _ => space5S K) (fun src => Sized5S K sA s2bS3 siS3 smE saE src ∧ LeanLimits src) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_parse5S K hA Nano.PS.stage2B_implements Nano.IS.inlS3_implements Nano.Self.nanoExpM.implements1
      Nano.Self.nanoAsm.implements1 Nano.PS.stage2B_code_len Nano.IS.inlS3_code_len nanoExpM_code_len_s3
      nanoAsm_code_len hfA (fun _ => rfl) Nano.IS.inlS3_f nanoExpM_f_s3 (fun _ => rfl))
    fun _ h => h.1

end Nano.SelfHost

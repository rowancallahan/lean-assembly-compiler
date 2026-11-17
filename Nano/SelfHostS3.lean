/- nano self-hosting with stage 2 (the parser) compiled THROUGH S3 (`Nano.PS.stage2S3_implements`,
Nano/ParseS3Self.lean) plugged into box A's composition (`selfHosted_closeA`: lexer halves `vB`/`eB`, expander,
assembler, compiled by the list front end). `Testing/notes/NANO_PARSE_S3.md`.

The domain also states the limits of Lean's own elaborator (owner's request, NANO.md "RESOURCE LIMITS": Lean fails
on ≥ 512 nested `let`s, ≥ 256 nested calls, chains of ≥ ~3000 operands): `LeanLimits src` bounds the elaborated
program's nesting (lets, calls at cost 2, right-nested operands) by 400 and its left operator chains by 2500. It only
narrows the domain (`SelfHosted.mono`); `nanoElab` (the spec) is unchanged. -/
import Nano.SelfHostedA
import Nano.ParseS3Stage
import Nano.InlS3Stage

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.B Nano.PB

/-- nesting of an expression: `let` bodies, call arguments (cost 2), right operands (parenthesized) -/
def nest : Ex → Nat
  | .num _ => 0
  | .var _ => 0
  | .add a b => max (nest a) (nest b + 1)
  | .sub a b => max (nest a) (nest b + 1)
  | .mul a b => max (nest a) (nest b + 1)
  | .let_ v b => max (nest v + 1) (nest b + 1)
  | .call b as => max (nest b) (nest as + 2)
  | .anil => 0
  | .acons e r => max (nest e) (nest r)

/-- the longest chain of left-nested binary operators -/
def chain : Ex → Nat
  | .num _ => 0
  | .var _ => 0
  | .add a b => max (chain a + 1) (chain b)
  | .sub a b => max (chain a + 1) (chain b)
  | .mul a b => max (chain a + 1) (chain b)
  | .let_ v b => max (chain v) (chain b)
  | .call b as => max (chain b) (chain as)
  | .anil => 0
  | .acons e r => max (chain e) (chain r)

/-- **the limits of Lean's elaborator**, stated on the elaborated program -/
def LeanLimits (src : List UInt8) : Prop :=
  ∀ p, nanoElab src = some p → nest p.2 ≤ 400 ∧ chain p.2 ≤ 2500

/-- a smaller domain -/
theorem SelfHosted.mono {B : List (BitVec 32)} {space : Nat → Nat} {D D' : List UInt8 → Prop}
    {compile : Prog → Option CompiledA} (h : SelfHosted B space D compile) (hD : ∀ s, D' s → D s) :
    SelfHosted B space D' compile where
  code := h.code
  emits src p c hd := h.emits src p c (hD src hd)
  correct := h.correct
  correctInt := h.correctInt
  runs := h.runs

/-- the work space of the S3-compiled parser stage -/
noncomputable abbrev s2S3 : Nat → Nat := Nano.S3Stage.spaceP Nano.PS.Stage2S3.P

/-- **nano self-hosting with the parser compiled through S3**: what remains is the inliner's machine theorem (its
code-size bound and the condition `Pi` under which it equals `inlB`) -/
theorem selfHosted_s3 {ci : List (BitVec 32)} {fi : ByteArray → List UInt8} {si : Nat → Nat}
    {Pi : List UInt8 → Prop} (K : Nat)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hci : ci.length < 2 ^ 17) (hfi : ∀ x, Pi x → fi (ofL x) = U.inlB x) :
    SelfHosted (link (link (link (link (link Nano.Self.vBE.code Nano.Self.eBE.code)
        (Proven.S3.words Nano.PS.Stage2S3.P)) ci) Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code)
      (fun _ => space6 K)
      (fun src => Sized6 K s1aA s1bA s2S3 si smA saA (fun _ => True) Pi src ∧ LeanLimits src) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_closeA (P2 := fun _ => True) K Nano.PS.stage2S3_implements hi Nano.PS.stage2S3_code_len hci
      (fun x _ => Nano.PS.stage2S3_f x) hfi)
    fun _ h => h.1

/-- the work space of the S3-compiled inliner stage -/
noncomputable abbrev siS3 : Nat → Nat := Nano.S3Stage.spaceP Nano.IS.InlS3.P

/-- the self-hosted binary: lexer halves, parser (S3), inliner (S3), expander, assembler -/
noncomputable abbrev binary : List (BitVec 32) :=
  link (link (link (link (link Nano.Self.vBE.code Nano.Self.eBE.code) (Proven.S3.words Nano.PS.Stage2S3.P))
    (Proven.S3.words Nano.IS.InlS3.P)) Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code

/-- the explicit domain: the size conditions of the six stages (`Sized6`; the parser and the inliner equal their
Lean functions on every input) and the limits of Lean's elaborator -/
def Domain (K : Nat) (src : List UInt8) : Prop :=
  Sized6 K s1aA s1bA s2S3 siS3 smA saA (fun _ => True) (fun _ => True) src ∧ LeanLimits src

end Nano.SelfHost

namespace Nano
open Nano.SelfHost

/-- **nano is self-hosted** (no hypotheses; the domain is explicit): the binary `binary` (six compiled stages,
the parser and the inliner compiled through S3), run on the Sail model on a source in `Domain K`, emits `nanoGen p`;
that code computes `p.eval` (`SelfHosted`, Nano/SelfHost.lean) -/
theorem selfHosted (K : Nat) : SelfHosted binary (fun _ => space6 K) (Domain K) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_closeA (P2 := fun _ => True) (Pi := fun _ => True) K Nano.PS.stage2S3_implements
      Nano.IS.inlS3_implements Nano.PS.stage2S3_code_len Nano.IS.inlS3_code_len
      (fun x _ => Nano.PS.stage2S3_f x) (fun x _ => Nano.IS.inlS3_f x))
    fun _ h => h.1

end Nano

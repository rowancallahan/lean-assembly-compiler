/- **`Nano.selfHosted`**: nano self-hosting, every stage compiled by our compilers with its machine theorem
(branch nano-final). FIVE stages, linked by `link_stage`:
1. `lexA` = stage 1 and parser 2a together (`stage2a ∘ lexB`), THROUGH S3 (`Nano.LS.lexA_implements`, Nano/LexS3Stage.lean);
2. `stage2b`, the parser machine, THROUGH S3 (`Nano.PS.stage2B_implements`);
3. the inliner `inlB`, THROUGH S3 (`Nano.IS.inlS3_implements`);
4. the expander `mexp` (front end, listCS: `Nano.Self.nanoExpM.implements1`);
5. the assembler `asm` (front end: `Nano.Self.nanoAsm.implements1`).
`stage2b (stage2a (lexB src)) = stage2 (lexB src) = serU u` (`stage2b_stage2a`, `stage2_hfe`), then the inliner, the
expander and the assembler give `nanoGen p` (`chain_eq`). The domain: the elaborator accepts the source, the size
bounds of every intermediate result and work space (`SizedL`), and `LeanLimits` (Lean's own elaborator limits). -/
import Nano.LexS3Stage
import Nano.ParseS3BStage
import Nano.InlS3Stage
import Nano.ExpandMSelf
import Nano.ParseBSelfHost
import Nano.LeanLimits

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link Nano.U Nano.B Nano.PB Nano.PS

/-- the size conditions of the five-stage binary (`lexA` first) on a source -/
def SizedL (K : Nat) (s1 s2 si sm sa : Nat → Nat) (src : List UInt8) : Prop :=
  ∃ u, nanoElabU src = some u ∧ (∀ d ∈ u, d.1 < 256) ∧ u.length ≤ 65536 ∧
    (stage2a (lexB src)).length ≤ 2 ^ 20 ∧ (stage2a (lexB src)).length ≤ K ∧ s1 src.length ≤ K ∧
    s2 (stage2a (lexB src)).length ≤ K ∧
    (serU u).length ≤ 2 ^ 20 ∧ (serU u).length ≤ K ∧ si (serU u).length ≤ K ∧
    (inlB (serU u)).length ≤ 2 ^ 20 ∧ (inlB (serU u)).length ≤ K ∧ sm (inlB (serU u)).length ≤ K ∧
    (mexp (inlB (serU u))).length ≤ 2 ^ 20 ∧ (mexp (inlB (serU u))).length ≤ K ∧
    sa (mexp (inlB (serU u))).length ≤ K

/-- the work space of the five-stage binary -/
def space5 (K : Nat) : Nat := 4 * (4 * (4 * (4 * K + 96) + 96) + 96) + 96

set_option maxRecDepth 20000 in
theorem selfHosted_lexA {c1 c2 ci cm ca : List (BitVec 32)} {f1 f2 fi fm fa : ByteArray → List UInt8}
    {s1 s2 si sm sa : Nat → Nat} (K : Nat)
    (h1 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c1 f1 s1 (2 ^ 20) true)
    (h2 : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) c2 f2 s2 (2 ^ 20) true)
    (hi : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ci fi si (2 ^ 20) true)
    (hm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) cm fm sm (2 ^ 20) true)
    (ha : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) ca fa sa (2 ^ 20) true)
    (hc2 : c2.length < 2 ^ 17) (hci : ci.length < 2 ^ 17) (hcm : cm.length < 2 ^ 17) (hca : ca.length < 2 ^ 17)
    (hf1 : ∀ x, f1 (ofL x) = stage2a (lexB x)) (hf2 : ∀ x, f2 (ofL x) = stage2b x)
    (hfi : ∀ x, fi (ofL x) = inlB x) (hfm : ∀ x, fm (ofL x) = mexp x) (hfa : ∀ x, fa (ofL x) = asm x) :
    SelfHosted (link (link (link (link c1 c2) ci) cm) ca) (fun _ => space5 K) (SizedL K s1 s2 si sm sa)
      nanoCompileA := by
  have hfe : ∀ src u, nanoElabU src = some u → f2 (ofL (f1 (ofL src))) = serU u := fun src u hu => by
    rw [hf1, hf2, stage2b_stage2a, stage2_hfe src u hu]
  have h0 := link_stage (α := SrcIn (SizedL K s1 s2 si sm sa)) K (comap h1 fun s => ofL s.1) h2 hc2 fun a _ => by
    obtain ⟨u, hu, -, -, b1, b2, b3, b4, -⟩ := a.2
    show (f1 (ofL a.1)).length ≤ 2 ^ 20 ∧ (f1 (ofL a.1)).length ≤ K ∧ s1 (ofL a.1).data.toList.length ≤ K ∧
      s2 (f1 (ofL a.1)).length ≤ K
    rw [hf1]; exact ⟨b1, b2, b3, b4⟩
  have h01 := link_stage (4 * K + 96) h0 hi hci fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, b5, b6, b7, -⟩ := a.2
    rw [hfe a.1 u hu]; exact ⟨b5, by omega, by omega, Nat.le_trans b7 (by omega)⟩
  have h02 := link_stage (4 * (4 * K + 96) + 96) h01 hm hcm fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, b8, b9, b10, -⟩ := a.2
    rw [hfe a.1 u hu, hfi]; exact ⟨b8, by omega, by omega, Nat.le_trans b10 (by omega)⟩
  have h03 := link_stage (4 * (4 * (4 * K + 96) + 96) + 96) h02 ha hca fun a _ => by
    obtain ⟨u, hu, -, -, -, -, -, -, -, -, -, -, -, -, b11, b12, b13⟩ := a.2
    rw [hfe a.1 u hu, hfi, hfm]; exact ⟨b11, by omega, by omega, Nat.le_trans b13 (by omega)⟩
  refine selfHosted_stack (cb := fun src => fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1 (ofL src)))))))))) h03
    fun src p hD hp => ?_
  obtain ⟨u, hu, hb, hl, -⟩ := hD
  obtain ⟨u', hu', hc⟩ := chain_eq src p hp
  rw [hu] at hu'; cases hu'
  show fa (ofL (fm (ofL (fi (ofL (f2 (ofL (f1 (ofL src))))))))) = nanoGen p
  rw [hfe src u hu, hfi, hfm, hfa]; exact hc hb hl

set_option maxRecDepth 100000 in
theorem nanoExpM_code_len' : Nano.Self.nanoExpM.code.length < 2 ^ 17 := by decide +kernel

/-- the work spaces of the five compiled stages -/
noncomputable abbrev sLex : Nat → Nat := Nano.S3Stage.spaceP Nano.LS.LexA.P
noncomputable abbrev s2bF : Nat → Nat := Nano.S3Stage.spaceP Nano.PS.Stage2B.P
noncomputable abbrev siF : Nat → Nat := Nano.S3Stage.spaceP Nano.IS.InlS3.P
abbrev smF : Nat → Nat := fun _ => 8 * (Nano.Self.nanoExpM.slots + 1) + 7
abbrev saF : Nat → Nat := fun _ => 8 * (Nano.Self.nanoAsm.slots + 1) + 7

/-- **the self-hosted nano compiler, as one RISC-V binary** -/
def binary : List (BitVec 32) :=
  link (link (link (link (Proven.S3.words Nano.LS.LexA.P) (Proven.S3.words Nano.PS.Stage2B.P))
    (Proven.S3.words Nano.IS.InlS3.P)) Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code

/-- the domain: the size bounds of every stage (`K` bounds every intermediate result and work space) and the limits of
Lean's own elaborator -/
def Domain (K : Nat) (src : List UInt8) : Prop := SizedL K sLex s2bF siF smF saF src ∧ LeanLimits src

end Nano.SelfHost

namespace Nano
open Proven Nano.SelfHost Nano.Link

/-- **`Nano.selfHosted`**: the binary `binary` (five stages compiled by our compilers and linked) is a nano compiler:
on every source in `Domain K` it computes, on the Sail RV64 model, exactly what `nanoCompileA` (the proved compiler of
nano programs) produces for the program the specification elaborator `nanoElab` reads from the source. -/
theorem selfHosted (K : Nat) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA :=
  SelfHosted.mono
    (selfHosted_lexA K Nano.LS.lexA_implements Nano.PS.stage2B_implements Nano.IS.inlS3_implements
      Nano.Self.nanoExpM.implements1 Nano.Self.nanoAsm.implements1 Nano.PS.stage2B_code_len Nano.IS.inlS3_code_len
      nanoExpM_code_len' nanoAsm_code_len Nano.LS.lexA_f (fun _ => rfl) Nano.IS.inlS3_f
      (fun x => (Nano.MX.mexp_eq_mx x).symm) (fun _ => rfl))
    fun _ h => h.1

end Nano

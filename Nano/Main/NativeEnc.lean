/- **The native AArch64 compile, option E**: `compileOn enc` for a translator `enc` of Gen's bytes that meets `EncOKN`:
on the bytes of a J program `Cj` (JOK, < 2^18 instructions) it emits the specification encoder's bytes `natEncJ Cj`
(Run/NatEnc.lean), or nothing.  Same slot as `EncOK` for rv2arm (Main/TopOn.lean); the nano-subset translator is the
instance (its program proof gives `EncOKN`).  The image relation holds by construction (`natEncJ_img`).
`CjUnique` (Run/CjUnique.lean: `cjUnique`; a fact about Gen's word encoding only): Gen's bytes determine the J program —
needed because `GenOKG` fixes the image before the J program is known.
`C_correct_nativeE` / `C_runs_nativeE`: from `A64SemN` and `EncOKN` alone (the native laws are `natLawsOK`,
Run/NatSeg.lean). -/
import Nano.Main.TopOn
import Nano.Run.NatSeg
import Nano.Run.NatEnc
import Nano.Run.CjUnique
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

/-- Gen's bytes determine the J program -/
def CjUnique : Prop :=
  ∀ (c c' : List UInt8) (Cj Cj' : List CallProbe.J), Cj.length < 2 ^ 18 → Cj'.length < 2 ^ 18 →
    (∀ j ∈ Cj, SimW.JOK j) → (∀ j ∈ Cj', SimW.JOK j) →
    C.g40 16777216 c (Cj.map CallProbe.encG) 0 [] = C.g40 16777216 c' (Cj'.map CallProbe.encG) 0 [] → Cj = Cj'

/-- `enc` turns Gen's bytes for its J program `Cj` into the native encoder's bytes for `Cj` -/
def EncOKN (enc : List UInt8 → List UInt8) : Prop :=
  enc [] = [] ∧
  ∀ (c : List UInt8) (Cj : List CallProbe.J), Cj.length < 2 ^ 18 → (∀ j ∈ Cj, SimW.JOK j) →
    enc (C.g40 16777216 c (Cj.map CallProbe.encG) 0 []) ≠ [] →
    natEncJ Cj = some (enc (C.g40 16777216 c (Cj.map CallProbe.encG) 0 []))

variable {M : Machine} {X W : M.State → Nat → Prop}

theorem genOKG_enc (U : CjUnique) {enc : List UInt8 → List UInt8} (hE : EncOKN enc) :
    GenOKG (natTarget M X W NatV) (enc ∘ mC) := fun x hx => by
  have hx' : enc (mC x) ≠ [] := hx
  have hm : mC x ≠ [] := fun e => hx' (by rw [e]; exact hE.1)
  by_cases hex : ∃ (c : List UInt8) (Cj : List CallProbe.J), Cj.length < 2 ^ 18 ∧ (∀ j ∈ Cj, SimW.JOK j) ∧
      mC x = C.g40 16777216 c (Cj.map CallProbe.encG) 0 []
  · obtain ⟨c, Cj, hl, hj, e⟩ := hex
    have hn := hE.2 c Cj hl hj (by rw [← e]; exact hx')
    obtain ⟨I, hI, hV⟩ := natEncJ_img hn
    refine ⟨hm, fun _ => ⟨I, by rw [hI, ← e]; rfl, fun c' Cj' h1 h2 h3 => ?_⟩⟩
    have : Cj' = Cj := U c' c Cj' Cj h1 hl h2 hj (h3.symm.trans e)
    rw [this]; exact hV
  · exact ⟨hm, fun _ => ⟨⟨enc (mC x), CallProbe.LinkLay.lin 0, fun _ => True, fun _ _ => False⟩, rfl,
      fun c Cj h1 h2 h3 => absurd ⟨c, Cj, h1, h2, h3⟩ hex⟩⟩

/-- **the native compile is correct on AArch64** (option E), for any machine with the A64 steps and any translator
that meets `EncOKN` -/
theorem C_correct_nativeE (S : A64SemN M X W) (enc : List UInt8 → List UInt8) (hE : EncOKN enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileCorrectP M (ArmLoader X W) (compileOn enc) :=
  C_correct_g (natLaws S (natLawsOK S)) (enc ∘ mC) (genOKG_enc cjUnique hE) hwin

/-- **the native compile runs correctly on AArch64, with any work block** (option E) -/
theorem C_runs_nativeE (S : A64SemN M X W) (enc : List UInt8 → List UInt8) (hE : EncOKN enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileRunsP M (ArmLoader X W) (compileOn enc) :=
  C_runs_g (natLaws S (natLawsOK S)) (enc ∘ mC) (genOKG_enc cjUnique hE) hwin

end NanoMain

/- Nano/V2Self/Proof/ParRunDef: Layer-2 def level (parser lead), pure.  Expression-family frames never emit output; a plain def
from `.binders` to the next `.defs` is `pDef`'s plain branch (`plainB_spec`). -/
import Nano.V2Self.Proof.ParRunBody
import Nano.V2Self.Proof.ParRunShape
import Nano.V2Self.Proof.ParTreeOK
namespace ParRun
open ParSpec

/-- frames that write output -/
def isOutF : Frame → Bool
  | .defEnd | .flat _ | .flatL _ | .defClose => true
  | _ => false

/-- a frame that is neither def-level nor an output frame keeps the output and pushes only such frames -/
theorem stepF_noOut {f : Frame} {st st' : St} {k : List Frame} (hD : isD f = false) (hO : isOutF f = false)
    (h : stepF f st = some (k, st')) : st'.out = st.out ∧ k.all (fun g => !isD g && !isOutF g) = true := by
  cases f <;> simp only [isD, isOutF] at hD hO <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases hD; done)
    | (cases hO; done)
    | (cases h; done)
    | (cases h; exact ⟨rfl, by decide⟩)
    | (cases h; exact ⟨rfl, by simp [isD, isOutF]⟩)
    | (cases h; exact ⟨by simp [leaf], by simp [isD, isOutF]⟩)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       refine ⟨?_, by simp [isD, isOutF]⟩
       first
       | (rw [mkNode_out h2]; done)
       | (rw [locOf_out h2]; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          rw [mkNode_out h2', mkNode_out h1]; done))

/-- runs of such frames keep the output -/
theorem Star.noOut {c d : List Frame × St} (h : Star c d) (hk : c.1.all (fun g => !isD g && !isOutF g) = true) :
    d.2.out = c.2.out ∧ d.1.all (fun g => !isD g && !isOutF g) = true := by
  induction h with
  | refl => exact ⟨rfl, hk⟩
  | @step c c1 d hs _ ih =>
    obtain ⟨fs, st⟩ := c
    cases fs with
    | nil => simp [stepS] at hs
    | cons f rest =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
      obtain ⟨⟨hD, hO⟩, hr⟩ := hk
      obtain ⟨e1, e2⟩ := stepF_noOut hD hO h1
      obtain ⟨e3, e4⟩ := ih (by simp [List.all_append, e2, hr])
      exact ⟨e3.trans e1, e4⟩

end ParRun

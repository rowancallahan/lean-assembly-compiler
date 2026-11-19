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


theorem pBinders_noLs : ∀ (f : Nat) (b : Bool) (ts : List Tok) (g : List (List (List Nat) × TyR)) (r : List Tok),
    pBinders f b ts = some (g, r) → ∀ x ∈ g, x.2 ≠ .sh .ls := by
  intro f
  induction f with
  | zero => intro b ts g r h; simp [pBinders] at h
  | succ f ih =>
    intro b ts g r h x hx
    rw [pBinders.eq_def] at h
    simp only at h
    split at h
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hx; done)
      | (obtain rfl : f = _ := Nat.succ.inj ‹f + 1 = _›
         obtain ⟨⟨ns, r1⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h
         simp only at h2
         split at h2
         · obtain ⟨⟨t, r3⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
           simp only at h4
           split at h4
           all_goals first
             | (cases h4; done)
             | (obtain ⟨⟨g', r5⟩, h5, h6⟩ := Option.map_eq_some_iff.mp h4
                simp only [Prod.mk.injEq] at h6; obtain ⟨rfl, rfl⟩ := h6
                rcases List.mem_cons.mp hx with rfl | hx
                · exact (pTy_noLs f).2 _ _ _ h3
                · exact ih _ _ _ _ h5 x hx)
         · cases h2)

theorem mem_go_kind (p : Ps) : ∀ (s : Nat) (ns : List (List Nat)) (e : List Nat × Nat × Ps), e ∈ (bindSlots.go p s ns).1 → e.2.2 = p := by
  intro s ns e he
  induction ns generalizing s with
  | nil => simp [go_nil] at he
  | cons x l ih =>
    rw [go_cons] at he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih _ he

theorem mem_bindSlots_kind : ∀ (g : List (List (List Nat) × TyR)) (s : Nat) (u : Bool) (e : List Nat × Nat × Ps),
    e ∈ (bindSlots s u g).1 → e.2.2 ∈ (bindSlots s u g).2.1
  | [], s, u, e, he => by simp [bindSlots_nil] at he
  | (ns, t) :: g, s, u, e, he => by
    rw [bindSlots_cons] at he ⊢
    rcases List.mem_append.mp he with he | he
    · apply List.mem_append_left
      rw [mem_go_kind _ _ _ _ he, go_ps]
      cases ns with
      | nil => simp [go_nil] at he
      | cons y l => simp
    · exact List.mem_append_right _ (mem_bindSlots_kind g _ _ e he)

end ParRun

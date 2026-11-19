/- Nano/V2Self/Proof/ParRunBnd: Layer-2 bounds along runs (parser lead), for `ParInvRun.Obl`.
`reach_prim32`: every prim callee on the task stack is < 2^32 (in fact < 10). -/
import Nano.V2Self.Proof.ParRunCInv
namespace ParRun
open ParSpec

def Callee.small : Callee → Bool
  | .pr p => decide (p < 2 ^ 32)
  | .df _ => true

def Frame.prOK : Frame → Bool
  | .args c _ | .mkCallN c _ | .argCheck c _ | .mkCall c _ => c.small
  | _ => true

theorem stepF_pr {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hf : f.prOK = true) :
    k.all Frame.prOK = true := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp [Frame.prOK, Callee.small] at hf ⊢; try omega)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3; simp [Frame.prOK])

theorem Star.pr {c d : List Frame × St} (h : Star c d) (hi : c.1.all Frame.prOK = true) : d.1.all Frame.prOK = true := by
  induction h with
  | refl => exact hi
  | @step c c1 d hs _ ih =>
    apply ih
    obtain ⟨fs, st⟩ := c
    cases fs with
    | nil => simp [stepS] at hs
    | cons f rest =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      simp only [List.all_cons, Bool.and_eq_true] at hi
      simp only [List.all_append, Bool.and_eq_true]; exact ⟨stepF_pr h1 hi.1, hi.2⟩

/-- prim callees of the top call frames are small -/
theorem reach_prim32 {toks : List Tok} {f : Frame} {fs : List Frame} {st : St} {p : Nat}
    (h : Star ([.defs], init toks) (f :: fs, st)) (hf : ∃ k, f = .argCheck (.pr p) k ∨ f = .mkCall (.pr p) k) : p < 2 ^ 32 := by
  have := h.pr rfl
  simp only [List.all_cons, Bool.and_eq_true] at this
  obtain ⟨k, rfl | rfl⟩ := hf <;> simpa [Frame.prOK, Callee.small] using this.1

/-- non-input parameters are parameters -/
def NniOK (st : St) : Prop := st.cur.nni ≤ st.cur.params.length

theorem mkNode_cur' {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : st'.cur = st.cur := by
  unfold mkNode at h; split at h <;> cases h; rfl

theorem locOf_cur' {st st' : St} {bd : Bd} (h : locOf st bd = some st') : st'.cur = st.cur := by
  unfold locOf at h; split at h <;> cases h; rfl

theorem stepF_nni {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hi : NniOK st) : NniOK st' := by
  unfold NniOK at hi ⊢
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; first | exact hi | (simp at hi ⊢; done) | (simp [DefR.fresh] at hi ⊢; done) | (simp at hi ⊢; omega))
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
         | (rw [mkNode_cur' h2]; exact hi)
         | (rw [locOf_cur' h2]; exact hi)
         | (obtain ⟨s1, a1, a2⟩ := Option.bind_eq_some_iff.mp h2; rw [mkNode_cur' a2, mkNode_cur' a1]; exact hi))

theorem reach_nni {toks : List Tok} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (fs, st)) : NniOK st := by
  have : ∀ {c d : List Frame × St}, Star c d → NniOK c.2 → NniOK d.2 := by
    intro c d h
    induction h with
    | refl => exact id
    | @step c c1 d hs _ ih =>
      intro hi; apply ih
      obtain ⟨fs, st⟩ := c
      cases fs with
      | nil => simp [stepS] at hs
      | cons f rest => obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs; exact stepF_nni h1 hi
  exact this h (by simp [NniOK, init, DefR.fresh])

end ParRun

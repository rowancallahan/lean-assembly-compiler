/- Nano/V2Self/Proof/Parser/ParRunShape: the SHAPE of Layer-2 task stacks (parser lead), pure.
Def-level frames (`isD`: defs, binders, group, plainBody, afterColon, stateTy, armsStart, armBind, zeroDone, defEnd, defClose) only ever
sit at the BOTTOM of the stack, one at a time.  Consequences: `.defs` is always alone, and once `acc` is set the stack is empty (the
machine stops on status 2 with no pending task, as Layer 2 does). -/
import Nano.V2Self.Proof.Parser.ParRunStar
namespace ParRun

def isD : Frame → Bool
  | .defs | .binders | .group _ | .plainBody | .afterColon | .stateTy | .armsStart | .armBind .. | .zeroDone | .defEnd | .defClose => true
  | _ => false

/-- a stack: empty, or D-free frames above exactly one def-level frame -/
def StackOK (fs : List Frame) : Bool :=
  match fs.reverse with
  | [] => true
  | g :: pre => isD g && pre.all (fun f => !isD f)

/-- what a frame may push: a def-level frame replaces itself by a (possibly empty) stack of the same shape, any other frame pushes
D-free frames only -/
def PushOK (d : Bool) (k : List Frame) : Bool := if d then StackOK k else k.all (fun f => !isD f)

theorem mkNode_acc {st st' : St} {t a b : Nat} {s : Option ParSpec.Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : st'.acc = st.acc := by
  unfold mkNode at h; split at h <;> cases h; rfl

theorem locOf_acc {st st' : St} {bd : Bd} (h : locOf st bd = some st') : st'.acc = st.acc := by
  unfold locOf at h; split at h <;> cases h; rfl

/-- every handler pushes a well-shaped list, and only `.defs` on the empty token list sets `acc` (pushing nothing) -/
theorem stepF_shape {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    PushOK (isD f) k = true ∧ (st'.acc = true → st.acc = true ∨ (f = .defs ∧ k = [])) := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨by decide, fun e => Or.inl e⟩)
    | (cases h; exact ⟨by simp [PushOK, StackOK, isD], fun e => Or.inl e⟩)
    | (cases h; exact ⟨by simp [PushOK, StackOK, isD], fun e => Or.inr ⟨rfl, rfl⟩⟩)
    | (cases h; refine ⟨by simp [PushOK, StackOK, isD], fun e => Or.inl ?_⟩; simpa [leaf] using e)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | exact ⟨by simp [PushOK, StackOK, isD], fun e => Or.inl (by rw [← mkNode_acc h2]; exact e)⟩
       | exact ⟨by simp [PushOK, StackOK, isD], fun e => Or.inl (by rw [← locOf_acc h2]; exact e)⟩
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          exact ⟨by simp [PushOK, StackOK, isD], fun e => Or.inl (by rw [← mkNode_acc h1, ← mkNode_acc h2']; exact e)⟩))

theorem stackOK_cons {f : Frame} {rest : List Frame} (h : StackOK (f :: rest) = true) :
    (rest = [] ∧ isD f = true) ∨ (rest ≠ [] ∧ isD f = false ∧ StackOK rest = true) := by
  unfold StackOK at h ⊢
  rw [List.reverse_cons] at h
  match hr : rest.reverse, h with
  | [], h =>
    left; exact ⟨List.reverse_eq_nil_iff.mp hr, by simpa using h⟩
  | g :: pre, h =>
    right
    have hne : rest ≠ [] := fun e => by subst e; simp at hr
    simp only [List.cons_append, Bool.and_eq_true, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine ⟨hne, h.2.2, ?_⟩
    simp [h.1, h.2.1]

theorem stackOK_append {k rest : List Frame} (hk : k.all (fun f => !isD f) = true) (hr : StackOK rest = true) (hne : rest ≠ []) :
    StackOK (k ++ rest) = true := by
  unfold StackOK at hr ⊢
  rw [List.reverse_append]
  match he : rest.reverse, hr with
  | [], _ => exact absurd (List.reverse_eq_nil_iff.mp he) hne
  | g :: pre, hr =>
    simp only [List.cons_append, Bool.and_eq_true, List.all_append, List.all_reverse] at hr ⊢
    exact ⟨hr.1, hr.2, hk⟩

/-- the stack invariant: well-shaped, and empty once accepted -/
def StkInv (c : List Frame × St) : Prop := StackOK c.1 = true ∧ (c.2.acc = true → c.1 = [])

theorem stepS_stkinv {c d : List Frame × St} (hs : stepS c = some d) (hi : StkInv c) : StkInv d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    obtain ⟨hp, ha⟩ := stepF_shape h1
    obtain ⟨hok, hacc⟩ := hi
    rcases stackOK_cons hok with ⟨rfl, hD⟩ | ⟨hne, hD, hr⟩
    · simp only [PushOK, hD, if_true] at hp
      refine ⟨by simpa using hp, fun e => ?_⟩
      rcases ha e with e2 | ⟨rfl, rfl⟩
      · exact absurd (hacc e2) (by simp)
      · rfl
    · simp only [PushOK, hD, Bool.false_eq_true, if_false] at hp
      refine ⟨stackOK_append hp hr hne, fun e => ?_⟩
      rcases ha e with e2 | ⟨rfl, rfl⟩
      · exact absurd (hacc e2) (by simp)
      · simp [isD] at hD

theorem Star.stkinv {c d : List Frame × St} (h : Star c d) (hi : StkInv c) : StkInv d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_stkinv hs hi)

theorem stkinv_init (toks : List ParSpec.Tok) : StkInv ([.defs], init toks) := ⟨rfl, fun e => by simp [init] at e⟩


/-! ## `.defs` is only ever the whole stack -/
/-- only `defClose` pushes `.defs`, and then alone -/
theorem stepF_defs_mem {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hm : Frame.defs ∈ k) :
    k = [.defs] ∧ f = .defClose := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp at hm; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3; simp at hm)

/-- `.defs` occurs in a stack only as the whole stack -/
def DInv (c : List Frame × St) : Prop := Frame.defs ∈ c.1 → c.1 = [.defs]

theorem stepS_dinv {c d : List Frame × St} (hs : stepS c = some d) (hk : StkInv c) (hi : DInv c) : DInv d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨rfl, rfl⟩ := stepF_defs_mem h1 hm
      rcases stackOK_cons hk.1 with ⟨rfl, _⟩ | ⟨_, hD, _⟩
      · rfl
      · simp [isD] at hD
    · have := hi (List.mem_cons_of_mem _ hm)
      simp at this
      rw [this.2] at hm; simp at hm

theorem Star.dinv {c d : List Frame × St} (h : Star c d) (hk : StkInv c) (hi : DInv c) : DInv d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_stkinv hs hk) (stepS_dinv hs hk hi)

theorem dinv_init (toks : List ParSpec.Tok) : DInv ([.defs], init toks) := fun _ => rfl

/-- below a popped frame other than `.defs`, no `.defs` (the glue's `inDefF fs = true`) -/
theorem defs_not_below {f : Frame} {fs : List Frame} {st : St} (hi : DInv (f :: fs, st)) (hf : f ≠ .defs) : ∀ g ∈ fs, g ≠ .defs := by
  intro g hg e; subst e
  have := hi (List.mem_cons_of_mem _ hg)
  simp at this; exact hf this.1

theorem dinv_reach {toks : List ParSpec.Tok} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (fs, st)) : DInv (fs, st) :=
  h.dinv (stkinv_init toks) (dinv_init toks)

end ParRun

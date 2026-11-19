/- Nano/V2Self/Proof/ParRunNames: def names are non-empty (parser lead), pure.  If every identifier token of the input has a
non-empty spelling (part of the token well-formedness hypothesis; Lex2 never produces an empty identifier), then every finished def
row has a non-empty name — needed because Par1's acceptance check reads the main name through fixed cell offsets. -/
import Nano.V2Self.Proof.ParRunShape
namespace ParRun
open ParSpec

def IdsOK (toks : List Tok) : Prop := ∀ x, Tok.id x ∈ toks → x ≠ []

/-- names: tokens, finished rows, and the current row unless only `.defs` frames are left (before the first def) -/
def NInv (c : List Frame × St) : Prop :=
  IdsOK c.2.toks ∧ (∀ d ∈ c.2.defs, d.name ≠ []) ∧ (c.2.cur.name ≠ [] ∨ ∀ f ∈ c.1, f = .defs)

theorem idsOK_sfx {p r : List Tok} (h : IdsOK (p ++ r)) : IdsOK r := fun x hx => h x (List.mem_append_right _ hx)

theorem mkNode_names {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : st'.toks = st.toks ∧ st'.defs = st.defs ∧ st'.cur = st.cur := by
  unfold mkNode at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩

theorem locOf_names {st st' : St} {bd : Bd} (h : locOf st bd = some st') : st'.toks = st.toks ∧ st'.defs = st.defs ∧ st'.cur = st.cur := by
  unfold locOf at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩

/-- per handler: identifier tokens stay non-empty (the tokens shrink to a suffix), the rows only grow by the current row
(`defClose`), the current row's name changes only at `.defs` (to a token spelling) -/
theorem stepF_names {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    (IdsOK st.toks → IdsOK st'.toks) ∧
    (st'.defs = st.defs ∨ (f = .defClose ∧ st'.defs = st.defs ++ [st.cur])) ∧
    (IdsOK st.toks → (st'.cur.name = st.cur.name ∧ f ≠ .defs) ∨ (f = .defs ∧ (st'.cur.name ≠ [] ∨ (k = [] ∧ st'.cur = st.cur)))) := by
  cases f
  case defs =>
    simp only [stepF] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; exact ⟨id, Or.inl rfl, fun _ => Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩)
      | (cases h; refine ⟨fun hI x hx => hI x ?_, Or.inl rfl, fun hI => Or.inr ⟨rfl, Or.inl (hI _ ?_)⟩⟩ <;> simp_all [DefR.fresh]; done)
  all_goals simp only [stepF] at h
  all_goals (repeat' split at h)
  all_goals
    first
    | (cases h; done)
    | (cases h; exact ⟨id, Or.inl rfl, fun _ => Or.inl ⟨rfl, nofun⟩⟩)
    | (cases h; refine ⟨fun hI x hx => hI x ?_, Or.inl rfl, fun _ => Or.inl ⟨rfl, nofun⟩⟩; simp_all [leaf]; done)
    | (cases h; exact ⟨id, Or.inr ⟨rfl, rfl⟩, fun _ => Or.inl ⟨rfl, nofun⟩⟩)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (unfold mkNode at h2; split at h2 <;> cases h2
          refine ⟨fun hI x hx => hI x ?_, Or.inl rfl, fun _ => Or.inl ⟨rfl, nofun⟩⟩; simp_all; done)
       | (unfold locOf at h2; split at h2 <;> cases h2
          refine ⟨fun hI x hx => hI x ?_, Or.inl rfl, fun _ => Or.inl ⟨rfl, nofun⟩⟩; simp_all; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          first | (unfold mkNode at h1; split at h1 <;> cases h1) | cases h1
          all_goals (unfold mkNode at h2'; split at h2' <;> cases h2')
          all_goals (refine ⟨fun hI x hx => hI x ?_, Or.inl rfl, fun _ => Or.inl ⟨rfl, nofun⟩⟩; simp_all)))

theorem stepS_ninv {c d : List Frame × St} (hs : stepS c = some d) (hi : NInv c) : NInv d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    obtain ⟨n1, n2, n3⟩ := stepF_names h1
    obtain ⟨hI, hD, hC⟩ := hi
    simp only at hI hD hC
    refine ⟨n1 hI, ?_, ?_⟩
    · rcases n2 with e | ⟨rfl, e⟩
      · rw [e]; exact hD
      · rw [e]
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hD d hd
        · rw [List.mem_singleton.mp hd]
          rcases hC with hC | hC
          · exact hC
          · exact absurd (hC .defClose (by simp)) (by intro e; cases e)
    · rcases n3 hI with ⟨e, hf⟩ | ⟨rfl, hk | ⟨rfl, e⟩⟩
      · rcases hC with hC | hC
        · exact Or.inl (by simp only; rw [e]; exact hC)
        · exact absurd (hC f (by simp)) hf
      · exact Or.inl hk
      · rcases hC with hC | hC
        · exact Or.inl (by simp only; rw [e]; exact hC)
        · exact Or.inr (fun g hg => hC g (by simp at hg ⊢; exact Or.inr hg))

theorem Star.ninv {c d : List Frame × St} (h : Star c d) (hi : NInv c) : NInv d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_ninv hs hi)

theorem ninv_init {toks : List Tok} (h : IdsOK toks) : NInv ([.defs], init toks) :=
  ⟨h, fun d hd => by simp [init] at hd, Or.inr (fun f hf => by simpa using hf)⟩

end ParRun

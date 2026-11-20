/- Nano/V2Self/Proof/Parser/ParRunCInv: three Layer-2 stack invariants the Layer-3 handlers of box C need besides `WF` (pure, box C).
* `modeOK`: every `expr _ md` / `prim md` frame has md ≤ 2 (task 3's v104 reads the mode cell);
* `FlatOK`: flatten frames (`flat`, `flatL`) only form a top segment of the stack (node builders need no flatten frame below them);
* `StashOK`: either the stash is set, or scanning from the top a `stash` frame comes before any `letPairSemi` (task 53 reads h[29]). -/
import Nano.V2Self.Proof.Parser.ParRunShape
set_option backward.isDefEq.respectTransparency false
namespace ParRun

def Frame.modeOK : Frame → Bool
  | .expr _ md => decide (md ≤ 2)
  | .prim md => decide (md ≤ 2)
  | _ => true

def Frame.isFl : Frame → Bool
  | .flat _ => true
  | .flatL _ => true
  | _ => false

def Frame.isLPS : Frame → Bool
  | .letPairSemi .. => true
  | _ => false

def FlatOK (fs : List Frame) : Bool := (fs.dropWhile Frame.isFl).all (fun f => !f.isFl)

/-- from the top: a `stash` frame before any `letPairSemi` -/
def StashB : List Frame → Bool
  | [] => true
  | .stash _ :: _ => true
  | .letPairSemi .. :: _ => false
  | _ :: r => StashB r

def CInv (c : List Frame × St) : Prop :=
  c.1.all Frame.modeOK = true ∧ FlatOK c.1 = true ∧ (c.2.stash.isSome = true ∨ StashB c.1 = true)

theorem bm_le (tl : Bool) : bm tl ≤ 2 := by cases tl <;> decide

theorem stepF_mode {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hf : f.modeOK = true) :
    k.all Frame.modeOK = true := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp [Frame.modeOK, bm_le] at hf ⊢; try omega)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3; simp [Frame.modeOK])

theorem stepF_flat {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    (f.isFl = true → k.all Frame.isFl = true) ∧ (f.isFl = false → FlatOK k = true) := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp [Frame.isFl, FlatOK])
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3; simp [Frame.isFl, FlatOK])

theorem mkNode_stash {st st' : St} {t a b : Nat} {s : Option ParSpec.Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : st'.stash = st.stash := by
  unfold mkNode at h; split at h <;> cases h; rfl

theorem locOf_stash {st st' : St} {bd : Bd} (h : locOf st bd = some st') : st'.stash = st.stash := by
  unfold locOf at h; split at h <;> cases h; rfl

theorem stepF_stash {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    (st.stash.isSome = true → st'.stash.isSome = true) ∧ (f.isLPS = false → (∃ x, f = .stash x) ∨
      (st'.stash = st.stash ∧ (k.all (fun g => !g.isLPS) = true ∨ StashB k = true ∧ ∃ x, Frame.stash x ∈ k))) := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp [Frame.isLPS, StashB, leaf])
    | (cases h; simp [Frame.isLPS, StashB, leaf]; done)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (have e := mkNode_stash h2; simp [Frame.isLPS, e])
       | (have e := locOf_stash h2; simp [Frame.isLPS, e])
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          have e1 := mkNode_stash h1; have e2 := mkNode_stash h2'; simp [Frame.isLPS, e1, e2]))

theorem stashB_app1 {fs : List Frame} (hb : StashB fs = true) :
    ∀ k : List Frame, k.all (fun g => !g.isLPS) = true → StashB (k ++ fs) = true
  | [], _ => hb
  | g :: r, hk => by
    simp only [List.all_cons, Bool.and_eq_true] at hk
    have hr := stashB_app1 hb r hk.2
    have h1 := hk.1
    cases g <;> simp_all [StashB, Frame.isLPS]

theorem stashB_app2 {fs : List Frame} : ∀ k : List Frame, StashB k = true → (∃ x, Frame.stash x ∈ k) → StashB (k ++ fs) = true
  | [], _, ⟨_, hx⟩ => by simp at hx
  | g :: r, hb, ⟨x, hx⟩ => by
    cases g <;> simp only [StashB, List.cons_append] at hb ⊢ <;> try rfl
    all_goals
      first
      | exact absurd hb (by decide)
      | (have hx' : Frame.stash x ∈ r := by simpa using hx
         exact stashB_app2 r hb ⟨x, hx'⟩)

theorem flatOK_app {k fs : List Frame} (hk : FlatOK k = true) (hf : fs.all (fun f => !f.isFl) = true) : FlatOK (k ++ fs) = true := by
  induction k with
  | nil =>
    simp only [FlatOK, List.nil_append] at hk ⊢
    cases fs with
    | nil => rfl
    | cons g r =>
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hf
      simpa [List.dropWhile, hf.1] using hf.2
  | cons g r ih =>
    simp only [FlatOK, List.cons_append, List.dropWhile] at hk ⊢
    cases hg : g.isFl
    · simp only [hg] at hk ⊢
      simp only [List.all_cons, List.all_append, Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, hk.2, hf⟩
    · simp only [hg] at hk ⊢; exact ih hk

theorem flatOK_all {k fs : List Frame} (hk : k.all Frame.isFl = true) (hf : FlatOK fs = true) : FlatOK (k ++ fs) = true := by
  induction k with
  | nil => simpa using hf
  | cons g r ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hk
    simp only [FlatOK, List.cons_append, List.dropWhile, hk.1] at ih ⊢
    exact ih hk.2

theorem stepS_cinv {c d : List Frame × St} (hs : stepS c = some d) (hi : CInv c) : CInv d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    obtain ⟨hm, hfl, hst⟩ := hi
    simp only [List.all_cons, Bool.and_eq_true] at hm
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.all_append, Bool.and_eq_true]; exact ⟨stepF_mode h1 hm.1, hm.2⟩
    · obtain ⟨a1, a2⟩ := stepF_flat h1
      cases hf : f.isFl
      · simp only [FlatOK, List.dropWhile, hf, List.all_cons, Bool.and_eq_true] at hfl
        exact flatOK_app (a2 hf) hfl.2
      · simp only [FlatOK, List.dropWhile, hf] at hfl
        exact flatOK_all (a1 hf) hfl
    · obtain ⟨b1, b2⟩ := stepF_stash h1
      rcases hst with e | e
      · exact Or.inl (b1 e)
      · cases hl : f.isLPS
        · by_cases hfs : ∃ x, f = .stash x
          · obtain ⟨x, rfl⟩ := hfs
            simp only [stepF, Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨_, rfl⟩ := h1; exact Or.inl rfl
          rcases b2 hl with hx | ⟨es, hk⟩
          · exact absurd hx hfs
          · right
            have hb : StashB rest = true := by
              cases f <;> simp_all [StashB, Frame.isLPS]
            rcases hk with hk | ⟨hk1, hk2⟩
            · exact stashB_app1 hb k hk
            · exact stashB_app2 k hk1 hk2
        · cases f <;> simp_all [StashB, Frame.isLPS]

theorem Star.cinv {c d : List Frame × St} (h : Star c d) (hi : CInv c) : CInv d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_cinv hs hi)

theorem cinv_init (toks : List ParSpec.Tok) : CInv ([.defs], init toks) := ⟨rfl, rfl, Or.inr rfl⟩

/-! ## the side conditions of box C's handlers -/
theorem cinv_mode {md : Nat} {fs : List Frame} {st : St} (hi : CInv (.prim md :: fs, st)) : md ≤ 2 := by
  have := hi.1; simp [Frame.modeOK] at this; exact this.1

theorem cinv_noflat {f : Frame} {fs : List Frame} {st : St} (hi : CInv (f :: fs, st)) (hf : f.isFl = false) :
    fs.all (fun g => !g.isFl) = true := by
  have := hi.2.1; simp only [FlatOK, List.dropWhile, hf, List.all_cons, Bool.and_eq_true] at this; exact this.2

theorem cinv_stash {y : List Nat} {tl : Bool} {fs : List Frame} {st : St} (hi : CInv (.letPairSemi y tl :: fs, st)) :
    st.stash.isSome = true := by
  rcases hi.2.2 with e | e
  · exact e
  · simp [StashB] at e

end ParRun

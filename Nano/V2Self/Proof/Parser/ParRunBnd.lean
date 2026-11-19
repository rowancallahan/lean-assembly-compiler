/- Nano/V2Self/Proof/Parser/ParRunBnd: Layer-2 bounds along runs (parser lead), for `ParInvRun.Obl`.
`reach_prim32`: every prim callee on the task stack is < 2^32 (in fact < 10). -/
import Nano.V2Self.Proof.Parser.ParRunCInv
import Nano.V2Self.Proof.Parser.ParRunArena
import Nano.V2Self.Proof.Parser.ParRunWFPres
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

/-! ## flatten frames hold arena nodes -/
def Frame.inA (A : List RN) : Frame → Prop
  | .flat n => ∀ m ∈ nodes n, m ∈ A
  | .flatL ns => ∀ n ∈ ns, ∀ m ∈ nodes n, m ∈ A
  | _ => True

theorem kid_sub {n k m : RN} (hk : k ∈ n.kids) (hm : m ∈ nodes k) : m ∈ nodes n := by
  cases n; exact kid_nodes_sub hk hm

theorem stepF_inA_fl {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hf : f.isFl = true)
    (hi : f.inA st.arena) : st'.arena = st.arena ∧ ∀ x ∈ k, x.inA st.arena := by
  cases f <;> simp [Frame.isFl] at hf
  case flat n =>
    simp only [stepF] at h
    have key : ∀ ks : List RN, (∀ x ∈ ks, x ∈ n.kids) → (Frame.flatL ks).inA st.arena :=
      fun ks hks x hx m hm => hi m (kid_sub (hks x hx) hm)
    split at h
    · cases h; exact ⟨rfl, by simpa using key _ (fun _ h => h)⟩
    · cases h; refine ⟨rfl, ?_⟩
      simp only [List.mem_singleton, forall_eq]
      split
      · exact key _ (fun x hx => List.mem_of_mem_tail hx)
      · exact key _ (fun _ h => h)
  case flatL ns =>
    simp only [stepF] at h
    split at h
    · cases h; exact ⟨rfl, by simp⟩
    · rename_i n r
      have h1 : (Frame.flat n).inA st.arena := fun m hm => hi n (by simp) m hm
      have h2 : (Frame.flatL r).inA st.arena := fun x hx m hm => hi x (by simp [hx]) m hm
      split at h <;> cases h
      · exact ⟨rfl, by simpa using h2⟩
      · exact ⟨rfl, by simpa using ⟨h1, h2⟩⟩

theorem stepF_inA_nf {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hf : f.isFl = false)
    (hA : ArenaInv st) : ∀ x ∈ k, x.inA st'.arena := by
  cases f <;> simp [Frame.isFl] at hf <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp [Frame.inA]; done)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3; simp)
    | (cases h; simp only [Frame.inA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true]
       intro m hm; rw [hA, ‹st.vals = [_]›]; simpa using hm)

theorem inA_nf {A : List RN} {x : Frame} (h : x.isFl = false) : x.inA A := by
  cases x <;> simp [Frame.isFl] at h <;> trivial

def FlatIn (c : List Frame × St) : Prop := ∀ f ∈ c.1, f.inA c.2.arena

theorem stepS_flatIn {c d : List Frame × St} (hs : stepS c = some d) (hc : CInv c) (hA : ArenaInv c.2) (hi : FlatIn c) :
    FlatIn d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    intro x hx
    cases hf : f.isFl
    · rcases List.mem_append.mp hx with hx | hx
      · exact stepF_inA_nf h1 hf hA x hx
      · have := cinv_noflat hc hf
        simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        exact inA_nf (this x hx)
    · obtain ⟨e, hk⟩ := stepF_inA_fl h1 hf (hi f (by simp))
      show x.inA st'.arena
      rw [e]
      rcases List.mem_append.mp hx with hx | hx
      · exact hk x hx
      · exact hi x (by simp [hx])

theorem reach_flatIn {toks : List Tok} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (fs, st)) : FlatIn (fs, st) := by
  have : ∀ {c d : List Frame × St}, Star c d → Star ([.defs], init toks) c → FlatIn c → FlatIn d := by
    intro c d h
    induction h with
    | refl => exact fun _ hi => hi
    | @step c c1 d hs _ ih =>
      intro hr hi
      exact ih (hr.trans (.step hs (.refl _))) (stepS_flatIn hs (hr.cinv (cinv_init _)) (hr.inv (init_inv toks)).1 hi)
  exact this h (.refl _) (fun f hf => by simp at hf; subst hf; trivial)

/-! ## prim nodes 1..3 have a first child -/
def P9 (st : St) : Prop := ∀ m ∈ st.arena, m.tag = 9 → m.a < 4 → m.kids ≠ []

theorem p9_mkNode {st st' : St} {t a b : Nat} {sh : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b sh p n = some st') (ht : t = 9 → a < 4 → 1 ≤ n) (hi : P9 st) : P9 st' := by
  obtain ⟨hn, rfl⟩ := mkNode_eq.mp h
  intro m hm h9 ha
  rcases List.mem_append.mp hm with hm | hm
  · exact hi m hm h9 ha
  · rw [List.mem_singleton.mp hm] at h9 ha ⊢
    have := ht h9 ha
    intro e
    have e2 : ((st.vals.take n).reverse).length = 0 := by rw [show (st.vals.take n).reverse = [] from e]; rfl
    simp only [List.length_reverse, List.length_take] at e2; omega

theorem p9_app {st : St} {nd : RN} (h : nd.tag = 9 → nd.a < 4 → nd.kids ≠ []) (hi : P9 st) :
    ∀ m ∈ st.arena ++ [nd], m.tag = 9 → m.a < 4 → m.kids ≠ [] := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi m hm
  · rw [List.mem_singleton.mp hm]; exact h

theorem stepF_p9 {f : Frame} {r k : List Frame} {st st' : St} (hw : WF (f :: r) st) (h : stepF f st = some (k, st'))
    (hi : P9 st) : P9 st' := by
  obtain ⟨g1, hg⟩ := wf_pre hw
  cases f
  case mkCall c n =>
    cases c with
    | pr p =>
      simp only [effF, St.g] at hg
      split at hg
      · rename_i hc
        simp only [stepF] at h
        obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
        exact p9_mkNode h2 (fun _ ha => hc.2.2 (by simpa [Callee.need1] using ha)) hi
      · cases hg
    | df j =>
      simp only [stepF] at h
      split at h
      · obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
        exact p9_mkNode h2 (fun e => absurd e (by decide)) hi
      · cases h
  all_goals simp only [stepF] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hi)
    | (cases h; intro m hm; simp at hm; done)
    | (cases h; exact p9_app (by simp [RN.tag, RN.a]) hi)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | exact p9_mkNode h2 (fun e => absurd e (by decide)) hi
       | (unfold locOf at h2; split at h2 <;> cases h2; exact p9_app (by simp [RN.tag]) hi)
       | (obtain ⟨s1, a1, a2⟩ := Option.bind_eq_some_iff.mp h2
          exact p9_mkNode a2 (fun e => absurd e (by decide)) (p9_mkNode a1 (fun e => absurd e (by decide)) hi))
       | (obtain ⟨s1, a1, a2⟩ := Option.bind_eq_some_iff.mp h2
          cases a1; exact p9_mkNode a2 (fun e => absurd e (by decide)) hi))

theorem reach_p9 {toks : List Tok} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (fs, st)) : P9 st := by
  have : ∀ {c d : List Frame × St}, Star c d → Star ([.defs], init toks) c → P9 c.2 → P9 d.2 := by
    intro c d h
    induction h with
    | refl => exact fun _ hi => hi
    | @step c c1 d hs _ ih =>
      intro hr hi
      obtain ⟨fs, st⟩ := c
      cases fs with
      | nil => simp [stepS] at hs
      | cons f rest =>
        obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
        exact ih (hr.trans (.step hs (.refl _))) (stepF_p9 (wf_star hr) h1 hi)
  exact this h (.refl _) (fun m hm => by simp [init] at hm)

/-- **the flattener's side conditions**: a `flat` frame's node is an arena node (so it has fewer children than the arena has
nodes), a call's input-argument count is at most its argument count, and a prim 1..3 has a first child -/
theorem reach_flat {toks : List Tok} {n : RN} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (.flat n :: fs, st)) :
    n.kids.length < st.arena.length ∧ (n.tag = 9 → n.a < 4 → n.kids ≠ []) ∧
      (n.tag = 8 → (n.kids.filter RN.isInp).length ≤ n.b) := by
  have hin : (Frame.flat n).inA st.arena := reach_flatIn h (.flat n) (List.mem_cons_self ..)
  have hm : n ∈ st.arena := hin n (self_mem_nodes n)
  obtain ⟨hA, hC⟩ := h.inv (init_inv toks)
  refine ⟨kids_lt_arena hA hm, reach_p9 h n hm, fun h8 => ?_⟩
  have := hC n hm
  simp [cntOK, h8] at this
  rw [this]; exact List.length_filter_le _ _

end ParRun

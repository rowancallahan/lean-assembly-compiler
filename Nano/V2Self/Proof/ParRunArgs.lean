/- Nano/V2Self/Proof/ParRunArgs: Layer 2 → ParSpec for ARGUMENT LISTS (box G).
`AtomSpec cx st st'`: an atom segment pushed one node `v` and is `ParSpec.pAtom` (non-tail) at all large fuels, with node `v.toNd`.
`atomSeg_spec`: every run of `[argAtom]` is an `AtomSpec`, given the same for parenthesised atoms (`ParenH`: the open-recursion
hypothesis that the expression induction supplies).  `args_spec`: `Atoms k` = `ParSpec.pArgs` for every parameter list the
argument types match. -/
import Nano.V2Self.Proof.ParRunAtom
namespace ParRun
open ParSpec

/-- a segment that pushed exactly one node and left the tables alone -/
structure Pushed (st st' : St) (v : RN) : Prop where
  vals : st'.vals = v :: st.vals
  binds : st'.binds = st.binds
  defs : st'.defs = st.defs
  cur : st'.cur = st.cur

theorem CxRel.transport {st st' : St} {cx : Cx} (h : CxRel st cx) (hb : st'.binds = st.binds) (hd : st'.defs = st.defs) :
    CxRel st' cx := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by rw [hb]; exact a, by rw [hb]; exact b, by rw [hb]; exact c, by rw [hd]; exact d, by rw [hd]; exact e⟩

/-- an argument value: typed, not a provisional self-call, and a `len'` node has the Nat code -/
def ValOK (v : RN) (ty : Ty) : Prop := TyRel v ty ∧ v.pend = false ∧ (v.tag = 9 → v.a = 1 → v.sh = some .nt)

/-- an atom segment as the spec sees it -/
def AtomSpec (cx : Cx) (st st' : St) : Prop :=
  ∃ v ty, Pushed st st' v ∧ ValOK v ty ∧ ∃ F, ∀ f, F ≤ f → pAtom f cx false st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)

/-- the hypothesis on parenthesised atoms (runs shorter than `N`) -/
def ParenH (N : Nat) (cx : Cx) : Prop :=
  ∀ n, n < N → ∀ (st fin : St) (r : List Tok), st.toks = .k 6 :: r →
    StarN n ([.expr 0 0, .parenClose], { st with toks := r }) ([], fin) → CxRel st cx → AtomSpec cx st fin

theorem StarN.nil_inv {n : Nat} {st : St} {c : List Frame × St} (h : StarN n ([], st) c) : n = 0 ∧ c = ([], st) := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => simp [stepS] at hs

theorem atomSeg_spec {N : Nat} {cx : Cx} (hP : ParenH N cx) {n : Nat} (hn : n ≤ N) {st st' : St}
    (h : StarN n ([.argAtom], st) ([], st')) (hc : CxRel st cx) : AtomSpec cx st st' := by
  rcases atom_run h with ⟨r, n', ht, rfl, hrun⟩ | ⟨st1, n', _, hl, hrun⟩
  · exact hP n' (by omega) st st' r ht hrun hc
  · obtain ⟨_, he⟩ := hrun.nil_inv
    cases he
    obtain ⟨v, ty, r, rfl, hty, hpe, hp⟩ := atomLeaf_spec hc hl false st.nx
    have h9 : v.tag = 9 → v.a = 1 → v.sh = some .nt := by
      intro h9 h1
      cases hl with
      | num _ => cases h9
      | nil _ => cases h1
      | bnew _ => cases h1
      | loc _ _ hl' =>
        unfold locOf at hl'; split at hl'
        · simp at hl'
        · simp only [Option.some.injEq] at hl'
          have := congrArg St.vals hl'; simp at this; rw [← this] at h9; cases h9
      | cst _ _ _ _ _ hm =>
        obtain ⟨_, he⟩ := mkNode_inv hm
        have := congrArg St.vals he; simp at this; rw [this] at h9; cases h9
    exact ⟨v, ty, ⟨rfl, rfl, rfl, rfl⟩, ⟨hty, hpe, h9⟩, 1, fun f hf => by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact hp g⟩

theorem pArgs_nil (f : Nat) (cx : Cx) (ts : List Tok) (nx : Nat) : pArgs (f + 1) cx [] ts nx = some ([], ts, nx) := by
  rw [pArgs]

theorem pArgs_cons (f : Nat) (cx : Cx) (p : Ps) (ps : List Ps) (ts : List Tok) (nx : Nat) :
    pArgs (f + 1) cx (p :: ps) ts nx = (pAtom f cx false ts nx).bind fun (a, ta, r1, nx1) =>
      if tyMatch p ta then (pArgs f cx ps r1 nx1).map fun (as, r2, nx2) => ((a, ta) :: as, r2, nx2) else none := by
  rw [pArgs]

/-- parameter kinds matched by the argument types, position by position -/
inductive ArgsMatch : List Ps → List (RN × Ty) → Prop
  | nil : ArgsMatch [] []
  | cons {p ps v vs} : tyMatch p v.2 = true → ArgsMatch ps vs → ArgsMatch (p :: ps) (v :: vs)

/-- `k` atom segments are `pArgs` for every parameter list they match -/
theorem args_spec {N : Nat} {cx : Cx} (hP : ParenH N cx) : ∀ {k m : Nat} {st st' : St}, Atoms k st st' m → m ≤ N → CxRel st cx →
    ∃ vs : List (RN × Ty), vs.length = k ∧ st'.vals = (vs.map (·.1)).reverse ++ st.vals ∧ st'.binds = st.binds ∧ st'.defs = st.defs ∧
      st'.cur = st.cur ∧ (∀ p ∈ vs, ValOK p.1 p.2) ∧
      ∃ F, ∀ f, F ≤ f → ∀ ps : List Ps, ArgsMatch ps vs →
        pArgs f cx ps st.toks st.nx = some (vs.map (fun p => (p.1.toNd, p.2)), st'.toks, st'.nx) := by
  intro k m st st' h
  induction h with
  | nil st =>
    intro _ _
    refine ⟨[], rfl, rfl, rfl, rfl, rfl, fun p hp => absurd hp (by simp), 1, fun f hf ps hps => ?_⟩
    cases hps
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact pArgs_nil g cx _ _
  | @cons k st st1 st2 n1 n2 ha _ ih =>
    intro hm hc
    obtain ⟨v, ty, hpu, hty, F1, hp1⟩ := atomSeg_spec hP (by omega) ha hc
    obtain ⟨vs, hlen, hvals, hb, hd, hcu, htys, F2, hp2⟩ := ih (by omega) (hc.transport hpu.binds hpu.defs)
    refine ⟨(v, ty) :: vs, by simp [hlen], ?_, hb.trans hpu.binds, hd.trans hpu.defs, hcu.trans hpu.cur, ?_, max F1 F2 + 1, ?_⟩
    · rw [hvals, hpu.vals]; simp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hty
      · exact htys p hp
    · intro f hf ps hps
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      cases hps with
      | cons hm1 hrest =>
        rw [pArgs_cons, hp1 g (by omega)]
        simp only [Option.bind_some, hm1, if_true]
        rw [hp2 g (by omega) _ hrest]
        rfl

end ParRun

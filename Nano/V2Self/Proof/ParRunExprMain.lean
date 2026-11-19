/- Nano/V2Self/Proof/ParRunExprMain: the expression refinement, assembled from per-family lemmas (box B). -/
import Nano.V2Self.Proof.ParRunExprInv
namespace ParRun
open ParSpec

/-- a primary (`prim md`, not at `if` / `let` unless md = 2) ↔ `pApp f cx (md == 1)` -/
def PrimSpec (n : Nat) : Prop := ∀ md ks st fin cx, StarN n (.prim md :: ks, st) ([], fin) → CxRel st cx →
  (md = 2 ∨ ((∀ r, st.toks ≠ .k 32 :: r) ∧ (∀ r, st.toks ≠ .k 2 :: r))) →
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ (v.toNd.tailCont = true → v.pend = true) ∧
      ∀ f, 4 * st.toks.length + 2 ≤ f → pApp f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem prim_two_ifs {ks st fin n} (h : StarN n (.prim 2 :: ks, st) ([], fin)) :
    (∀ r, st.toks ≠ .k 32 :: r) ∧ (∀ r, st.toks ≠ .k 2 :: r) := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
    obtain ⟨k, st1, hs, _⟩ := h.head
    constructor <;> intro r hr <;> simp [stepF, hr] at hs

theorem bin_of {n : Nat} (hP : ∀ n' < n, PrimSpec n') (hL : ∀ n' < n, LoopSpec n') : BinSpec n := by
  classical
  intro m ks st fin cx h hc
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  simp only [List.cons_append, List.nil_append] at h1
  obtain ⟨a, st1, n1, hn1, hp1, hlt1, h2, hspa⟩ := hP n (by omega) 2 _ _ fin cx h1 hc (Or.inl rfl)
  let ta : Ty := if hva : VT (rows st) a then Classical.choose (hspa hva) else .bot
  have hta : VT (rows st1) a → TyRel a ta ∧ PT a := fun hva => by
    have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
    rw [hr] at hva
    simp only [ta, dif_pos hva]; exact ⟨(Classical.choose_spec (hspa hva)).1, (Classical.choose_spec (hspa hva)).2.1⟩
  obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hspec⟩ :=
    hL n1 (by omega) m ks st1 fin cx a st.vals ta h2 hp1.vals (CxRel.transport hc hp1.binds hp1.defs) hta
  have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
  refine ⟨v, st', n', by omega, ⟨hp.vals, by rw [hp.binds, hp1.binds], by rw [hp.defs, hp1.defs], by rw [hp.cur, hp1.cur],
    by rw [hp.arm, hp1.arm], by rw [hp.all, hp1.all], by have := hp.toks; omega, by have := hp.nx; have := hp1.nx; omega⟩,
    by have := hp.toks; omega, hrun, hstop, fun hvt => ?_⟩
  rw [hr] at hspec
  obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
  have hva : VT (rows st) a := fun u hu => hvt u (hsub u hu)
  refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hpa := (Classical.choose_spec (hspa hva)).2.2 g (by omega)
  simp only [show (2 == 1) = false from rfl] at hpa
  rw [pBin.eq_def]; simp only
  rw [hpa]; simp only [Option.bind_some]
  have := hf g (by omega)
  simp only [ta, dif_pos hva] at this
  exact this


/-- a full expression (`expr 0 md`, md < 2) ↔ `pExpr f cx (md == 1)` -/
def ExprSpec (n : Nat) : Prop := ∀ md ks st fin cx, md < 2 → StarN n (.expr 0 md :: ks, st) ([], fin) → CxRel st cx →
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

theorem pExpr_other {f cx tl ts nx} (h32 : ∀ r, ts ≠ .k 32 :: r) (h2 : ∀ r, ts ≠ .k 2 :: r) :
    pExpr (f + 1) cx tl ts nx = pBin f cx tl 0 ts nx := by
  rw [pExpr.eq_def]; simp only
  split <;> first | exact (h2 _ rfl).elim | exact (h32 _ rfl).elim | rfl | simp_all

/-- `expr 0 md` at a token that is neither `if` nor `let`: the primary, then the operator loop at precedence 0 -/
theorem expr_other {n : Nat} (hP : ∀ n' < n, PrimSpec n') (hL : ∀ n' < n, LoopSpec n') {md ks st fin cx} (hmd : md < 2)
    (h : StarN n (.expr 0 md :: ks, st) ([], fin)) (hc : CxRel st cx)
    (h32 : ∀ r, st.toks ≠ .k 32 :: r) (h2 : ∀ r, st.toks ≠ .k 2 :: r) :
    ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ Stop 0 st'.toks ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ PT v ∧
      ∀ f, 4 * st.toks.length + 4 ≤ f → pExpr f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx)) := by
  classical
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨k, st1, hs, h1⟩ := h.head
  rw [expr_eq] at hs; simp at hs; obtain ⟨rfl, rfl⟩ := hs
  simp only [List.cons_append, List.nil_append] at h1
  obtain ⟨a, st1, n1, hn1, hp1, hlt1, h2', hspa⟩ := hP n (by omega) md _ _ fin cx h1 hc (Or.inr ⟨h32, h2⟩)
  let ta : Ty := if hva : VT (rows st) a then Classical.choose (hspa hva) else .bot
  have hr : rows st1 = rows st := by simp [rows, hp1.defs, hp1.cur]
  have hta : VT (rows st1) a → TyRel a ta ∧ PT a := fun hva => by
    rw [hr] at hva
    simp only [ta, dif_pos hva]; exact ⟨(Classical.choose_spec (hspa hva)).1, (Classical.choose_spec (hspa hva)).2.1⟩
  -- the first step of the loop decides whether an operator follows
  obtain ⟨v, st', n', hn', hp, hsub, hrun, hstop, hspec⟩ :=
    hL n1 (by omega) 0 ks st1 fin cx a st.vals ta h2' hp1.vals (CxRel.transport hc hp1.binds hp1.defs) hta
  refine ⟨v, st', n', by omega, ⟨hp.vals, by rw [hp.binds, hp1.binds], by rw [hp.defs, hp1.defs], by rw [hp.cur, hp1.cur],
    by rw [hp.arm, hp1.arm], by rw [hp.all, hp1.all], by have := hp.toks; omega, by have := hp.nx; have := hp1.nx; omega⟩,
    by have := hp.toks; omega, hrun, hstop, fun hvt => ?_⟩
  rw [hr] at hspec
  obtain ⟨ty, hty, hpt, hf⟩ := hspec hvt
  have hva : VT (rows st) a := fun u hu => hvt u (hsub u hu)
  refine ⟨ty, hty, hpt, fun f hf' => ?_⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hpa := (Classical.choose_spec (hspa hva)).2.2 g (by omega)
  have hloop := hf g (by omega)
  simp only [ta, dif_pos hva] at hloop
  rw [pExpr_other h32 h2, pBin.eq_def]; simp only
  rw [hpa]; simp only [Option.bind_some]
  -- with the tail flag on and an operator next, ParSpec re-parses the primary with the flag off
  split
  · rename_i t rest hmd1 hrt
    split
    · rename_i hop
      -- the loop's first step tested that `a` is not pending
      have hpend : a.pend = false := by
        match n1, h2' with
        | 0, h2' => exact absurd h2'.zero_nil.1 (by simp)
        | n1 + 1, h2' =>
          obtain ⟨k, st2, hs2, _⟩ := h2'.head
          rcases binLoop_inv hs2 with ⟨_, _, hlt⟩ | ⟨t', r', op, p, top, rest', ht', _, _, hv', hpend, _⟩
          · obtain ⟨opp, hop'⟩ := Option.isSome_iff_exists.mp hop
            exact absurd (hlt t rest opp.1 opp.2 hrt hop') (by omega)
          · rw [hp1.vals] at hv'; injection hv' with hv'; rw [hv']; exact hpend
      have htc : a.toNd.tailCont = false := by
        cases hc' : a.toNd.tailCont
        · rfl
        · have := (Classical.choose_spec (hspa hva)).2.1 hc'; rw [hpend] at this; cases this
      have hmd : md = 1 := by simpa using hmd1
      subst hmd
      have hpf := (tl_down g).2.2.1 _ _ _ _ hpa htc
      rw [hpf]; simp only [Option.bind_some]; exact hloop
    · exact hloop
  · exact hloop

end ParRun

/- `Tree`: the body of a first-order tail-recursive function as a decision tree over `BExp`, its
one-iteration semantics `Tree.step`, the iteration `Tree.Runs`, a compiler to `BStmt` and the
once-and-for-all theorem `Tree.prog_ok` (source level, no machine).

A conditional is two loops that run at most once (`BStmt` has no `if`):
`a := c; b := (a == 0); while a { T; a := 0 }; while b { E; b := 0 }`.
The function is `fl := 1; while fl { body }`: a `ret e` leaf does `res := e; fl := 0`, a `call` leaf
assigns the new arguments in parallel (through temporaries). -/
import Riscv.Direct.Arr2Src

namespace Proven.Frontx
open Proven

inductive Tree where
  | ret (e : BExp)
  /-- tail call: parallel assignment `v := e` for the pairs, all `e` evaluated in the old state -/
  | call (as : List (Nat × BExp))
  | ite (c : BExp) (t e : Tree)
  | let_ (v : Nat) (e : BExp) (k : Tree)
  | load (v b : Nat) (i : BExp) (k : Tree)
  /-- guarded load: `v := if c ≠ 0 then block b [i] else d` -/
  | cload (v b : Nat) (i c d : BExp) (k : Tree)
  | store (b : Nat) (i e : BExp) (k : Tree)

inductive Out where
  | ret (r : BitVec 64) (σ : BState)
  | call (σ : BState)

def parSet (ρ : BEnv) : BEnv → List (Nat × BExp) → BEnv
  | env, [] => env
  | env, (v, e) :: as => parSet ρ (env.set v (e.denote ρ)) as

/-- byte `j` of block `b` -/
def rd (H : Heap) (b j : Nat) : Option (BitVec 8) := (H[b]?).bind (·[j]?)
/-- the heap with byte `j` of block `b` set to `x` -/
def wr (H : Heap) (b j : Nat) (x : BitVec 8) : Option Heap :=
  (H[b]?).bind fun B => if j < B.length then some (H.set b (B.set j x)) else none

/-- one iteration; `none` = an out-of-bounds access -/
def Tree.step : Tree → BState → Option Out
  | .ret e, σ => some (.ret (e.denote σ.env) σ)
  | .call as, σ => some (.call ⟨parSet σ.env σ.env as, σ.heap⟩)
  | .ite c t e, σ => if c.denote σ.env = 0 then e.step σ else t.step σ
  | .let_ v e k, σ => k.step ⟨σ.env.set v (e.denote σ.env), σ.heap⟩
  | .load v b i k, σ => (rd σ.heap b (i.denote σ.env).toNat).bind fun x =>
      k.step ⟨σ.env.set v (x.setWidth 64), σ.heap⟩
  | .cload v b i c d k, σ =>
    if c.denote σ.env = 0 then k.step ⟨σ.env.set v (d.denote σ.env), σ.heap⟩
    else (rd σ.heap b (i.denote σ.env).toNat).bind fun x => k.step ⟨σ.env.set v (x.setWidth 64), σ.heap⟩
  | .store b i e k, σ => (wr σ.heap b (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8)).bind fun H =>
      k.step ⟨σ.env, H⟩

/-- iterate until a `ret` leaf: result `r`, final state `σ'` -/
inductive Tree.Runs (t : Tree) : BState → BitVec 64 → BState → Prop
  | ret {σ r σ'} : t.step σ = some (.ret r σ') → Runs t σ r σ'
  | call {σ σ₁ r σ'} : t.step σ = some (.call σ₁) → Runs t σ₁ r σ' → Runs t σ r σ'

/-! ## Compiler -/

/-- `M` user variables `0..M-1`; then `res`, `fl`, `K` call temporaries, two condition variables per
nesting depth -/
structure Lay where
  M : Nat
  K : Nat

def Lay.res (L : Lay) : Nat := L.M
def Lay.fl (L : Lay) : Nat := L.M + 1
def Lay.tmp (L : Lay) (j : Nat) : Nat := L.M + 2 + j
def Lay.cv (L : Lay) (d : Nat) : Nat := L.M + 2 + L.K + 2 * d

def skip (L : Lay) : BStmt := .assign L.fl (.var L.fl)

def tmps (L : Lay) : List (Nat × BExp) → Nat → BStmt
  | [], _ => skip L
  | (_, e) :: as, j => .seq (.assign (L.tmp j) e) (tmps L as (j + 1))

def copies (L : Lay) : List (Nat × BExp) → Nat → BStmt
  | [], _ => skip L
  | (v, _) :: as, j => .seq (.assign v (.var (L.tmp j))) (copies L as (j + 1))

def comp (L : Lay) : Tree → Nat → BStmt
  | .ret e, _ => .seq (.assign L.res e) (.assign L.fl (.const 0))
  | .call as, _ => .seq (tmps L as 0) (copies L as 0)
  | .ite c t e, d =>
    .seq (.assign (L.cv d) c) (.seq (.assign (L.cv d + 1) (.bin .eq (.var (L.cv d)) (.const 0)))
      (.seq (.loop (.var (L.cv d)) (.seq (comp L t (d + 1)) (.assign (L.cv d) (.const 0))))
        (.loop (.var (L.cv d + 1)) (.seq (comp L e (d + 1)) (.assign (L.cv d + 1) (.const 0))))))
  | .let_ v e k, d => .seq (.assign v e) (comp L k d)
  | .load v b i k, d => .seq (.load v b i) (comp L k d)
  | .cload v b i c e k, d =>
    .seq (.assign (L.cv d) c) (.seq (.assign (L.cv d + 1) (.bin .eq (.var (L.cv d)) (.const 0)))
      (.seq (.loop (.var (L.cv d)) (.seq (.load v b i) (.assign (L.cv d) (.const 0))))
        (.seq (.loop (.var (L.cv d + 1)) (.seq (.assign v e) (.assign (L.cv d + 1) (.const 0)))) (comp L k d))))
  | .store b i e k, d => .seq (.store b i e) (comp L k d)

/-- the whole function: result in variable `out` -/
def prog (L : Lay) (t : Tree) (out : Nat) : BStmt :=
  .seq (.assign L.fl (.const 1)) (.seq (.loop (.var L.fl) (comp L t 0)) (.assign out (.var L.res)))

def Tree.wf (L : Lay) : Tree → Prop
  | .ret e => e.vlt L.M
  | .call as => as.length ≤ L.K ∧ ∀ p ∈ as, p.1 < L.M ∧ p.2.vlt L.M
  | .ite c t e => c.vlt L.M ∧ t.wf L ∧ e.wf L
  | .let_ v e k => v < L.M ∧ e.vlt L.M ∧ k.wf L
  | .load v _ i k => v < L.M ∧ i.vlt L.M ∧ k.wf L
  | .cload v _ i c d k => v < L.M ∧ i.vlt L.M ∧ c.vlt L.M ∧ d.vlt L.M ∧ k.wf L
  | .store _ i e k => i.vlt L.M ∧ e.vlt L.M ∧ k.wf L

/-! ## Correctness -/

/-- `τ` (machine-side state, with control variables) agrees with `σ` on the user variables and the heap -/
def Agree (M : Nat) (σ τ : BState) : Prop := (∀ v, v < M → τ.env v = σ.env v) ∧ τ.heap = σ.heap

theorem denote_agree {M : Nat} {ρ ρ' : BEnv} (h : ∀ v, v < M → ρ' v = ρ v) :
    ∀ e : BExp, e.vlt M → e.denote ρ' = e.denote ρ
  | .var i, hv => h i hv
  | .const _, _ => rfl
  | .bin _ a b, hv => by simp only [BExp.denote, denote_agree h a hv.1, denote_agree h b hv.2]
  | .ite c a b, hv => by
    simp only [BExp.denote, denote_agree h c hv.1, denote_agree h a hv.2.1, denote_agree h b hv.2.2]

theorem set_eq (ρ : BEnv) (v : Nat) (x : BitVec 64) : ρ.set v x v = x := by simp [BEnv.set]
theorem set_ne (ρ : BEnv) {v w : Nat} (x : BitVec 64) (h : w ≠ v) : ρ.set v x w = ρ w := by simp [BEnv.set, h]

theorem skip_ok (L : Lay) (τ : BState) : BExec (skip L) τ τ := by
  have h : τ = ⟨τ.env.set L.fl ((BExp.var L.fl).denote τ.env), τ.heap⟩ := by
    cases τ with | mk env heap =>
    simp only [BState.mk.injEq, and_true]; funext i
    by_cases hi : i = L.fl <;> simp [BEnv.set, BExp.denote, hi]
  exact BExec.assign' h

theorem tmps_ok (L : Lay) : ∀ (as : List (Nat × BExp)) (j : Nat) (τ : BState),
    (∀ p ∈ as, p.2.vlt L.M) →
    ∃ τ', BExec (tmps L as j) τ τ' ∧ τ'.heap = τ.heap ∧
      (∀ x, (x < L.tmp j ∨ L.tmp j + as.length ≤ x) → τ'.env x = τ.env x) ∧
      ∀ i (h : i < as.length), τ'.env (L.tmp j + i) = as[i].2.denote τ.env
  | [], j, τ, _ => ⟨τ, skip_ok L τ, rfl, fun _ _ => rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | (v, e) :: as, j, τ, hv => by
    obtain ⟨τ', hx, hh, hk, hi⟩ := tmps_ok L as (j + 1) ⟨τ.env.set (L.tmp j) (e.denote τ.env), τ.heap⟩
      (fun p hp => hv p (List.mem_cons_of_mem _ hp))
    have hlow : ∀ x, x < L.M → (τ.env.set (L.tmp j) (e.denote τ.env)) x = τ.env x := fun x hx =>
      set_ne _ _ (by simp only [Lay.tmp]; omega)
    refine ⟨τ', .seq .assign hx, hh, fun x hx => ?_, fun i h => ?_⟩
    · rw [hk x (by simp only [Lay.tmp, List.length_cons] at hx ⊢; omega)]
      exact set_ne _ _ (by simp only [Lay.tmp, List.length_cons] at hx ⊢; omega)
    · cases i with
      | zero =>
        rw [Nat.add_zero, hk _ (Or.inl (by simp only [Lay.tmp]; omega))]; exact set_eq _ _ _
      | succ i =>
        have := hi i (by simpa using h)
        rw [show L.tmp j + (i + 1) = L.tmp (j + 1) + i by simp only [Lay.tmp]; omega, this]
        exact denote_agree hlow _ (hv _ (List.mem_cons_of_mem _ (List.getElem_mem _)))

theorem copies_ok (L : Lay) (ρ : BEnv) : ∀ (as : List (Nat × BExp)) (j : Nat) (τ : BState),
    (∀ p ∈ as, p.1 < L.M) → (∀ i (h : i < as.length), τ.env (L.tmp j + i) = as[i].2.denote ρ) →
    ∃ τ', BExec (copies L as j) τ τ' ∧ τ'.heap = τ.heap ∧
      (∀ x, L.M ≤ x → τ'.env x = τ.env x) ∧ ∀ x, x < L.M → τ'.env x = parSet ρ τ.env as x
  | [], j, τ, _, _ => ⟨τ, skip_ok L τ, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | (v, e) :: as, j, τ, hv, ht => by
    have hvM : v < L.M := (hv _ List.mem_cons_self)
    have h0 := ht 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨τ', hx, hh, hk, hi⟩ := copies_ok L ρ as (j + 1) ⟨τ.env.set v (e.denote ρ), τ.heap⟩
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) (fun i h => by
        have := ht (i + 1) (by simpa using h)
        simp only [List.getElem_cons_succ] at this
        rw [← this, show L.tmp j + (i + 1) = L.tmp (j + 1) + i by simp only [Lay.tmp]; omega]
        exact set_ne _ _ (by simp only [Lay.tmp]; omega))
    refine ⟨τ', .seq (BExec.assign' ?_) hx, hh, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [BExp.denote, h0]
    · rw [hk x hx]; exact set_ne _ _ (by omega)
    · rw [hi x hx]; rfl

theorem parSet_congr (ρ : BEnv) (x : Nat) : ∀ (as : List (Nat × BExp)) (e₁ e₂ : BEnv), e₁ x = e₂ x →
    parSet ρ e₁ as x = parSet ρ e₂ as x
  | [], _, _, h => h
  | (v, e) :: as, e₁, e₂, h => parSet_congr ρ x as _ _ (by
      by_cases hx : x = v <;> simp [BEnv.set, hx, h])

theorem parSet_rho (M : Nat) {ρ ρ' : BEnv} (h : ∀ v, v < M → ρ' v = ρ v) : ∀ (as : List (Nat × BExp)) (env : BEnv),
    (∀ p ∈ as, p.2.vlt M) → parSet ρ' env as = parSet ρ env as
  | [], _, _ => rfl
  | (v, e) :: as, env, hv => by
    simp only [parSet, denote_agree h e (hv _ List.mem_cons_self)]
    exact parSet_rho M h as _ (fun p hp => hv p (List.mem_cons_of_mem _ hp))

/-- what one compiled iteration does, given one step of the tree -/
def Post (L : Lay) (τ τ' : BState) : Out → Prop
  | .ret r σ' => Agree L.M σ' τ' ∧ τ'.env L.res = r ∧ τ'.env L.fl = 0
  | .call σ' => Agree L.M σ' τ' ∧ τ'.env L.fl = τ.env L.fl

theorem Post.mono {L : Lay} {τ τ₀ τ' τ'' : BState} {o : Out} (h : Post L τ τ' o)
    (hfl : τ.env L.fl = τ₀.env L.fl) (hh : τ''.heap = τ'.heap) (he : ∀ x, x < L.M + 2 → τ''.env x = τ'.env x) :
    Post L τ₀ τ'' o := by
  have hA : ∀ σ', Agree L.M σ' τ' → Agree L.M σ' τ'' := fun σ' h =>
    ⟨fun v hv => (he v (by omega)).trans (h.1 v hv), hh.trans h.2⟩
  cases o with
  | ret r σ' => exact ⟨hA _ h.1, (he _ (by simp [Lay.res])).trans h.2.1, (he _ (by simp [Lay.fl])).trans h.2.2⟩
  | call σ' => exact ⟨hA _ h.1, ((he _ (by simp [Lay.fl])).trans h.2).trans hfl⟩

theorem comp_ok (L : Lay) : ∀ (t : Tree) (d : Nat) (σ τ : BState) (o : Out), t.wf L → Agree L.M σ τ →
    t.step σ = some o →
    ∃ τ', BExec (comp L t d) τ τ' ∧ (∀ x, L.M + 2 + L.K ≤ x → x < L.cv d → τ'.env x = τ.env x) ∧ Post L τ τ' o
  | .ret e, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step, Option.some.injEq] at hs; subst hs
    refine ⟨_, .seq .assign .assign, fun x h1 _ => ?_, ⟨fun v hv => ?_, hA.2⟩, ?_, ?_⟩
    · dsimp only
      rw [set_ne _ _ (by simp only [Lay.fl]; omega), set_ne _ _ (by simp only [Lay.res]; omega)]
    · dsimp only
      rw [set_ne _ _ (by simp only [Lay.fl]; omega), set_ne _ _ (by simp only [Lay.res]; omega)]; exact hA.1 v hv
    · dsimp only
      rw [set_ne _ _ (by simp [Lay.fl, Lay.res]), set_eq]; exact denote_agree hA.1 e hw
    · exact set_eq _ _ _
  | .call as, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step, Option.some.injEq] at hs; subst hs
    obtain ⟨τ₁, hx1, hh1, hk1, hi1⟩ := tmps_ok L as 0 τ (fun p hp => (hw.2 p hp).2)
    obtain ⟨τ₂, hx2, hh2, hk2, hi2⟩ := copies_ok L τ.env as 0 τ₁ (fun p hp => (hw.2 p hp).1) hi1
    refine ⟨τ₂, .seq hx1 hx2, fun x h1 _ => ?_, ⟨fun v hv => ?_, by rw [hh2, hh1, hA.2]⟩, ?_⟩
    · rw [hk2 x (by omega)]; exact hk1 x (Or.inr (by have := hw.1; simp only [Lay.tmp]; omega))
    · rw [hi2 v hv, parSet_rho L.M hA.1 as _ (fun p hp => (hw.2 p hp).2)]
      exact parSet_congr _ _ as _ _ ((hk1 v (Or.inl (by simp only [Lay.tmp]; omega))).trans (hA.1 v hv))
    · rw [hk2 _ (by simp [Lay.fl]), hk1 _ (Or.inl (by simp [Lay.fl, Lay.tmp]))]
  | .ite c t e, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step] at hs
    have hc := denote_agree hA.1 c hw.1
    have hcv : L.M + 2 + L.K ≤ L.cv d := by simp [Lay.cv]
    have hcv1 : L.cv d + 1 < L.cv (d + 1) := by simp only [Lay.cv]; omega
    -- state after the two condition assignments
    let τ₁ : BState := ⟨τ.env.set (L.cv d) (c.denote τ.env), τ.heap⟩
    let τ₂ : BState := ⟨τ₁.env.set (L.cv d + 1) ((BExp.bin .eq (.var (L.cv d)) (.const 0)).denote τ₁.env), τ₁.heap⟩
    have hA2 : Agree L.M σ τ₂ := ⟨fun v hv => by
      show BEnv.set (BEnv.set _ _ _) _ _ v = _
      rw [set_ne _ _ (by omega), set_ne _ _ (by omega)]; exact hA.1 v hv, hA.2⟩
    have ha : τ₂.env (L.cv d) = c.denote σ.env := by
      show BEnv.set (BEnv.set _ _ _) _ _ _ = _
      rw [set_ne _ _ (by omega), set_eq, hc]
    have hb : τ₂.env (L.cv d + 1) = if c.denote σ.env = 0 then 1 else 0 := by
      show BEnv.set (BEnv.set _ _ _) _ _ _ = _
      have h1 : τ₁.env (L.cv d) = c.denote σ.env := by
        show BEnv.set _ _ _ _ = _
        rw [set_eq, hc]
      rw [set_eq]; simp only [BExp.denote, Op.eval, h1]
    have hlow : ∀ x, x < L.cv d → τ₂.env x = τ.env x := fun x hx => by
      show BEnv.set (BEnv.set _ _ _) _ _ x = _
      rw [set_ne _ _ (by omega), set_ne _ _ (by omega)]
    have h12 : BExec (.assign (L.cv d) c) τ τ₁ := .assign
    have h23 : BExec (.assign (L.cv d + 1) (.bin .eq (.var (L.cv d)) (.const 0))) τ₁ τ₂ := .assign
    by_cases h0 : c.denote σ.env = 0
    · rw [if_pos h0] at hs
      obtain ⟨τ₃, hx, hk, hp⟩ := comp_ok L e (d + 1) σ τ₂ o hw.2.2 hA2 hs
      have ha3 : τ₃.env (L.cv d) = 0 := by rw [hk _ hcv (by omega), ha, h0]
      refine ⟨⟨τ₃.env.set (L.cv d + 1) 0, τ₃.heap⟩, .seq h12 (.seq h23 (.seq (.loopF (by simp [BExp.denote, ha, h0]))
        (.loopT (by simp [BExp.denote, hb, h0]) (.seq hx .assign) (.loopF (by simp [BExp.denote, set_eq])))))
        , fun x h1 h2 => ?_, ?_⟩
      · show BEnv.set _ _ _ x = _
        rw [set_ne _ _ (by omega), hk x h1 (by omega), hlow x h2]
      · exact hp.mono (hlow _ (by simp only [Lay.fl]; omega)) rfl (fun x hx => set_ne _ _ (by omega))
    · rw [if_neg h0] at hs
      obtain ⟨τ₃, hx, hk, hp⟩ := comp_ok L t (d + 1) σ τ₂ o hw.2.1 hA2 hs
      have hb3 : τ₃.env (L.cv d + 1) = 0 := by rw [hk _ (by omega) hcv1, hb, if_neg h0]
      refine ⟨⟨τ₃.env.set (L.cv d) 0, τ₃.heap⟩, .seq h12 (.seq h23 (.seq
        (.loopT (by simp only [BExp.denote, ha]; exact h0) (.seq hx .assign) (.loopF (by simp [BExp.denote, set_eq])))
        (.loopF (by
          show BEnv.set _ _ _ _ = _
          rw [set_ne _ _ (by omega), hb3])))), fun x h1 h2 => ?_, ?_⟩
      · show BEnv.set _ _ _ x = _
        rw [set_ne _ _ (by omega), hk x h1 (by omega), hlow x h2]
      · exact hp.mono (hlow _ (by simp only [Lay.fl]; omega)) rfl (fun x hx => set_ne _ _ (by omega))
  | .let_ v e k, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step] at hs
    have hA1 : Agree L.M ⟨σ.env.set v (e.denote σ.env), σ.heap⟩ ⟨τ.env.set v (e.denote τ.env), τ.heap⟩ :=
      ⟨fun x hx => by
        show BEnv.set _ _ _ x = BEnv.set _ _ _ x
        rw [denote_agree hA.1 e hw.2.1]
        by_cases h : x = v <;> simp [BEnv.set, h, hA.1 x hx], hA.2⟩
    obtain ⟨τ', hx, hk, hp⟩ := comp_ok L k d _ _ o hw.2.2 hA1 hs
    refine ⟨τ', .seq .assign hx, fun x h1 h2 => ?_, ?_⟩
    · rw [hk x h1 h2]; exact set_ne _ _ (by have := hw.1; omega)
    · exact hp.mono (set_ne _ _ (by have := hw.1; simp only [Lay.fl]; omega)) rfl (fun _ _ => rfl)
  | .load v b i k, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step] at hs
    have hi := denote_agree hA.1 i hw.2.1
    cases hr : rd σ.heap b (i.denote σ.env).toNat with
    | none => rw [hr] at hs; cases hs
    | some x =>
      rw [hr] at hs; simp only [Option.bind_some] at hs
      cases hB : σ.heap[b]? with
      | none => simp [rd, hB] at hr
      | some B =>
        have hx : B[(i.denote σ.env).toNat]? = some x := by simpa [rd, hB] using hr
        have hA1 : Agree L.M ⟨σ.env.set v (x.setWidth 64), σ.heap⟩ ⟨τ.env.set v (x.setWidth 64), τ.heap⟩ :=
          ⟨fun y hy => by
            show BEnv.set _ _ _ y = BEnv.set _ _ _ y
            by_cases h : y = v <;> simp [BEnv.set, h, hA.1 y hy], hA.2⟩
        obtain ⟨τ', hx', hk, hp⟩ := comp_ok L k d _ _ o hw.2.2 hA1 hs
        refine ⟨τ', .seq (BExec.load' (B := B) (by rw [hA.2]; exact hB) (congrArg BitVec.toNat hi) hx) hx',
          fun y h1 h2 => ?_, ?_⟩
        · rw [hk y h1 h2]; exact set_ne _ _ (by have := hw.1; omega)
        · exact hp.mono (set_ne _ _ (by have := hw.1; simp only [Lay.fl]; omega)) rfl (fun _ _ => rfl)
  | .cload v b i c e k, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step] at hs
    obtain ⟨hv, hwi, hwc, hwe, hwk⟩ := hw
    have hc := denote_agree hA.1 c hwc
    have hcv : L.M + 2 + L.K ≤ L.cv d := by simp [Lay.cv]
    let τ₁ : BState := ⟨τ.env.set (L.cv d) (c.denote τ.env), τ.heap⟩
    let τ₂ : BState := ⟨τ₁.env.set (L.cv d + 1) ((BExp.bin .eq (.var (L.cv d)) (.const 0)).denote τ₁.env), τ₁.heap⟩
    have hlow : ∀ x, x < L.cv d → τ₂.env x = τ.env x := fun x hx => by
      show BEnv.set (BEnv.set _ _ _) _ _ x = _
      rw [set_ne _ _ (by omega), set_ne _ _ (by omega)]
    have hA2 : ∀ x, x < L.M → τ₂.env x = σ.env x := fun x hx => (hlow x (by omega)).trans (hA.1 x hx)
    have ha : τ₂.env (L.cv d) = c.denote σ.env := by
      show BEnv.set (BEnv.set _ _ _) _ _ _ = _
      rw [set_ne _ _ (by omega), set_eq, hc]
    have hb : τ₂.env (L.cv d + 1) = if c.denote σ.env = 0 then 1 else 0 := by
      show BEnv.set (BEnv.set _ _ _) _ _ _ = _
      have h1 : τ₁.env (L.cv d) = c.denote σ.env := by
        show BEnv.set _ _ _ _ = _
        rw [set_eq, hc]
      rw [set_eq]; simp only [BExp.denote, Op.eval, h1]
    have h12 : BExec (.assign (L.cv d) c) τ τ₁ := .assign
    have h23 : BExec (.assign (L.cv d + 1) (.bin .eq (.var (L.cv d)) (.const 0))) τ₁ τ₂ := .assign
    by_cases h0 : c.denote σ.env = 0
    · rw [if_pos h0] at hs
      -- else branch: `v := e`
      let τ₃ : BState := ⟨τ₂.env.set v (e.denote τ₂.env), τ₂.heap⟩
      let τ₄ : BState := ⟨τ₃.env.set (L.cv d + 1) 0, τ₃.heap⟩
      have hA4 : Agree L.M ⟨σ.env.set v (e.denote σ.env), σ.heap⟩ τ₄ := ⟨fun x hx => by
        show BEnv.set (BEnv.set _ _ _) _ _ x = BEnv.set _ _ _ x
        rw [set_ne _ _ (by omega), denote_agree hA2 e hwe]
        by_cases h : x = v <;> simp [BEnv.set, h, hA2 x hx], hA.2⟩
      obtain ⟨τ', hx, hk, hp⟩ := comp_ok L k d _ τ₄ o hwk hA4 hs
      have h4 : ∀ x, L.M ≤ x → x < L.cv d → τ₄.env x = τ.env x := fun x h1 h2 => by
        show BEnv.set (BEnv.set _ _ _) _ _ x = _
        rw [set_ne _ _ (by omega), set_ne _ _ (by omega), hlow x h2]
      refine ⟨τ', .seq h12 (.seq h23 (.seq (.loopF (by simp [BExp.denote, ha, h0]))
        (.seq (.loopT (by simp [BExp.denote, hb, h0]) (.seq .assign .assign) (.loopF (by simp [BExp.denote, set_eq])))
          hx))), fun x h1 h2 => ?_, ?_⟩
      · rw [hk x h1 h2, h4 x (by omega) h2]
      · exact hp.mono (h4 _ (by simp only [Lay.fl]; omega) (by simp only [Lay.fl]; omega)) rfl (fun _ _ => rfl)
    · rw [if_neg h0] at hs
      have hi := denote_agree hA2 i hwi
      cases hr : rd σ.heap b (i.denote σ.env).toNat with
      | none => rw [hr] at hs; cases hs
      | some x =>
        rw [hr] at hs; simp only [Option.bind_some] at hs
        cases hB : σ.heap[b]? with
        | none => simp [rd, hB] at hr
        | some B =>
          have hx : B[(i.denote σ.env).toNat]? = some x := by simpa [rd, hB] using hr
          let τ₃ : BState := ⟨τ₂.env.set v (x.setWidth 64), τ₂.heap⟩
          let τ₄ : BState := ⟨τ₃.env.set (L.cv d) 0, τ₃.heap⟩
          have hA4 : Agree L.M ⟨σ.env.set v (x.setWidth 64), σ.heap⟩ τ₄ := ⟨fun y hy => by
            show BEnv.set (BEnv.set _ _ _) _ _ y = BEnv.set _ _ _ y
            rw [set_ne _ _ (by omega)]
            by_cases h : y = v <;> simp [BEnv.set, h, hA2 y hy], hA.2⟩
          obtain ⟨τ', hx', hk, hp⟩ := comp_ok L k d _ τ₄ o hwk hA4 hs
          have h4 : ∀ y, L.M ≤ y → y < L.cv d → τ₄.env y = τ.env y := fun y h1 h2 => by
            show BEnv.set (BEnv.set _ _ _) _ _ y = _
            rw [set_ne _ _ (by omega), set_ne _ _ (by omega), hlow y h2]
          have hb4 : τ₄.env (L.cv d + 1) = 0 := by
            show BEnv.set (BEnv.set _ _ _) _ _ _ = _
            rw [set_ne _ _ (by omega), set_ne _ _ (by omega), hb, if_neg h0]
          have hl : BExec (.load v b i) τ₂ τ₃ :=
            BExec.load' (B := B) (by show τ.heap[b]? = _; rw [hA.2]; exact hB) (congrArg BitVec.toNat hi) hx
          refine ⟨τ', .seq h12 (.seq h23 (.seq
            (.loopT (by simp only [BExp.denote, ha]; exact h0) (.seq hl .assign) (.loopF (by simp [BExp.denote, set_eq])))
            (.seq (.loopF hb4) hx'))), fun y h1 h2 => ?_, ?_⟩
          · rw [hk y h1 h2, h4 y (by omega) h2]
          · exact hp.mono (h4 _ (by simp only [Lay.fl]; omega) (by simp only [Lay.fl]; omega)) rfl (fun _ _ => rfl)
  | .store b i e k, d, σ, τ, o, hw, hA, hs => by
    simp only [Tree.step] at hs
    have hi := denote_agree hA.1 i hw.1
    have he := denote_agree hA.1 e hw.2.1
    cases hr : wr σ.heap b (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8) with
    | none => rw [hr] at hs; cases hs
    | some H =>
      rw [hr] at hs; simp only [Option.bind_some] at hs
      cases hB : σ.heap[b]? with
      | none => simp [wr, hB] at hr
      | some B =>
        simp only [wr, hB, Option.bind_some] at hr
        by_cases hl : (i.denote σ.env).toNat < B.length
        · rw [if_pos hl, Option.some.injEq] at hr; subst hr
          have hA1 : Agree L.M ⟨σ.env, σ.heap.set b (B.set (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8))⟩
              ⟨τ.env, τ.heap.set b (B.set (i.denote σ.env).toNat ((e.denote τ.env).setWidth 8))⟩ :=
            ⟨hA.1, by rw [he, hA.2]⟩
          obtain ⟨τ', hx', hk, hp⟩ := comp_ok L k d _ _ o hw.2.2 hA1 hs
          exact ⟨τ', .seq (BExec.store' (B := B) (by rw [hA.2]; exact hB) (congrArg BitVec.toNat hi) hl) hx', hk,
            hp.mono rfl rfl (fun _ _ => rfl)⟩
        · rw [if_neg hl] at hr; cases hr

theorem loop_ok (L : Lay) {t : Tree} (hw : t.wf L) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ') :
    ∀ τ, Agree L.M σ τ → τ.env L.fl ≠ 0 →
    ∃ τ', BExec (.loop (.var L.fl) (comp L t 0)) τ τ' ∧ Agree L.M σ' τ' ∧ τ'.env L.res = r := by
  induction h with
  | ret hs =>
    intro τ hA hf
    obtain ⟨τ', hx, _, hA', hr, hf'⟩ := comp_ok L t 0 _ τ _ hw hA hs
    exact ⟨τ', .loopT hf hx (.loopF hf'), hA', hr⟩
  | call hs _ ih =>
    intro τ hA hf
    obtain ⟨τ₁, hx, _, hA', hf'⟩ := comp_ok L t 0 _ τ _ hw hA hs
    obtain ⟨τ', hl, hq⟩ := ih τ₁ hA' (by rw [hf']; exact hf)
    exact ⟨τ', .loopT hf hx hl, hq⟩

/-- **Once and for all**: if the tree iterates from `σ` to the result `r`, the compiled program run from any
state with the same user variables and heap ends with `r` in `out`, the same heap, and the other user
variables as the tree left them. -/
theorem prog_ok (L : Lay) {t : Tree} (hw : t.wf L) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ')
    (out : Nat) (τ : BState) (hA : Agree L.M σ τ) :
    ∃ τ', BExec (prog L t out) τ τ' ∧ τ'.env out = r ∧ τ'.heap = σ'.heap ∧
      ∀ v, v < L.M → v ≠ out → τ'.env v = σ'.env v := by
  obtain ⟨τ₁, hl, hA', hr⟩ := loop_ok L hw h ⟨τ.env.set L.fl 1, τ.heap⟩
    ⟨fun v hv => (set_ne _ _ (by simp only [Lay.fl]; omega)).trans (hA.1 v hv), hA.2⟩
    (by show BEnv.set _ _ _ _ ≠ 0; rw [set_eq]; decide)
  exact ⟨_, .seq .assign (.seq hl .assign), by simp [BEnv.set, BExp.denote, hr], hA'.2, fun v hv hne => by
    show BEnv.set _ _ _ v = _
    rw [set_ne _ _ hne]; exact hA'.1 v hv⟩

/-! ## Trees without `store` keep the heap -/

def Tree.ro : Tree → Bool
  | .ret _ | .call _ => true
  | .ite _ t e => t.ro && e.ro
  | .let_ _ _ k | .load _ _ _ k | .cload _ _ _ _ _ k => k.ro
  | .store .. => false

theorem Tree.step_ro : ∀ (t : Tree) (σ : BState) (o : Out), t.ro = true → t.step σ = some o →
    (match o with | .ret _ σ' => σ'.heap | .call σ' => σ'.heap) = σ.heap
  | .ret e, σ, o, _, hs => by simp only [Tree.step, Option.some.injEq] at hs; subst hs; rfl
  | .call as, σ, o, _, hs => by simp only [Tree.step, Option.some.injEq] at hs; subst hs; rfl
  | .ite c t e, σ, o, hr, hs => by
    simp only [Tree.ro, Bool.and_eq_true] at hr
    simp only [Tree.step] at hs
    by_cases h : c.denote σ.env = 0
    · rw [if_pos h] at hs; exact step_ro e σ o hr.2 hs
    · rw [if_neg h] at hs; exact step_ro t σ o hr.1 hs
  | .let_ v e k, σ, o, hr, hs => step_ro k ⟨σ.env.set v (e.denote σ.env), σ.heap⟩ o hr hs
  | .load v b i k, σ, o, hr, hs => by
    simp only [Tree.step] at hs
    cases h : rd σ.heap b (i.denote σ.env).toNat with
    | none => rw [h] at hs; cases hs
    | some x => rw [h] at hs; exact step_ro k ⟨σ.env.set v (x.setWidth 64), σ.heap⟩ o hr hs
  | .cload v b i c d k, σ, o, hr, hs => by
    simp only [Tree.step] at hs
    by_cases h0 : c.denote σ.env = 0
    · rw [if_pos h0] at hs; exact step_ro k ⟨σ.env.set v (d.denote σ.env), σ.heap⟩ o hr hs
    · rw [if_neg h0] at hs
      cases h : rd σ.heap b (i.denote σ.env).toNat with
      | none => rw [h] at hs; cases hs
      | some x => rw [h] at hs; exact step_ro k ⟨σ.env.set v (x.setWidth 64), σ.heap⟩ o hr hs
  | .store .., _, _, hr, _ => by cases hr

theorem Tree.Runs.heap_ro {t : Tree} (hr : t.ro = true) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ') :
    σ'.heap = σ.heap := by
  induction h with
  | ret hs => exact Tree.step_ro t _ _ hr hs
  | call hs _ ih => exact ih.trans (Tree.step_ro t _ _ hr hs)

/-- `prog_ok` for a read-only tree started in the very state `σ` -/
theorem prog_ok_ro (L : Lay) {t : Tree} (hw : t.wf L) (hr : t.ro = true) {σ : BState} {r : BitVec 64}
    (h : ∃ σ', t.Runs σ r σ') (out : Nat) :
    ∃ τ', BExec (prog L t out) σ τ' ∧ τ'.env out = r ∧ τ'.heap = σ.heap := by
  obtain ⟨σ', h⟩ := h
  obtain ⟨τ', h1, h2, h3, _⟩ := prog_ok L hw h out σ ⟨fun _ _ => rfl, rfl⟩
  exact ⟨τ', h1, h2, h3.trans (h.heap_ro hr)⟩

/-! ## Building `Runs` (used by the generated per-function proofs) -/

theorem step_call {t : Tree} {σ : BState} {r : BitVec 64} (σ₁ : BState) (hs : t.step σ = some (.call σ₁))
    (h : ∃ σ', t.Runs σ₁ r σ') : ∃ σ', t.Runs σ r σ' :=
  h.elim fun σ' h1 => ⟨σ', .call hs h1⟩

theorem Tree.Runs.congr {t : Tree} {σ σ' : BState} {r r' : BitVec 64} (h : t.Runs σ r σ') (e : r = r') :
    t.Runs σ r' σ' := e ▸ h

theorem step_ret {t : Tree} {σ : BState} {r : BitVec 64} (σ' : BState) (hs : t.step σ = some (.ret r σ')) :
    ∃ σ', t.Runs σ r σ' := ⟨σ', .ret hs⟩

/-- the variables `rs` hold the given values -/
def AllEnv (env : BEnv) (rs : List (Nat × BitVec 64)) : Prop := ∀ p ∈ rs, env p.1 = p.2
theorem allEnv_nil (env : BEnv) : AllEnv env [] := fun _ h => nomatch h
theorem allEnv_cons {env : BEnv} {v : Nat} {x : BitVec 64} {rs : List (Nat × BitVec 64)} (h : env v = x)
    (hr : AllEnv env rs) : AllEnv env ((v, x) :: rs) := fun p hp => by
  rcases List.mem_cons.1 hp with e | e
  · subst e; exact h
  · exact hr p e

theorem step_callQ {t : Tree} {σ : BState} {r : BitVec 64} {Q : BState → Prop} (σ₁ : BState)
    (hs : t.step σ = some (.call σ₁)) (h : ∃ σ', t.Runs σ₁ r σ' ∧ Q σ') : ∃ σ', t.Runs σ r σ' ∧ Q σ' :=
  h.elim fun σ' h1 => ⟨σ', .call hs h1.1, h1.2⟩

theorem step_retQ {t : Tree} {σ : BState} {r : BitVec 64} {Q : BState → Prop} (σ' : BState)
    (hs : t.step σ = some (.ret r σ')) (hq : Q σ') : ∃ σ', t.Runs σ r σ' ∧ Q σ' := ⟨σ', .ret hs, hq⟩

/-- `prog_ok` with extra result variables (read-only tree, started in the very state `σ`) -/
theorem prog_okQ (L : Lay) {t : Tree} (hw : t.wf L) (hr : t.ro = true) {σ : BState} {r : BitVec 64}
    {rs : List (Nat × BitVec 64)} (h : ∃ σ', t.Runs σ r σ' ∧ ∀ p ∈ rs, σ'.env p.1 = p.2) (out : Nat)
    (hlt : ∀ p ∈ rs, p.1 < L.M ∧ p.1 ≠ out) :
    ∃ τ', BExec (prog L t out) σ τ' ∧ τ'.env out = r ∧ τ'.heap = σ.heap ∧ ∀ p ∈ rs, τ'.env p.1 = p.2 := by
  obtain ⟨σ', h, hq⟩ := h
  obtain ⟨τ', h1, h2, h3, h4⟩ := prog_ok L hw h out σ ⟨fun _ _ => rfl, rfl⟩
  exact ⟨τ', h1, h2, h3.trans (h.heap_ro hr), fun p hp => (h4 p.1 (hlt p hp).1 (hlt p hp).2).trans (hq p hp)⟩

/-! ## One iteration against a Lean-side outcome (used by the certifying translator)

The translator turns the body of `f` into a term `out : LOut A` of the same `if` structure whose leaves are
`ret (rep e)` and `call args'`, and proves `Sim R tree σ out` node by node with the lemmas below. -/

inductive LOut (A : Type) where
  | ret (r : BitVec 64)
  | call (a : A)
  /-- a result with several components: `r`, and the values of the extra result variables -/
  | retm (r : BitVec 64) (rs : List (Nat × BitVec 64))

/-- the step of `k` from `σ` is the Lean outcome: the same result, or a call whose new state holds the new
arguments (`R`) -/
def Sim {A : Type} (R : A → BState → Prop) (k : Tree) (σ : BState) : LOut A → Prop
  | .ret r => ∃ σ', k.step σ = some (.ret r σ')
  | .call a => ∃ σ₁, k.step σ = some (.call σ₁) ∧ R a σ₁
  | .retm r rs => ∃ σ', k.step σ = some (.ret r σ') ∧ ∀ p ∈ rs, σ'.env p.1 = p.2

section
variable {A : Type} (R : A → BState → Prop)

theorem sim_ret (e : BExp) (env : BEnv) (heap : Heap) (r : BitVec 64) (h : e.denote env = r) :
    Sim R (.ret e) ⟨env, heap⟩ (.ret r) := ⟨⟨env, heap⟩, by simp only [Tree.step, h]⟩

theorem sim_call (as : List (Nat × BExp)) (env : BEnv) (heap : Heap) (a : A)
    (h : R a ⟨parSet env env as, heap⟩) : Sim R (.call as) ⟨env, heap⟩ (.call a) := ⟨_, rfl, h⟩

theorem sim_let (v : Nat) (e : BExp) (k : Tree) (env : BEnv) (heap : Heap) (x : BitVec 64) (o : LOut A)
    (hx : e.denote env = x) (h : Sim R k ⟨env.set v x, heap⟩ o) : Sim R (.let_ v e k) ⟨env, heap⟩ o := by
  subst hx; cases o <;> exact h

theorem sim_load (v b : Nat) (i : BExp) (k : Tree) (env : BEnv) (heap : Heap) (j : Nat) (y : BitVec 8)
    (o : LOut A) (hj : (i.denote env).toNat = j) (hr : rd heap b j = some y)
    (h : Sim R k ⟨env.set v (y.setWidth 64), heap⟩ o) : Sim R (.load v b i k) ⟨env, heap⟩ o := by
  have e : (Tree.load v b i k).step ⟨env, heap⟩ = k.step ⟨env.set v (y.setWidth 64), heap⟩ := by
    simp only [Tree.step, hj, hr, Option.bind_some]
  cases o <;> simp only [Sim, e] <;> exact h

theorem sim_cload (v b : Nat) (i c d : BExp) (k : Tree) (env : BEnv) (heap : Heap) (j : Nat) (z : BitVec 64)
    (o : LOut A) (hj : (i.denote env).toNat = j)
    (hc : c.denote env ≠ 0 → (rd heap b j).map (·.setWidth 64) = some z) (hd : c.denote env = 0 → d.denote env = z)
    (h : Sim R k ⟨env.set v z, heap⟩ o) : Sim R (.cload v b i c d k) ⟨env, heap⟩ o := by
  have e : (Tree.cload v b i c d k).step ⟨env, heap⟩ = k.step ⟨env.set v z, heap⟩ := by
    by_cases h0 : c.denote env = 0
    · simp only [Tree.step, if_pos h0, hd h0]
    · have := hc h0
      cases hr : rd heap b j with
      | none => rw [hr] at this; cases this
      | some x =>
        rw [hr] at this; simp only [Option.map_some, Option.some.injEq] at this
        simp only [Tree.step, if_neg h0, hj, hr, Option.bind_some, this]
  cases o <;> simp only [Sim, e] <;> exact h

theorem sim_dite (c : BExp) (a b : Tree) (env : BEnv) (heap : Heap) (P : Prop) [Decidable P]
    (o₁ : P → LOut A) (o₂ : ¬P → LOut A) (hc : c.denote env ≠ 0 ↔ P)
    (ht : ∀ h : P, Sim R a ⟨env, heap⟩ (o₁ h)) (hf : ∀ h : ¬P, Sim R b ⟨env, heap⟩ (o₂ h)) :
    Sim R (.ite c a b) ⟨env, heap⟩ (dite P o₁ o₂) := by
  by_cases hp : P
  · have e : (Tree.ite c a b).step ⟨env, heap⟩ = a.step ⟨env, heap⟩ := by
      simp only [Tree.step, if_neg (hc.2 hp)]
    rw [dif_pos hp]; have := ht hp
    cases h : o₁ hp <;> rw [h] at this <;> simp only [Sim, e] <;> exact this
  · have e : (Tree.ite c a b).step ⟨env, heap⟩ = b.step ⟨env, heap⟩ := by
      have : c.denote env = 0 := Classical.byContradiction fun h => hp (hc.1 h)
      simp only [Tree.step, if_pos this]
    rw [dif_neg hp]; have := hf hp
    cases h : o₂ hp <;> rw [h] at this <;> simp only [Sim, e] <;> exact this

/-- `sim_dite` under a function of the leaves (for bodies whose leaves are not `LOut` terms themselves) -/
theorem sim_dite_g {T : Type} (g : T → LOut A) (c : BExp) (a b : Tree) (env : BEnv) (heap : Heap) (P : Prop)
    [Decidable P] (x : P → T) (y : ¬P → T) (hc : c.denote env ≠ 0 ↔ P)
    (ht : ∀ h : P, Sim R a ⟨env, heap⟩ (g (x h))) (hf : ∀ h : ¬P, Sim R b ⟨env, heap⟩ (g (y h))) :
    Sim R (.ite c a b) ⟨env, heap⟩ (g (dite P x y)) := by
  have := sim_dite R c a b env heap P (fun h => g (x h)) (fun h => g (y h)) hc ht hf
  by_cases hp : P
  · rw [dif_pos hp] at this ⊢; exact this
  · rw [dif_neg hp] at this ⊢; exact this

theorem sim_pos {k : Tree} {σ : BState} {P : Prop} [Decidable P] {o₁ : P → LOut A} {o₂ : ¬P → LOut A} (h : P)
    (hs : Sim R k σ (dite P o₁ o₂)) : Sim R k σ (o₁ h) := by rwa [dif_pos h] at hs
theorem sim_neg {k : Tree} {σ : BState} {P : Prop} [Decidable P] {o₁ : P → LOut A} {o₂ : ¬P → LOut A} (h : ¬P)
    (hs : Sim R k σ (dite P o₁ o₂)) : Sim R k σ (o₂ h) := by rwa [dif_neg h] at hs

theorem sim_retm (e : BExp) (env : BEnv) (heap : Heap) (r : BitVec 64) (rs : List (Nat × BitVec 64))
    (h : e.denote env = r) (hr : ∀ p ∈ rs, env p.1 = p.2) : Sim R (.ret e) ⟨env, heap⟩ (.retm r rs) :=
  ⟨⟨env, heap⟩, by simp only [Tree.step, h], hr⟩

theorem sim_retm_elim {k : Tree} {σ : BState} {r : BitVec 64} {rs : List (Nat × BitVec 64)}
    (hs : Sim R k σ (.retm r rs)) : ∃ σ', k.step σ = some (.ret r σ') ∧ ∀ p ∈ rs, σ'.env p.1 = p.2 := hs

theorem sim_call_elim {k : Tree} {σ : BState} {a : A} (hs : Sim R k σ (.call a)) :
    ∃ σ₁, k.step σ = some (.call σ₁) ∧ R a σ₁ := hs
theorem sim_ret_elim {k : Tree} {σ : BState} {r : BitVec 64} (hs : Sim R k σ (.ret r)) :
    ∃ σ', k.step σ = some (.ret r σ') := hs
end

end Proven.Frontx

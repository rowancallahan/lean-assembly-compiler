/- `for i in [a:b]` loops in `Id`: the once-and-for-all part.

A loop `forIn [a:b] init F` (with `F : Nat → S → Id (ForInStep S)`, `S` the tuple of mutable locals) is run by a
tree whose state holds `i` and the locals: one iteration of the tree is "if `i < b` then the body, `yield s'`
being a call with `(i + 1, s')` and `done s'` a return, else return".  `for_exec` turns a proof of that single
step (`Sim`, built by the translator) into the theorem about the compiled program, initialisation included. -/
import Proven.Frontx.Tree

namespace Proven.Frontx
open Proven

/-- the leaves of a loop body as outcomes of one tree iteration -/
def cvt {S : Type} (post : S → BitVec 64) (i : Nat) : ForInStep S → LOut (Nat × S)
  | .yield s => .call (i + 1, s)
  | .done s => .ret (post s)

/-- `n` iterations from index `i` -/
def forFrom {S : Type} (F : Nat → S → Id (ForInStep S)) : Nat → Nat → S → S
  | 0, _, s => s
  | n + 1, i, s => match (F i s).run with
    | .done s' => s'
    | .yield s' => forFrom F n (i + 1) s'

theorem forIn_list_eq {S : Type} (F : Nat → S → Id (ForInStep S)) : ∀ (n i : Nat) (s : S),
    (forIn (m := Id) (List.range' i n 1) s F).run = forFrom F n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
    rw [List.range'_succ, List.forIn_cons]
    simp only [forFrom]
    cases h : (F i s).run with
    | done s' =>
      have : F i s = pure (ForInStep.done s') := h
      rw [this]; rfl
    | yield s' =>
      have : F i s = pure (ForInStep.yield s') := h
      rw [this]; exact forIn_list_eq F n (i + 1) s'

theorem forIn_range_eq {S : Type} (F : Nat → S → Id (ForInStep S)) (a b : Nat) (init : S) :
    (forIn (m := Id) [a:b] init F).run = forFrom F (b - a) a init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_list_eq F (b - a) a init

section
variable {S : Type} (R : Nat × S → BState → Prop) (t : Tree) (F : Nat → S → Id (ForInStep S))
  (post : S → BitVec 64) (b : Nat)

theorem for_runs
    (hstep : ∀ i s σ, R (i, s) σ →
      Sim R t σ (dite (i < b) (fun _ => cvt post i (F i s).run) (fun _ => .ret (post s)))) :
    ∀ (n i : Nat) (s : S) (σ : BState), n = b - i → R (i, s) σ →
      ∃ σ', t.Runs σ (post (forFrom F n i s)) σ'
  | 0, i, s, σ, hn, hR => by
    have h := hstep i s σ hR
    rw [dif_neg (by omega)] at h
    obtain ⟨σ', hs⟩ := h
    exact step_ret σ' hs
  | n + 1, i, s, σ, hn, hR => by
    have h := hstep i s σ hR
    rw [dif_pos (by omega)] at h
    simp only [forFrom]
    cases hF : (F i s).run with
    | done s' =>
      rw [hF] at h
      obtain ⟨σ', hs⟩ := h
      exact step_ret σ' hs
    | yield s' =>
      rw [hF] at h
      obtain ⟨σ₁, hs, hR₁⟩ := h
      exact step_call σ₁ hs (for_runs hstep n (i + 1) s' σ₁ (by omega) hR₁)
end

/-! ## primitive recursion on a `Nat` is a loop counting up

`f 0 = b`, `f (j + 1) = h j (f j)` (the recursive call need not be in tail position): `f k` is the loop
`acc := b; for j in [0:k] do acc := h j acc`.  This is the accumulator transformation, proved once. -/

theorem natRec_forFrom {β : Type} (f : Nat → β) (h : Nat → β → β) (hs : ∀ j, f (j + 1) = h j (f j)) :
    ∀ (n i : Nat), forFrom (fun j acc => pure (ForInStep.yield (h j acc))) n i (f i) = f (i + n)
  | 0, _ => rfl
  | n + 1, i => by
    show forFrom _ n (i + 1) (h i (f i)) = _
    rw [← hs i, natRec_forFrom f h hs n (i + 1)]; congr 1; omega

theorem natRec_forIn {β : Type} (f : Nat → β) (h : Nat → β → β) (hs : ∀ j, f (j + 1) = h j (f j)) (k : Nat) :
    f k = (forIn (m := Id) [0:k] (f 0) (fun j acc => pure (ForInStep.yield (h j acc)))).run := by
  rw [forIn_range_eq, natRec_forFrom f h hs]; simp

/-! ## a test before the loop

`if c then v else (loop; post)` is the loop over the range `[a : if c then a else b]` (empty when `c` holds)
followed by `if c then v else post`.  So a pre-test needs no sequencing of programs. -/

theorem pretest_eq {S β : Type} (c : Prop) [Decidable c] (v : β) (a b : Nat) (init : S)
    (F : Nat → S → Id (ForInStep S)) (post : S → β) :
    (if c then v else post (forIn (m := Id) [a:b] init F).run) =
      (fun s => if c then v else post s) (forIn (m := Id) [a : if c then a else b] init F).run := by
  by_cases h : c
  · simp only [if_pos h]
  · simp only [if_neg h]

/-! ## initialisation of the loop variables -/

def initS : List (Nat × BExp) → BStmt → BStmt
  | [], p => p
  | (v, e) :: l, p => .seq (.assign v e) (initS l p)

def seqSet (env : BEnv) : List (Nat × BExp) → BEnv
  | [] => env
  | (v, e) :: l => seqSet (env.set v (e.denote env)) l

theorem initS_exec {p : BStmt} {heap : Heap} {σ' : BState} : ∀ (l : List (Nat × BExp)) (env : BEnv),
    BExec p ⟨seqSet env l, heap⟩ σ' → BExec (initS l p) ⟨env, heap⟩ σ'
  | [], _, h => h
  | (v, e) :: l, env, h => .seq .assign (initS_exec l (env.set v (e.denote env)) h)

/-- **`for` loop, once and for all** (read-only tree): the single-step simulation and the loop relation at the
initialised state give the compiled program's theorem. -/
theorem for_exec {S : Type} (L : Lay) {t : Tree} (hw : t.wf L) (hro : t.ro = true) (R : Nat × S → BState → Prop)
    (F : Nat → S → Id (ForInStep S)) (post : S → BitVec 64) (a b : Nat) (init : S)
    (inits : List (Nat × BExp)) (out : Nat)
    (hstep : ∀ i s σ, R (i, s) σ →
      Sim R t σ (dite (i < b) (fun _ => cvt post i (F i s).run) (fun _ => .ret (post s))))
    {env : BEnv} {heap : Heap} (h0 : R (a, init) ⟨seqSet env inits, heap⟩) :
    ∃ σ', BExec (initS inits (prog L t out)) ⟨env, heap⟩ σ' ∧
      σ'.env out = post (forIn (m := Id) [a:b] init F).run ∧ σ'.heap = heap := by
  rw [forIn_range_eq]
  obtain ⟨σ', h1, h2, h3⟩ := prog_ok_ro L hw hro (for_runs R t F post b hstep (b - a) a init _ rfl h0) out
  exact ⟨σ', initS_exec inits env h1, h2, h3⟩

end Proven.Frontx

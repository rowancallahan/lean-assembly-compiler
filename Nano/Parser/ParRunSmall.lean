/- Nano/Parser/ParRunSmall: the WIDTH CAP invariant of Layer 2 (pure).  In every state reachable from `init`,
the next slot `nx`, the parameter width `npw` and every shape the machine stores a width word for (values, bindings, the
type register, the current row's result / params, the defs' results, pending `tyPair` frames) are below 2^20, so Par1's
64-bit width and slot cells equal ParRun's `Nat`s (Layer 3 uses it to match Par1's cap checks). -/
import Nano.Parser.ParRunCInv
namespace ParRun
open ParSpec

def Small (c : List Frame × St) : Prop :=
  c.2.nx < 2 ^ 20 ∧ c.2.cur.npw < 2 ^ 20 ∧ cw c.2.ty < 2 ^ 20 ∧ cw c.2.cur.res < 2 ^ 20 ∧
  (∀ s ∈ c.2.cur.params, s.width < 2 ^ 20) ∧ (∀ v ∈ c.2.vals, cw v.sh < 2 ^ 20) ∧ (∀ b ∈ c.2.binds, cw b.sh < 2 ^ 20) ∧
  (∀ d ∈ c.2.defs, cw d.res < 2 ^ 20) ∧ (∀ l, Frame.tyPair l ∈ c.1 → l.width < 2 ^ 20)

theorem mkNode_eqS {st st' : St} {t a b : Nat} {sh : Option Sh} {p : Bool} {n : Nat} (h : mkNode st t a b sh p n = some st') :
    st' = { st with vals := RN.mk t a b sh p (st.vals.take n).reverse :: st.vals.drop n,
                    arena := st.arena ++ [RN.mk t a b sh p (st.vals.take n).reverse] } := by
  unfold mkNode at h; split at h <;> cases h; rfl

theorem locOf_eqS {st st' : St} {bd : Bd} (h : locOf st bd = some st') :
    st' = { st with vals := RN.mk 2 bd.slot (if bd.inp then 0 else cw bd.sh) bd.sh false [] :: st.vals,
                    arena := st.arena ++ [RN.mk 2 bd.slot (if bd.inp then 0 else cw bd.sh) bd.sh false []] } := by
  unfold locOf at h; split at h <;> cases h; rfl

theorem small_init (toks : List Tok) : Small ([.defs], init toks) := by
  simp [Small, init, DefR.fresh, cw]

theorem cw_some (s : Sh) : cw (some s) = s.width := rfl

theorem primRes_w (p : Nat) : (primRes p).width = 1 := by unfold primRes; split <;> (try split) <;> (try split) <;> rfl

theorem rows_small {st : St} (h8 : ∀ d ∈ st.defs, cw d.res < 2 ^ 20) (h4 : cw st.cur.res < 2 ^ 20) {j : Nat} {d : DefR}
    (h : (rows st)[j]? = some d) : cw d.res < 2 ^ 20 := by
  have hm : d ∈ rows st := List.mem_of_getElem? h
  simp only [rows, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · exact h8 d hm
  · exact h4

theorem ty_small {st : St} (h3 : cw st.ty < 2 ^ 20) {w : Sh} (h : st.ty = some w) : w.width < 2 ^ 20 := by
  rw [h] at h3; exact h3

theorem cw_none : cw none = 1 := rfl

theorem pair_small {v : RN} {n : Nat} {l r : Sh} (hv : v.sh = some (.p l r)) (hc : ¬ 2 ^ 20 ≤ n + cw v.sh) :
    l.width < 2 ^ 20 ∧ r.width < 2 ^ 20 := by
  rw [hv] at hc; simp only [cw, Sh.width] at hc; omega

theorem fresh_small (x : List Nat) : (DefR.fresh x).npw = 0 ∧ cw (DefR.fresh x).res = 1 ∧ (DefR.fresh x).params = [] := ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem small_step {f : Frame} {fs : List Frame} {st st' : St} {k : List Frame} (hi : Small (f :: fs, st))
    (h : stepF f st = some (k, st')) : Small (k ++ fs, st') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hi
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp only [List.mem_cons] at h9
  have h9' : ∀ l, Frame.tyPair l ∈ fs → l.width < 2 ^ 20 := fun l hl => h9 l (Or.inr hl)
  have h6' : ∀ n, ∀ v ∈ st.vals.drop n, cw v.sh < 2 ^ 20 := fun n v hv => h6 v (List.mem_of_mem_drop hv)
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (first
       | (obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h; cases he
          first | (have e := mkNode_eqS hm; subst e) | (have e := locOf_eqS hm; subst e))
       | (obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h; cases he
          obtain ⟨st1, h1', h2'⟩ := Option.bind_eq_some_iff.mp hm
          have e2 := mkNode_eqS h2'; subst e2
          split at h1'
          · cases h1'
          · have e1 := mkNode_eqS h1'; subst e1
          · have e1 := mkNode_eqS h1'; subst e1)
       | (obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h; cases he
          obtain ⟨st1, h1', h2'⟩ := Option.bind_eq_some_iff.mp hm
          have e2 := mkNode_eqS h2'; subst e2
          have e1 := mkNode_eqS h1'; subst e1)
       | cases h)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only [leaf]) <;>
        (try simp only [List.forall_mem_cons, List.forall_mem_append, List.forall_mem_nil, List.nil_append, List.cons_append,
          RN.sh_mk, cw_some, Sh.width, primRes_w, List.drop_zero, fresh_small, and_true, true_and]) <;>
        (try simp only [List.mem_cons, List.mem_append, Frame.tyPair.injEq, reduceCtorEq, false_or, or_false,
          List.not_mem_nil, false_imp_iff, implies_true, and_true, cw_none]) <;>
        first
        | assumption
        | omega
        | trivial
        | exact h6' _
        | exact fun b hb => h7 b (List.mem_of_mem_take hb)
        | (intro _ hf; exact hf.elim)
        | exact ⟨by decide, h6' _⟩
        | exact ⟨by decide, h6⟩
        | exact ⟨by omega, h6' _⟩
        | exact ⟨h7 _ (findB_mem ‹_›), h6⟩
        | exact ⟨rows_small h8 h4 ‹_›, h6' _⟩
        | exact ⟨rows_small h8 h4 ‹_›, h6⟩
        | exact ⟨h6 _ (by rw [‹st.vals = _›]; simp), h6' _⟩
        | exact ty_small h3 ‹_›
        | exact ⟨h7, by omega⟩
        | exact ⟨h7, ty_small h3 ‹_›⟩
        | exact ⟨h5, ty_small h3 ‹_›⟩
        | exact ⟨h5, by decide⟩
        | exact ⟨h7, by decide⟩
        | exact ⟨h7, pair_small ‹_› ‹_›⟩
        | exact ⟨h7, h5 _ (List.mem_of_getElem? ‹_›)⟩
        | exact ⟨h8 _ (List.mem_of_getElem? ‹_›), h6⟩
        | (intro l hl; rcases hl with rfl | hl
           · exact ty_small h3 ‹_›
           · exact h9' l hl)
        | (intro b hb; rcases List.mem_or_eq_of_mem_set hb with hb | rfl
           · exact h7 b hb
           · exact ty_small h3 ‹_›)
        | skip
    | skip

theorem stepS_small {c d : List Frame × St} (hs : stepS c = some d) (hi : Small c) : Small d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    exact small_step hi h1

theorem Star.small {c d : List Frame × St} (h : Star c d) (hi : Small c) : Small d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_small hs hi)

end ParRun
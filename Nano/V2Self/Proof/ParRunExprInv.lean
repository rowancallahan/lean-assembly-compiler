/- Nano/V2Self/Proof/ParRunExprInv: inversion lemmas for the expression frames (if / let / pair-let / parens / tuples / primary). -/
import Nano.V2Self.Proof.ParRunExpr
namespace ParRun
open ParSpec

set_option hygiene false in
macro "inv_auto" : tactic => `(tactic| (
  simp only [stepF] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try (obtain ⟨rfl, rfl⟩ := h)) <;> simp_all))

theorem ifCmp_inv {tl st k st'} (h : stepF (.ifCmp tl) st = some (k, st')) :
    ∃ c r, (st.toks = .k 23 :: r ∧ c = 1 ∨ st.toks = .k 20 :: r ∧ c = 2) ∧ k = [.expr 0 2, .ifThen c tl] ∧ st' = { st with toks := r } := by
  inv_auto

theorem ifThen_inv {c tl st k st'} (h : stepF (.ifThen c tl) st = some (k, st')) :
    ∃ r, st.toks = .k 33 :: r ∧ k = [.expr 0 (bm tl), .ifElse, .expr 0 (bm tl), .mkIte c] ∧ st' = { st with toks := r } := by
  inv_auto

theorem ifElse_inv {st k st'} (h : stepF .ifElse st = some (k, st')) :
    ∃ r, st.toks = .k 34 :: r ∧ k = [] ∧ st' = { st with toks := r } := by
  inv_auto

theorem mkIte_inv {c st k st'} (h : stepF (.mkIte c) st = some (k, st')) :
    ∃ e t b a rest, st.vals = e :: t :: b :: a :: rest ∧ a.sh = some .uw ∧ b.sh = some .uw ∧ t.sh = e.sh ∧ k = [] ∧
      st' = { st with vals := RN.mk 4 c 0 e.sh (t.pend || e.pend) [a, b, t, e] :: rest,
                      arena := st.arena ++ [RN.mk 4 c 0 e.sh (t.pend || e.pend) [a, b, t, e]] } := by
  simp only [stepF] at h
  split at h
  · rename_i e t b a rest hv
    split at h
    · obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h
      simp at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨_, rfl⟩ := mkNode_inv hm
      exact ⟨e, t, b, a, rest, hv, ‹_ ∧ _ ∧ _›.1, ‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2, rfl, by simp [hv]⟩
    · simp at h
  · simp at h

theorem letStart_inv {tl st k st'} (h : stepF (.letStart tl) st = some (k, st')) :
    (∃ x r, st.toks = .id x :: .k 9 :: r ∧ k = [.expr 0 0, .letSemi x tl] ∧ st' = { st with toks := r }) ∨
    (∃ r, st.toks = .k 6 :: r ∧ k = [.letPairX tl] ∧ st' = { st with toks := r }) := by
  inv_auto

theorem letSemi_inv {x tl st k st'} (h : stepF (.letSemi x tl) st = some (k, st')) :
    ∃ r v rest, st.toks = .k 13 :: r ∧ st.vals = v :: rest ∧ v.sh ≠ some .nt ∧
      k = [.expr 0 (bm tl), .letEnd st.nx st.binds.length] ∧
      st' = { st with toks := r, nx := st.nx + cw v.sh, binds := st.binds ++ [⟨x, st.nx, v.sh, false⟩] } := by
  inv_auto

theorem letEnd_inv {s d st k st'} (h : stepF (.letEnd s d) st = some (k, st')) :
    ∃ body v rest, st.vals = body :: v :: rest ∧ k = [] ∧
      st' = { st with binds := st.binds.take d, vals := RN.mk 5 s (cw v.sh) body.sh body.pend [v, body] :: rest,
                      arena := st.arena ++ [RN.mk 5 s (cw v.sh) body.sh body.pend [v, body]] } := by
  simp only [stepF] at h
  split at h
  · rename_i body v rest hv
    obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h
    simp at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨_, rfl⟩ := mkNode_inv hm
    exact ⟨body, v, rest, hv, rfl, by simp [hv]⟩
  · simp at h

theorem letPairX_inv {tl st k st'} (h : stepF (.letPairX tl) st = some (k, st')) :
    ∃ x r, st.toks = .id x :: .k 15 :: r ∧ k = [.letPairY x tl] ∧ st' = { st with toks := r } := by
  inv_auto

theorem letPairY_inv {x tl st k st'} (h : stepF (.letPairY x tl) st = some (k, st')) :
    ∃ y r, st.toks = .id y :: .k 7 :: .k 9 :: r ∧ k = [.expr 0 0, .stash x, .letPairSemi y tl] ∧ st' = { st with toks := r } := by
  inv_auto

theorem stash_eq (x : List Nat) (st : St) : stepF (.stash x) st = some ([], { st with stash := x }) := rfl

theorem letPairSemi_inv {y tl st k st'} (h : stepF (.letPairSemi y tl) st = some (k, st')) :
    ∃ r v rest l rr x, st.toks = .k 13 :: r ∧ st.vals = v :: rest ∧ st.stash = some x ∧ v.sh = some (.p l rr) ∧
      k = [.expr 0 (bm tl), .letEnd st.nx st.binds.length] ∧
      st' = { st with toks := r, nx := st.nx + cw v.sh,
                      binds := st.binds ++ [⟨x, st.nx, some l, false⟩, ⟨y, st.nx + l.width, some rr, false⟩] } := by
  inv_auto
  exact ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem parenClose_inv {st k st'} (h : stepF .parenClose st = some (k, st')) :
    (∃ r, st.toks = .k 7 :: r ∧ k = [] ∧ st' = { st with toks := r }) ∨
    (∃ r, st.toks = .k 15 :: r ∧ k = [.expr 0 0, .tupRest, .mkPair] ∧ st' = { st with toks := r }) := by
  inv_auto

theorem tupRest_inv {st k st'} (h : stepF .tupRest st = some (k, st')) :
    (∃ r, st.toks = .k 7 :: r ∧ k = [] ∧ st' = { st with toks := r }) ∨
    (∃ r, st.toks = .k 15 :: r ∧ k = [.expr 0 0, .tupRest, .mkPair] ∧ st' = { st with toks := r }) := by
  inv_auto

theorem mkPair_inv {st k st'} (h : stepF .mkPair st = some (k, st')) :
    ∃ y x rest l r, st.vals = y :: x :: rest ∧ x.sh = some l ∧ y.sh = some r ∧ x.pend = false ∧ y.pend = false ∧
      l ≠ .nt ∧ r ≠ .nt ∧ k = [] ∧
      st' = { st with ty := some (.p l r), vals := RN.mk 6 2 0 (some (.p l r)) false [x, y] :: rest,
                      arena := st.arena ++ [RN.mk 6 2 0 (some (.p l r)) false [x, y]] } := by
  simp only [stepF] at h
  split at h
  · rename_i y x rest hv
    split at h
    · rename_i l r hl hr
      split at h
      · simp at h
      · split at h
        · simp at h
        · obtain ⟨st2, hm, he⟩ := Option.map_eq_some_iff.mp h
          simp at he; obtain ⟨rfl, rfl⟩ := he
          obtain ⟨_, rfl⟩ := mkNode_inv hm
          refine ⟨y, x, rest, l, r, hv, hl, hr, ?_, ?_, ?_, ?_, rfl, by simp [hv]⟩ <;> simp_all
    · simp at h
  · simp at h

theorem expr_eq (m md : Nat) (st : St) : stepF (.expr m md) st = some ([.prim md, .binLoop m], st) := rfl


/-- the cases of a primary (task 3); `tl = (md == 1)` -/
inductive PrimCase (md : Nat) (st : St) : List Frame → St → Prop
  | ifs {r} : md ≠ 2 → st.toks = .k 32 :: r → PrimCase md st [.expr 0 2, .ifCmp (md == 1)] { st with toks := r }
  | lets {r} : md ≠ 2 → st.toks = .k 2 :: r → PrimCase md st [.letStart (md == 1)] { st with toks := r }
  | leaf {st1} : AtomLeaf st st1 → (∀ x r, st.toks = .id x :: r → (findB st.binds x).isSome) → PrimCase md st [] st1
  | paren {r} : st.toks = .k 6 :: r → PrimCase md st [.expr 0 (bm (md == 1)), .parenClose] { st with toks := r }
  | self {x r} : st.toks = .id x :: r → findB st.binds x = none → findD (rows st) x = some st.defs.length → md = 1 → st.arm = true →
      PrimCase md st [.selfArgs] { st with toks := r }
  | call {x r j} : st.toks = .id x :: r → findB st.binds x = none → findD (rows st) x = some j → j ≠ st.defs.length →
      PrimCase md st [.args (.df j) (arity st (.df j)), .mkCallN (.df j) st.vals.length] { st with toks := r }
  | primTok {t r} : st.toks = .k t :: r → 38 < t → t < 48 →
      PrimCase md st [.args (.pr (t - 38)) (primAr (t - 38)), .mkCallN (.pr (t - 38)) st.vals.length] { st with toks := r }

theorem prim_inv {md st k st'} (h : stepF (.prim md) st = some (k, st')) : PrimCase md st k st' := by
  simp only [stepF] at h
  split at h
  · simp at h
  · rename_i hmd
    split at h
    · rename_i r ht
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .ifs (fun h2 => hmd ⟨h2, Or.inl (by simp [ht])⟩) ht
    · rename_i r ht
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .lets (fun h2 => hmd ⟨h2, Or.inr (by simp [ht])⟩) ht
    · rename_i v r ht
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .leaf (.num ht) (fun x r' h' => by rw [ht] at h'; cases h')
    · rename_i r ht
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .paren ht
    · rename_i x r ht
      split at h
      · rename_i bd hb
        obtain ⟨st1, hl, he⟩ := Option.map_eq_some_iff.mp h
        simp at he; obtain ⟨rfl, rfl⟩ := he
        exact .leaf (.loc ht hb hl) (fun x' r' h' => by rw [ht] at h'; cases h'; simp [hb])
      · rename_i hb
        split at h
        · simp at h
        · rename_i j hj
          split at h
          · rename_i hjd
            split at h
            · simp at h; obtain ⟨rfl, rfl⟩ := h
              rename_i htl
              simp only [Bool.and_eq_true, beq_iff_eq] at htl
              subst hjd
              exact .self ht hb hj htl.1 htl.2
            · simp at h
          · rename_i hjd
            simp at h; obtain ⟨rfl, rfl⟩ := h
            exact .call ht hb hj hjd
    · rename_i r ht
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact .leaf (.nil ht) (fun x r' h' => by rw [ht] at h'; cases h')
    · rename_i t r ht
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h
        exact .primTok ht ‹_ ∧ _ ∧ _›.2.1 ‹_ ∧ _ ∧ _›.2.2
      · simp at h
    · simp at h

end ParRun

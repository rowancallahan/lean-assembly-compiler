/- Nano/V2Self/Proof/Parser/ParRunWFStep: preservation of the ghost part of `WF` (one lemma per frame, `gh_<frame>`). -/
import Nano.V2Self.Proof.Parser.ParRunWF
namespace ParRun
open ParSpec

def G.le (g g' : G) : Prop := g.v = g'.v ∧ g.b = g'.b ∧ (g.t → g'.t)

theorem mkNode_eq {st tag a b sh p n st'} : mkNode st tag a b sh p n = some st' ↔
    n ≤ st.vals.length ∧ st' = { st with vals := RN.mk tag a b sh p (st.vals.take n).reverse :: st.vals.drop n,
                                         arena := st.arena ++ [RN.mk tag a b sh p (st.vals.take n).reverse] } := by
  unfold mkNode; split
  · simp_all [eq_comm]
  · simp only [reduceCtorEq, false_iff, not_and]; intro; omega

theorem locOf_eq {st bd st'} : locOf st bd = some st' ↔ bd.sh ≠ some .nt ∧
    st' = { st with vals := RN.mk 2 bd.slot (if bd.inp then 0 else cw bd.sh) bd.sh false [] :: st.vals,
                    arena := st.arena ++ [RN.mk 2 bd.slot (if bd.inp then 0 else cw bd.sh) bd.sh false []] } := by
  unfold locOf; by_cases hn : bd.sh = some .nt
  · simp [hn]
  · simp only [hn, if_false, Option.some.injEq, ne_eq, not_false_eq_true, true_and]; exact eq_comm

theorem findD_lt {l : List DefR} {x j} (h : findD l x = some j) : j < l.length := by
  unfold findD at h
  cases h' : (l.reverse.findIdx? fun d => d.name == x) with
  | none => simp [h'] at h
  | some i => simp [h'] at h; have := List.findIdx?_eq_some_iff_findIdx_eq.mp h'; simp at this; omega

theorem rows_len (st : St) : (rows st).length = st.defs.length + 1 := by simp [rows]

theorem rows_upd_eq (st : St) : rows st = st.defs ++ [st.cur] := rfl

set_option hygiene false in
macro "ghost_auto" : tactic => `(tactic| (
  simp only [stepF] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq,
      mkNode_eq, locOf_eq, and_assoc, exists_and_left, exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right',
      exists_const] at h <;>
    (repeat (obtain ⟨_, h⟩ := h)) <;> (try subst_vars) <;>
    (try (have := findD_lt ‹findD _ _ = some _›)) <;>
    simp [effL, effF, St.g, St.ctx, G.le, leaf, arity, Ctx.arity, Ctx.callTgt, Ctx.callee, rows_len, Frame.final, Ctx.npar, rows_upd_eq] at he ⊢ <;>
    (try subst g1) <;> (try (obtain ⟨_, rfl⟩ := he)) <;> (try simp_all [rows_len, Ctx.npar, rows_upd_eq]) <;> (try omega)))

theorem gh_expr {m tl} {st k st' g1} (h : stepF (.expr m tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.expr m tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.expr m tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_binLoop {m} {st k st' g1} (h : stepF (.binLoop m) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.binLoop m) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.binLoop m) ∨ g1.le g2) := by
  ghost_auto

theorem gh_prim {tl} {st k st' g1} (h : stepF (.prim tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.prim tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.prim tl) ∨ g1.le g2) := by
  ghost_auto
  · refine ⟨_, ⟨⟨by omega, ?_, by simp [Callee.need1]⟩, rfl⟩, rfl, rfl, id⟩
    have := findD_lt ‹findD _ _ = some _›; simp at this; omega
  · rename_i t _ _ _ _ _ ht
    refine ⟨_, ⟨⟨by omega, fun hp => ?_⟩, rfl⟩, rfl, rfl, id⟩
    simp [Callee.need1] at hp
    obtain rfl | rfl | rfl : t = 39 ∨ t = 40 ∨ t = 41 := by omega
    all_goals decide

theorem gh_rparen {st k st' g1} (h : stepF .rparen st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .rparen st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .rparen ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkBin {op} {st k st' g1} (h : stepF (.mkBin op) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.mkBin op) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.mkBin op) ∨ g1.le g2) := by
  ghost_auto

theorem gh_ifCmp {tl} {st k st' g1} (h : stepF (.ifCmp tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.ifCmp tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.ifCmp tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_ifThen {c tl} {st k st' g1} (h : stepF (.ifThen c tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.ifThen c tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.ifThen c tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_ifElse {st k st' g1} (h : stepF .ifElse st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .ifElse st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .ifElse ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkIte {c} {st k st' g1} (h : stepF (.mkIte c) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.mkIte c) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.mkIte c) ∨ g1.le g2) := by
  ghost_auto

theorem gh_letSemi {x tl} {st k st' g1} (h : stepF (.letSemi x tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letSemi x tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letSemi x tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_letEnd {s d} {st k st' g1} (h : stepF (.letEnd s d) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letEnd s d) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letEnd s d) ∨ g1.le g2) := by
  ghost_auto

theorem gh_parenClose {st k st' g1} (h : stepF .parenClose st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .parenClose st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .parenClose ∨ g1.le g2) := by
  ghost_auto

theorem gh_letStart {tl} {st k st' g1} (h : stepF (.letStart tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letStart tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letStart tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkPair {st k st' g1} (h : stepF .mkPair st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .mkPair st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .mkPair ∨ g1.le g2) := by
  ghost_auto

theorem gh_argAtom {st k st' g1} (h : stepF .argAtom st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .argAtom st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .argAtom ∨ g1.le g2) := by
  ghost_auto

theorem gh_args {c n} {st k st' g1} (h : stepF (.args c n) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.args c n) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.args c n) ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkCallN {c d} {st k st' g1} (h : stepF (.mkCallN c d) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.mkCallN c d) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.mkCallN c d) ∨ g1.le g2) := by
  ghost_auto
  cases c <;> dsimp only at * <;> simp_all
  · rw [if_pos (by omega)]; simp only [Option.bind_some]; rw [if_pos ⟨by omega, by simp [Callee.need1]⟩]
    exact ⟨_, rfl, by simp; omega, rfl, id⟩
  · rename_i hl
    exact ⟨_, ⟨fun hp => by have := hl.2.2 hp; omega, rfl⟩, by simp; omega, rfl, id⟩

theorem gh_selfArgs {st k st' g1} (h : stepF .selfArgs st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .selfArgs st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .selfArgs ∨ g1.le g2) := by
  ghost_auto
  all_goals first | exact ⟨_, ⟨by omega, rfl⟩, rfl, rfl, id⟩ | exact ⟨_, rfl, by omega, rfl, id⟩ |
    (rw [if_pos (by omega)]; simp only [Option.bind_some]; rw [if_pos (by omega)]; exact ⟨_, rfl, by simp, rfl, id⟩)

theorem gh_argCheck {c n} {st k st' g1} (h : stepF (.argCheck c n) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.argCheck c n) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.argCheck c n) ∨ g1.le g2) := by
  ghost_auto
  all_goals refine ⟨_, ⟨⟨by omega, ?_⟩, rfl⟩, rfl, rfl, id⟩; cases c <;> dsimp only at * <;> omega

theorem gh_mkCall {c n} {st k st' g1} (h : stepF (.mkCall c n) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.mkCall c n) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.mkCall c n) ∨ g1.le g2) := by
  ghost_auto

theorem gh_shiftNum {op} {st k st' g1} (h : stepF (.shiftNum op) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.shiftNum op) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.shiftNum op) ∨ g1.le g2) := by
  ghost_auto

theorem gh_letPairX {tl} {st k st' g1} (h : stepF (.letPairX tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letPairX tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letPairX tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_letPairY {x tl} {st k st' g1} (h : stepF (.letPairY x tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letPairY x tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letPairY x tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_stash {x} {st k st' g1} (h : stepF (.stash x) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.stash x) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.stash x) ∨ g1.le g2) := by
  ghost_auto

theorem gh_letPairSemi {y tl} {st k st' g1} (h : stepF (.letPairSemi y tl) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.letPairSemi y tl) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.letPairSemi y tl) ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkCont {f n} {st k st' g1} (h : stepF (.mkCont f n) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.mkCont f n) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.mkCont f n) ∨ g1.le g2) := by
  ghost_auto

theorem gh_argName {st k st' g1} (h : stepF .argName st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .argName st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .argName ∨ g1.le g2) := by
  ghost_auto

theorem gh_defs {st k st' g1} (h : stepF .defs st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .defs st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .defs ∨ g1.le g2) := by
  ghost_auto

theorem gh_tyAtom {st k st' g1} (h : stepF .tyAtom st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .tyAtom st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .tyAtom ∨ g1.le g2) := by
  ghost_auto

theorem gh_tyCross {st k st' g1} (h : stepF .tyCross st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .tyCross st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .tyCross ∨ g1.le g2) := by
  ghost_auto

theorem gh_tyPair {l} {st k st' g1} (h : stepF (.tyPair l) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.tyPair l) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.tyPair l) ∨ g1.le g2) := by
  ghost_auto

theorem gh_binders {st k st' g1} (h : stepF .binders st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .binders st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .binders ∨ g1.le g2) := by
  ghost_auto

theorem gh_group {a} {st k st' g1} (h : stepF (.group a) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.group a) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.group a) ∨ g1.le g2) := by
  ghost_auto

theorem gh_assign {a sz} {st k st' g1} (h : stepF (.assign a sz) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.assign a sz) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.assign a sz) ∨ g1.le g2) := by
  ghost_auto
  all_goals exact ⟨_, ⟨by omega, rfl⟩, rfl, rfl, rfl⟩

theorem gh_plainBody {st k st' g1} (h : stepF .plainBody st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .plainBody st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .plainBody ∨ g1.le g2) := by
  ghost_auto

theorem gh_afterColon {st k st' g1} (h : stepF .afterColon st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .afterColon st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .afterColon ∨ g1.le g2) := by
  ghost_auto

theorem gh_stateTy {st k st' g1} (h : stepF .stateTy st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .stateTy st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .stateTy ∨ g1.le g2) := by
  ghost_auto

theorem gh_armsStart {st k st' g1} (h : stepF .armsStart st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .armsStart st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .armsStart ∨ g1.le g2) := by
  ghost_auto

theorem gh_armBind {stp i} {st k st' g1} (h : stepF (.armBind stp i) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.armBind stp i) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.armBind stp i) ∨ g1.le g2) := by
  ghost_auto

theorem gh_zeroDone {st k st' g1} (h : stepF .zeroDone st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .zeroDone st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .zeroDone ∨ g1.le g2) := by
  ghost_auto

theorem gh_mkLoop {st k st' g1} (h : stepF .mkLoop st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .mkLoop st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .mkLoop ∨ g1.le g2) := by
  ghost_auto

theorem gh_defEnd {st k st' g1} (h : stepF .defEnd st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .defEnd st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .defEnd ∨ g1.le g2) := by
  ghost_auto

theorem gh_flat {nd} {st k st' g1} (h : stepF (.flat nd) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.flat nd) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.flat nd) ∨ g1.le g2) := by
  ghost_auto

theorem gh_flatL {ns} {st k st' g1} (h : stepF (.flatL ns) st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx (.flatL ns) st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final (.flatL ns) ∨ g1.le g2) := by
  ghost_auto

theorem gh_defClose {st k st' g1} (h : stepF .defClose st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .defClose st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .defClose ∨ g1.le g2) := by
  ghost_auto

theorem gh_tupRest {st k st' g1} (h : stepF .tupRest st = some (k, st')) (hv : ∀ x ∈ st.vals, x.sh.isSome) (he : effF st.ctx .tupRest st.g = some g1) :
    ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (Frame.final .tupRest ∨ g1.le g2) := by
  ghost_auto

end ParRun

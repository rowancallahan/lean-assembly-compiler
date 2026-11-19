/- Nano/V2Self/Proof/ParRunWFInv: preservation of the state parts of `WF` (stack values have a shape code, finished defs and the
current def in a loop step arm have a result code), one lemma per frame (`si_<frame>`). -/
import Nano.V2Self.Proof.ParRunWFStep
namespace ParRun
open ParSpec


theorem findB_mem {bs : List Bd} {x bd} (h : findB bs x = some bd) : bd ∈ bs := by
  unfold findB at h; exact List.mem_reverse.mp (List.mem_of_find?_eq_some h)

theorem take_mem {l : List RN} {n x} (h : x ∈ (l.take n).reverse) : x ∈ l := List.mem_of_mem_take (List.mem_reverse.mp h)

@[simp] theorem RN.sh_mk (t a b : Nat) (s : Option Sh) (p : Bool) (k : List RN) : (RN.mk t a b s p k).sh = s := rfl

theorem rows_get_lt {st : St} {j d} (hj : j < st.defs.length) (h : (st.defs ++ [st.cur])[j]? = some d) : d ∈ st.defs := by
  rw [List.getElem?_append_left hj] at h; exact List.mem_of_getElem? h

theorem rows_get_last {st : St} {d} (h : (st.defs ++ [st.cur])[st.defs.length]? = some d) : d = st.cur := by
  simp at h; exact h.symm

set_option hygiene false in
macro "si_auto" : tactic => `(tactic| (
  simp only [stepF] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq,
      mkNode_eq, locOf_eq, and_assoc, exists_and_left, exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right',
      exists_const] at h <;>
    (repeat (obtain ⟨_, h⟩ := h)) <;> (try subst_vars) <;>
    (try (have := findB_mem ‹findB _ _ = some _›)) <;>
    simp [SInv, effF, St.g, St.ctx, leaf, Ctx.callTgt, rows_upd_eq, Ctx.npar] at hi he ⊢ <;>
    (try simp_all [SInv, rows_upd_eq]) <;>
    (try (intro a ha; first | exact hi.1 a (List.mem_of_mem_drop ha) | exact hi.1 a (List.mem_of_mem_tail ha))) <;> (try omega)))

theorem si_expr {m tl} {st k st' g1} (h : stepF (.expr m tl) st = some (k, st')) (he : effF st.ctx (.expr m tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_binLoop {m} {st k st' g1} (h : stepF (.binLoop m) st = some (k, st')) (he : effF st.ctx (.binLoop m) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_prim {tl} {st k st' g1} (h : stepF (.prim tl) st = some (k, st')) (he : effF st.ctx (.prim tl) st.g = some g1)
    (hi : SInv st) (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : SInv st' := by
  si_auto

theorem si_rparen {st k st' g1} (h : stepF .rparen st = some (k, st')) (he : effF st.ctx .rparen st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkBin {op} {st k st' g1} (h : stepF (.mkBin op) st = some (k, st')) (he : effF st.ctx (.mkBin op) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_ifCmp {tl} {st k st' g1} (h : stepF (.ifCmp tl) st = some (k, st')) (he : effF st.ctx (.ifCmp tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_ifThen {c tl} {st k st' g1} (h : stepF (.ifThen c tl) st = some (k, st')) (he : effF st.ctx (.ifThen c tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_ifElse {st k st' g1} (h : stepF .ifElse st = some (k, st')) (he : effF st.ctx .ifElse st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkIte {c} {st k st' g1} (h : stepF (.mkIte c) st = some (k, st')) (he : effF st.ctx (.mkIte c) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letSemi {x tl} {st k st' g1} (h : stepF (.letSemi x tl) st = some (k, st')) (he : effF st.ctx (.letSemi x tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letEnd {s d} {st k st' g1} (h : stepF (.letEnd s d) st = some (k, st')) (he : effF st.ctx (.letEnd s d) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_parenClose {st k st' g1} (h : stepF .parenClose st = some (k, st')) (he : effF st.ctx .parenClose st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letStart {tl} {st k st' g1} (h : stepF (.letStart tl) st = some (k, st')) (he : effF st.ctx (.letStart tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkPair {st k st' g1} (h : stepF .mkPair st = some (k, st')) (he : effF st.ctx .mkPair st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_argAtom {st k st' g1} (h : stepF .argAtom st = some (k, st')) (he : effF st.ctx .argAtom st.g = some g1)
    (hi : SInv st) (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : SInv st' := by
  si_auto

theorem si_args {c n} {st k st' g1} (h : stepF (.args c n) st = some (k, st')) (he : effF st.ctx (.args c n) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkCallN {c d} {st k st' g1} (h : stepF (.mkCallN c d) st = some (k, st')) (he : effF st.ctx (.mkCallN c d) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_selfArgs {st k st' g1} (h : stepF .selfArgs st = some (k, st')) (he : effF st.ctx .selfArgs st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_argCheck {c n} {st k st' g1} (h : stepF (.argCheck c n) st = some (k, st')) (he : effF st.ctx (.argCheck c n) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkCall {c n} {st k st' g1} (h : stepF (.mkCall c n) st = some (k, st')) (he : effF st.ctx (.mkCall c n) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto
  exact ⟨hi.2.1 _ (rows_get_lt he.1.2 ‹_›), fun a ha => hi.1 a (List.mem_of_mem_drop ha)⟩

theorem si_shiftNum {op} {st k st' g1} (h : stepF (.shiftNum op) st = some (k, st')) (he : effF st.ctx (.shiftNum op) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letPairX {tl} {st k st' g1} (h : stepF (.letPairX tl) st = some (k, st')) (he : effF st.ctx (.letPairX tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letPairY {x tl} {st k st' g1} (h : stepF (.letPairY x tl) st = some (k, st')) (he : effF st.ctx (.letPairY x tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_stash {x} {st k st' g1} (h : stepF (.stash x) st = some (k, st')) (he : effF st.ctx (.stash x) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_letPairSemi {y tl} {st k st' g1} (h : stepF (.letPairSemi y tl) st = some (k, st')) (he : effF st.ctx (.letPairSemi y tl) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkCont {f n} {st k st' g1} (h : stepF (.mkCont f n) st = some (k, st')) (he : effF st.ctx (.mkCont f n) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  have hv := hi.1
  si_auto
  · exact fun a ha => hv a (List.mem_of_mem_tail ha)
  · exact fun a ha => hv a (List.mem_of_mem_drop ha)

theorem si_argName {st k st' g1} (h : stepF .argName st = some (k, st')) (he : effF st.ctx .argName st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto
  exact hi.2.1 _ (List.mem_of_getElem? ‹_›)

theorem si_defs {st k st' g1} (h : stepF .defs st = some (k, st')) (he : effF st.ctx .defs st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_tyAtom {st k st' g1} (h : stepF .tyAtom st = some (k, st')) (he : effF st.ctx .tyAtom st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_tyCross {st k st' g1} (h : stepF .tyCross st = some (k, st')) (he : effF st.ctx .tyCross st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_tyPair {l} {st k st' g1} (h : stepF (.tyPair l) st = some (k, st')) (he : effF st.ctx (.tyPair l) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_binders {st k st' g1} (h : stepF .binders st = some (k, st')) (he : effF st.ctx .binders st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_group {a} {st k st' g1} (h : stepF (.group a) st = some (k, st')) (he : effF st.ctx (.group a) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_assign {a} {st k st' g1} (h : stepF (.assign a) st = some (k, st')) (he : effF st.ctx (.assign a) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_plainBody {st k st' g1} (h : stepF .plainBody st = some (k, st')) (he : effF st.ctx .plainBody st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_afterColon {st k st' g1} (h : stepF .afterColon st = some (k, st')) (he : effF st.ctx .afterColon st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_stateTy {st k st' g1} (h : stepF .stateTy st = some (k, st')) (he : effF st.ctx .stateTy st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_armsStart {st k st' g1} (h : stepF .armsStart st = some (k, st')) (he : effF st.ctx .armsStart st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_armBind {stp i} {st k st' g1} (h : stepF (.armBind stp i) st = some (k, st')) (he : effF st.ctx (.armBind stp i) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_zeroDone {st k st' g1} (h : stepF .zeroDone st = some (k, st')) (he : effF st.ctx .zeroDone st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_mkLoop {st k st' g1} (h : stepF .mkLoop st = some (k, st')) (he : effF st.ctx .mkLoop st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto
  exact fun a ha => hi.1.2 a (List.mem_of_mem_tail ha)

theorem si_defEnd {st k st' g1} (h : stepF .defEnd st = some (k, st')) (he : effF st.ctx .defEnd st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_flat {nd} {st k st' g1} (h : stepF (.flat nd) st = some (k, st')) (he : effF st.ctx (.flat nd) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_flatL {ns} {st k st' g1} (h : stepF (.flatL ns) st = some (k, st')) (he : effF st.ctx (.flatL ns) st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

theorem si_defClose {st k st' g1} (h : stepF .defClose st = some (k, st')) (he : effF st.ctx .defClose st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto
  rintro d (hd | rfl)
  · exact hi.2 d hd
  · exact he.1

theorem si_tupRest {st k st' g1} (h : stepF .tupRest st = some (k, st')) (he : effF st.ctx .tupRest st.g = some g1)
    (hi : SInv st) : SInv st' := by
  si_auto

end ParRun

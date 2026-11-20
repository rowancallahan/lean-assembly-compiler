/- Nano/V2Self/Proof/Parser/ParRunWFFr: per-frame facts for the preservation of `WF`: the shape of the pushed frames (`ks_*`), the
context is unchanged by non-final frames (`cx_*`), binder shape codes stay set outside binder groups (`bs_*`). -/
import Nano.V2Self.Proof.Parser.ParRunWFInv
namespace ParRun
open ParSpec

/-- what a frame may push -/
def KOK (f : Frame) (k : List Frame) : Prop :=
  finalsLast k = true ∧ (f.final = false → ∀ x ∈ k, x.final = false) ∧ (f.isTy = true → ∀ x ∈ k, x.isTy = true) ∧
  (∀ a, .group a ∈ k → k = [.group a] ∧ f.final = true) ∧
  (∀ a sz, .assign a sz ∈ k → (f = .group a ∧ k = [.tyAtom, .rparen, .assign a sz, .binders]) ∨ (f = .assign (a - 1) sz ∧ 1 ≤ a ∧ k = [.assign a sz]))

set_option hygiene false in
macro "step_norm" : tactic => `(tactic| (
  simp only [stepF] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq,
      mkNode_eq, locOf_eq, and_assoc, exists_and_left, exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right',
      exists_const] at h <;>
    (repeat (obtain ⟨_, h⟩ := h)) <;> (try subst_vars)))

theorem ks_expr {m tl} {st k st'} (h : stepF (.expr m tl) st = some (k, st')) : KOK (.expr m tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_expr {m tl} {st k st'} (h : stepF (.expr m tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_expr {m tl} {st k st'} (h : stepF (.expr m tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_binLoop {m} {st k st'} (h : stepF (.binLoop m) st = some (k, st')) : KOK (.binLoop m) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_binLoop {m} {st k st'} (h : stepF (.binLoop m) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_binLoop {m} {st k st'} (h : stepF (.binLoop m) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_prim {tl} {st k st'} (h : stepF (.prim tl) st = some (k, st')) : KOK (.prim tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_prim {tl} {st k st'} (h : stepF (.prim tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_prim {tl} {st k st'} (h : stepF (.prim tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_rparen {st k st'} (h : stepF .rparen st = some (k, st')) : KOK .rparen k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_rparen {st k st'} (h : stepF .rparen st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bt_rparen {st k st'} (h : stepF .rparen st = some (k, st')) : st'.binds = st.binds := by
  step_norm <;> rfl

theorem ks_mkBin {op} {st k st'} (h : stepF (.mkBin op) st = some (k, st')) : KOK (.mkBin op) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkBin {op} {st k st'} (h : stepF (.mkBin op) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkBin {op} {st k st'} (h : stepF (.mkBin op) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_ifCmp {tl} {st k st'} (h : stepF (.ifCmp tl) st = some (k, st')) : KOK (.ifCmp tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_ifCmp {tl} {st k st'} (h : stepF (.ifCmp tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_ifCmp {tl} {st k st'} (h : stepF (.ifCmp tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_ifThen {c tl} {st k st'} (h : stepF (.ifThen c tl) st = some (k, st')) : KOK (.ifThen c tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_ifThen {c tl} {st k st'} (h : stepF (.ifThen c tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_ifThen {c tl} {st k st'} (h : stepF (.ifThen c tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_ifElse {st k st'} (h : stepF .ifElse st = some (k, st')) : KOK .ifElse k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_ifElse {st k st'} (h : stepF .ifElse st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_ifElse {st k st'} (h : stepF .ifElse st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_mkIte {c} {st k st'} (h : stepF (.mkIte c) st = some (k, st')) : KOK (.mkIte c) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkIte {c} {st k st'} (h : stepF (.mkIte c) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkIte {c} {st k st'} (h : stepF (.mkIte c) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_letSemi {x tl} {st k st'} (h : stepF (.letSemi x tl) st = some (k, st')) : KOK (.letSemi x tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letSemi {x tl} {st k st'} (h : stepF (.letSemi x tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letSemi {x tl} {st k st'} (h : stepF (.letSemi x tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))
  all_goals (intro bd hbd; (try simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbd); rcases hbd with hbd | rfl | rfl <;> first | exact hb _ hbd | simp [hi.1.1] | simp)

theorem ks_letEnd {s d} {st k st'} (h : stepF (.letEnd s d) st = some (k, st')) : KOK (.letEnd s d) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letEnd {s d} {st k st'} (h : stepF (.letEnd s d) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letEnd {s d} {st k st'} (h : stepF (.letEnd s d) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_parenClose {st k st'} (h : stepF .parenClose st = some (k, st')) : KOK .parenClose k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_parenClose {st k st'} (h : stepF .parenClose st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_parenClose {st k st'} (h : stepF .parenClose st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_letStart {tl} {st k st'} (h : stepF (.letStart tl) st = some (k, st')) : KOK (.letStart tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letStart {tl} {st k st'} (h : stepF (.letStart tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letStart {tl} {st k st'} (h : stepF (.letStart tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_mkPair {st k st'} (h : stepF .mkPair st = some (k, st')) : KOK .mkPair k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkPair {st k st'} (h : stepF .mkPair st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkPair {st k st'} (h : stepF .mkPair st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_argAtom {st k st'} (h : stepF .argAtom st = some (k, st')) : KOK .argAtom k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_argAtom {st k st'} (h : stepF .argAtom st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_argAtom {st k st'} (h : stepF .argAtom st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_args {c n} {st k st'} (h : stepF (.args c n) st = some (k, st')) : KOK (.args c n) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_args {c n} {st k st'} (h : stepF (.args c n) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_args {c n} {st k st'} (h : stepF (.args c n) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_mkCallN {c d} {st k st'} (h : stepF (.mkCallN c d) st = some (k, st')) : KOK (.mkCallN c d) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkCallN {c d} {st k st'} (h : stepF (.mkCallN c d) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkCallN {c d} {st k st'} (h : stepF (.mkCallN c d) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_selfArgs {st k st'} (h : stepF .selfArgs st = some (k, st')) : KOK .selfArgs k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_selfArgs {st k st'} (h : stepF .selfArgs st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_selfArgs {st k st'} (h : stepF .selfArgs st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_argCheck {c n} {st k st'} (h : stepF (.argCheck c n) st = some (k, st')) : KOK (.argCheck c n) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_argCheck {c n} {st k st'} (h : stepF (.argCheck c n) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_argCheck {c n} {st k st'} (h : stepF (.argCheck c n) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_mkCall {c n} {st k st'} (h : stepF (.mkCall c n) st = some (k, st')) : KOK (.mkCall c n) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkCall {c n} {st k st'} (h : stepF (.mkCall c n) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkCall {c n} {st k st'} (h : stepF (.mkCall c n) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_shiftNum {op} {st k st'} (h : stepF (.shiftNum op) st = some (k, st')) : KOK (.shiftNum op) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_shiftNum {op} {st k st'} (h : stepF (.shiftNum op) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_shiftNum {op} {st k st'} (h : stepF (.shiftNum op) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_letPairX {tl} {st k st'} (h : stepF (.letPairX tl) st = some (k, st')) : KOK (.letPairX tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letPairX {tl} {st k st'} (h : stepF (.letPairX tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letPairX {tl} {st k st'} (h : stepF (.letPairX tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_letPairY {x tl} {st k st'} (h : stepF (.letPairY x tl) st = some (k, st')) : KOK (.letPairY x tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letPairY {x tl} {st k st'} (h : stepF (.letPairY x tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letPairY {x tl} {st k st'} (h : stepF (.letPairY x tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_stash {x} {st k st'} (h : stepF (.stash x) st = some (k, st')) : KOK (.stash x) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_stash {x} {st k st'} (h : stepF (.stash x) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_stash {x} {st k st'} (h : stepF (.stash x) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_letPairSemi {y tl} {st k st'} (h : stepF (.letPairSemi y tl) st = some (k, st')) : KOK (.letPairSemi y tl) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_letPairSemi {y tl} {st k st'} (h : stepF (.letPairSemi y tl) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_letPairSemi {y tl} {st k st'} (h : stepF (.letPairSemi y tl) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))
  all_goals (intro bd hbd; (try simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbd); rcases hbd with hbd | rfl | rfl <;> first | exact hb _ hbd | simp [hi.1.1] | simp)

theorem ks_mkCont {f n} {st k st'} (h : stepF (.mkCont f n) st = some (k, st')) : KOK (.mkCont f n) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkCont {f n} {st k st'} (h : stepF (.mkCont f n) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkCont {f n} {st k st'} (h : stepF (.mkCont f n) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_argName {st k st'} (h : stepF .argName st = some (k, st')) : KOK .argName k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_argName {st k st'} (h : stepF .argName st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_argName {st k st'} (h : stepF .argName st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_defs {st k st'} (h : stepF .defs st = some (k, st')) : KOK .defs k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_defs {st k st'} (h : stepF .defs st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_tyAtom {st k st'} (h : stepF .tyAtom st = some (k, st')) : KOK .tyAtom k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_tyAtom {st k st'} (h : stepF .tyAtom st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bt_tyAtom {st k st'} (h : stepF .tyAtom st = some (k, st')) : st'.binds = st.binds := by
  step_norm <;> rfl

theorem ks_tyCross {st k st'} (h : stepF .tyCross st = some (k, st')) : KOK .tyCross k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_tyCross {st k st'} (h : stepF .tyCross st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bt_tyCross {st k st'} (h : stepF .tyCross st = some (k, st')) : st'.binds = st.binds := by
  step_norm <;> rfl

theorem ks_tyPair {l} {st k st'} (h : stepF (.tyPair l) st = some (k, st')) : KOK (.tyPair l) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_tyPair {l} {st k st'} (h : stepF (.tyPair l) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bt_tyPair {l} {st k st'} (h : stepF (.tyPair l) st = some (k, st')) : st'.binds = st.binds := by
  step_norm <;> rfl

theorem ks_binders {st k st'} (h : stepF .binders st = some (k, st')) : KOK .binders k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_binders {st k st'} (h : stepF .binders st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_group {a} {st k st'} (h : stepF (.group a) st = some (k, st')) : KOK (.group a) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem ks_assign {a sz} {st k st'} (h : stepF (.assign a sz) st = some (k, st')) : KOK (.assign a sz) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem ks_plainBody {st k st'} (h : stepF .plainBody st = some (k, st')) : KOK .plainBody k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_plainBody {st k st'} (h : stepF .plainBody st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_afterColon {st k st'} (h : stepF .afterColon st = some (k, st')) : KOK .afterColon k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_afterColon {st k st'} (h : stepF .afterColon st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_stateTy {st k st'} (h : stepF .stateTy st = some (k, st')) : KOK .stateTy k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_stateTy {st k st'} (h : stepF .stateTy st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_armsStart {st k st'} (h : stepF .armsStart st = some (k, st')) : KOK .armsStart k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_armsStart {st k st'} (h : stepF .armsStart st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_armBind {stp i} {st k st'} (h : stepF (.armBind stp i) st = some (k, st')) : KOK (.armBind stp i) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_armBind {stp i} {st k st'} (h : stepF (.armBind stp i) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))
  all_goals (intro bd hbd; (try simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hbd); rcases hbd with hbd | rfl | rfl <;> first | exact hb _ hbd | simp [hi.1.1] | simp)

theorem ks_zeroDone {st k st'} (h : stepF .zeroDone st = some (k, st')) : KOK .zeroDone k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_zeroDone {st k st'} (h : stepF .zeroDone st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_mkLoop {st k st'} (h : stepF .mkLoop st = some (k, st')) : KOK .mkLoop k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_mkLoop {st k st'} (h : stepF .mkLoop st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_mkLoop {st k st'} (h : stepF .mkLoop st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_defEnd {st k st'} (h : stepF .defEnd st = some (k, st')) : KOK .defEnd k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_defEnd {st k st'} (h : stepF .defEnd st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_flat {nd} {st k st'} (h : stepF (.flat nd) st = some (k, st')) : KOK (.flat nd) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_flat {nd} {st k st'} (h : stepF (.flat nd) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_flat {nd} {st k st'} (h : stepF (.flat nd) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_flatL {ns} {st k st'} (h : stepF (.flatL ns) st = some (k, st')) : KOK (.flatL ns) k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_flatL {ns} {st k st'} (h : stepF (.flatL ns) st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_flatL {ns} {st k st'} (h : stepF (.flatL ns) st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_defClose {st k st'} (h : stepF .defClose st = some (k, st')) : KOK .defClose k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem bs_defClose {st k st'} (h : stepF .defClose st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

theorem ks_tupRest {st k st'} (h : stepF .tupRest st = some (k, st')) : KOK .tupRest k := by
  step_norm <;> simp [KOK, finalsLast, Frame.final, Frame.isTy] <;> omega

theorem cx_tupRest {st k st'} (h : stepF .tupRest st = some (k, st')) : st'.ctx = st.ctx := by
  step_norm <;> simp [St.ctx, rows, leaf]

theorem bs_tupRest {st k st'} (h : stepF .tupRest st = some (k, st')) (hi : SInv st)
    (hb : ∀ bd ∈ st.binds, bd.sh.isSome) : ∀ bd ∈ st'.binds, bd.sh.isSome := by
  step_norm <;> simp [SInv, leaf] at hi ⊢ <;> (try simp_all) <;> (try (intro bd hbd; exact hb bd (List.mem_of_mem_take hbd))) <;>
    (try (intro bd hbd; rcases hbd with hbd | hbd | hbd <;> (first | exact hb _ hbd | (subst hbd; simp [hi.1.1]) | (subst hbd; simp))))

end ParRun

/- Nano/V2Self/Proof/ParRunCall: Layer 2, ARGUMENTS and CALLS (task codes 43 argAtom, 44 args, 45 mkCallN, 47 argCheck, 48 mkCall,
55 argName).  Fuel-free facts about runs of these frames (no ParSpec function yet):
* frame inversions (`argAtom_inv`, `argName_inv`, `argCheck_inv`, `mkCall_inv`, `mkNode_inv`);
* `argCheck_run`: `argCheck c k` is a pure check (k + 1 steps, state unchanged, every argument `argOK`);
* `atom_run`: an argument atom is a parenthesised expression (left to the expression induction) or an `AtomLeaf` (numeral, local,
  constant def, `[]`, `bnew`: the non-recursive clauses of `ParSpec.pAtom`), which pushes exactly one leaf node;
* `args_run`: `args c k` = k atom segments in sequence (`Atoms`). -/
import Nano.V2Self.Proof.ParRunStar
namespace ParRun
open ParSpec

/-! ## mkNode -/
theorem mkNode_inv {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat} (h : mkNode st t a b s p n = some st') :
    n ≤ st.vals.length ∧
    st' = { st with vals := RN.mk t a b s p (st.vals.take n).reverse :: st.vals.drop n,
                    arena := st.arena ++ [RN.mk t a b s p (st.vals.take n).reverse] } := by
  unfold mkNode at h
  split at h
  · simp at h; exact ⟨‹_›, h.symm⟩
  · simp at h

/-! ## args (44) / mkCallN (45) -/
theorem args_zero (c : Callee) (st : St) : stepF (.args c 0) st = some ([], st) := by simp [stepF]
theorem args_succ (c : Callee) (k : Nat) (st : St) : stepF (.args c (k + 1)) st = some ([.argAtom, .args c k], st) := by simp [stepF]
theorem mkCallN_eq (c : Callee) (d : Nat) (st : St) :
    stepF (.mkCallN c d) st = some ([.argCheck c (st.vals.length - d), .mkCall c (st.vals.length - d)], st) := by simp [stepF]

/-! ## argCheck (47) -/
/-- operand `k` (0 = top) has the shape of its parameter (a numeral or `len'` may stand for a Nat fuel parameter) -/
def argOK (st : St) (c : Callee) (k : Nat) : Prop :=
  ∃ v w, st.vals[k]? = some v ∧ parCode st c (arity st c - (k + 1)) = some w ∧
    (v.sh = some w ∨ (w = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1))))

theorem argCheck_zero (c : Callee) (st : St) : stepF (.argCheck c 0) st = some ([], st) := by simp [stepF]

theorem argCheck_inv {c : Callee} {k : Nat} {st st' : St} {fr : List Frame} (h : stepF (.argCheck c (k + 1)) st = some (fr, st')) :
    argOK st c k ∧ fr = [.argCheck c k] ∧ st' = st := by
  simp only [stepF] at h
  split at h
  · split at h
    · simp at h; exact ⟨⟨_, _, ‹_›, ‹_›, ‹_›⟩, h.1.symm, h.2.symm⟩
    · simp at h
  · simp at h

/-- the check task: `k + 1` steps, no state change, every one of the top `k` operands matches its parameter -/
theorem argCheck_run {c : Callee} : ∀ (k : Nat) {n : Nat} {ks : List Frame} {st fin : St},
    StarN n (.argCheck c k :: ks, st) ([], fin) → (∀ i, i < k → argOK st c i) ∧ ∃ n', n = n' + k + 1 ∧ StarN n' (ks, st) ([], fin)
  | k, 0, _, _, _, h => absurd h.zero_nil.1 (by simp)
  | 0, n + 1, ks, st, fin, h => by
    obtain ⟨fr, st1, hs, h1⟩ := h.head
    rw [argCheck_zero] at hs; cases hs
    exact ⟨fun i hi => absurd hi (by omega), n, rfl, h1⟩
  | k + 1, n + 1, ks, st, fin, h => by
    obtain ⟨fr, st1, hs, h1⟩ := h.head
    obtain ⟨hok, rfl, rfl⟩ := argCheck_inv hs
    obtain ⟨hall, n', rfl, h2⟩ := argCheck_run k h1
    refine ⟨fun i hi => ?_, n', by omega, h2⟩
    by_cases hik : i = k
    · subst hik; exact hok
    · exact hall i (by omega)

/-! ## mkCall (48) -/
theorem mkCall_inv {c : Callee} {n : Nat} {st st' : St} {fr : List Frame} (h : stepF (.mkCall c n) st = some (fr, st')) :
    fr = [] ∧
    ((∃ j d, c = .df j ∧ (rows st)[j]? = some d ∧ mkNode st 8 j n d.res false n = some st') ∨
     (∃ p, c = .pr p ∧ mkNode st 9 p 0 (some (primRes p)) false n = some st')) := by
  simp only [stepF] at h
  split at h
  · split at h
    · simp at h; obtain ⟨h2, rfl⟩ := h; exact ⟨rfl, Or.inl ⟨_, _, rfl, ‹_›, h2⟩⟩
    · simp at h
  · simp at h; obtain ⟨h2, rfl⟩ := h; exact ⟨rfl, Or.inr ⟨_, rfl, h2⟩⟩

/-! ## atoms (43 / 55) -/
/-- the non-parenthesised argument atoms, clause by clause as `ParSpec.pAtom` -/
inductive AtomLeaf (st : St) : St → Prop
  | num {v r} : st.toks = .num v :: r → AtomLeaf st (leaf { st with toks := r } 1 v 0 .uw)
  | loc {x r bd st1} : st.toks = .id x :: r → findB st.binds x = some bd → locOf { st with toks := r } bd = some st1 → AtomLeaf st st1
  | cst {x r j d st1} : st.toks = .id x :: r → findB st.binds x = none → findD st.defs x = some j → st.defs[j]? = some d →
      d.params.length = 0 → mkNode { st with toks := r } 8 j 0 d.res false 0 = some st1 → AtomLeaf st st1
  | nil {r} : st.toks = .k 30 :: .k 31 :: r → AtomLeaf st (leaf { st with toks := r } 9 5 0 .ls)
  | bnew {r} : st.toks = .k 43 :: r → AtomLeaf st (leaf { st with toks := r } 9 5 0 .bf)

theorem argAtom_inv {st st' : St} {fr : List Frame} (h : stepF .argAtom st = some (fr, st')) :
    (∃ r, st.toks = .k 6 :: r ∧ fr = [.expr 0 false, .parenClose] ∧ st' = { st with toks := r }) ∨
    (∃ v r, st.toks = .num v :: r ∧ fr = [.prim false] ∧ st' = st) ∨
    (∃ x r bd, st.toks = .id x :: r ∧ findB st.binds x = some bd ∧ fr = [] ∧ locOf { st with toks := r } bd = some st') ∨
    (fr = [.argName] ∧ st' = st ∧ ∀ x r, st.toks = .id x :: r → findB st.binds x = none) := by
  simp only [stepF] at h
  split at h
  · simp at h; exact Or.inl ⟨_, ‹_›, h.1.symm, h.2.symm⟩
  · simp at h; exact Or.inr (Or.inl ⟨_, _, ‹_›, h.1.symm, h.2.symm⟩)
  · split at h
    · simp at h; obtain ⟨h2, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, ‹_›, ‹_›, rfl, h2⟩))
    · simp at h
      refine Or.inr (Or.inr (Or.inr ⟨h.1.symm, h.2.symm, fun x r hx => ?_⟩))
      rename_i heq _ hnone
      rw [heq] at hx; cases hx; exact hnone
  · simp at h
    refine Or.inr (Or.inr (Or.inr ⟨h.1.symm, h.2.symm, fun x r hx => ?_⟩))
    rename_i h1 h2 h3
    exact absurd hx (h3 x r)

theorem argName_inv {st st' : St} {fr : List Frame} (h : stepF .argName st = some (fr, st')) :
    fr = [] ∧
    ((∃ x r j d, st.toks = .id x :: r ∧ findD st.defs x = some j ∧ st.defs[j]? = some d ∧ d.params.length = 0 ∧
        mkNode { st with toks := r } 8 j 0 d.res false 0 = some st') ∨
     (∃ r, st.toks = .k 30 :: .k 31 :: r ∧ st' = leaf { st with toks := r } 9 5 0 .ls) ∨
     (∃ r, st.toks = .k 43 :: r ∧ st' = leaf { st with toks := r } 9 5 0 .bf)) := by
  simp only [stepF] at h
  split at h
  · split at h
    · split at h
      · split at h
        · simp at h; obtain ⟨h2, rfl⟩ := h
          exact ⟨rfl, Or.inl ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, h2⟩⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h; exact ⟨h.1, Or.inr (Or.inl ⟨_, ‹_›, h.2.symm⟩)⟩
  · simp at h; exact ⟨h.1, Or.inr (Or.inr ⟨_, ‹_›, h.2.symm⟩)⟩
  · simp at h

theorem prim_num {tl : Bool} {st : St} {v : Nat} {r : List Tok} (h : st.toks = .num v :: r) :
    stepF (.prim tl) st = some ([], leaf { st with toks := r } 1 v 0 .uw) := by
  simp [stepF, h]

/-- an argument atom: a parenthesised expression / tuple, or a leaf -/
theorem atom_run {n : Nat} {ks : List Frame} {st fin : St} (h : StarN n (.argAtom :: ks, st) ([], fin)) :
    (∃ r n', st.toks = .k 6 :: r ∧ n = n' + 1 ∧ StarN n' (.expr 0 false :: .parenClose :: ks, { st with toks := r }) ([], fin)) ∨
    (∃ st1 n', n' < n ∧ AtomLeaf st st1 ∧ StarN n' (ks, st1) ([], fin)) := by
  match n, h with
  | 0, h => exact absurd h.zero_nil.1 (by simp)
  | n + 1, h =>
  obtain ⟨fr, st1, hs, h1⟩ := h.head
  rcases argAtom_inv hs with ⟨r, ht, rfl, rfl⟩ | ⟨v, r, ht, rfl, rfl⟩ | ⟨x, r, bd, ht, hb, rfl, hl⟩ | ⟨rfl, rfl, hnb⟩
  · exact Or.inl ⟨r, n, ht, rfl, h1⟩
  · match n, h1 with
    | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
    | n + 1, h1 =>
    obtain ⟨fr2, st2, hs2, h2⟩ := h1.head
    rw [prim_num ht] at hs2; cases hs2
    exact Or.inr ⟨_, n, by omega, .num ht, h2⟩
  · exact Or.inr ⟨_, n, by omega, .loc ht hb hl, h1⟩
  · match n, h1 with
    | 0, h1 => exact absurd h1.zero_nil.1 (by simp)
    | n + 1, h1 =>
    obtain ⟨fr2, st2, hs2, h2⟩ := h1.head
    obtain ⟨rfl, hc⟩ := argName_inv hs2
    rcases hc with ⟨x, r, j, d, ht, hd, hj, hp, hm⟩ | ⟨r, ht, rfl⟩ | ⟨r, ht, rfl⟩
    · exact Or.inr ⟨_, n, by omega, .cst ht (hnb x r ht) hd hj hp hm, h2⟩
    · exact Or.inr ⟨_, n, by omega, .nil ht, h2⟩
    · exact Or.inr ⟨_, n, by omega, .bnew ht, h2⟩

/-- what a leaf atom changes: tokens consumed, one childless non-pending node pushed (and appended to the arena) -/
theorem AtomLeaf.eff {st st1 : St} (h : AtomLeaf st st1) :
    ∃ r v, r.length < st.toks.length ∧ v.kids = [] ∧ v.pend = false ∧
      st1 = { st with toks := r, vals := v :: st.vals, arena := st.arena ++ [v] } := by
  cases h with
  | num ht => exact ⟨_, _, by simp [ht], rfl, rfl, rfl⟩
  | loc ht hb hl =>
    unfold locOf at hl
    split at hl
    · simp at hl
    · simp at hl; exact ⟨_, _, by simp [ht], rfl, rfl, hl.symm⟩
  | cst ht hb hd hj hp hm =>
    obtain ⟨_, rfl⟩ := mkNode_inv hm
    exact ⟨_, _, by simp [ht], by simp [RN.kids], rfl, rfl⟩
  | nil ht => exact ⟨_, _, by simp [ht]; omega, rfl, rfl, rfl⟩
  | bnew ht => exact ⟨_, _, by simp [ht], rfl, rfl, rfl⟩

/-! ## the argument list -/
/-- `k` argument atoms in sequence; `m` = number of steps -/
inductive Atoms : Nat → St → St → Nat → Prop
  | nil (st) : Atoms 0 st st 0
  | cons {k st st1 st2 n1 n2} : StarN n1 ([.argAtom], st) ([], st1) → Atoms k st1 st2 n2 → Atoms (k + 1) st st2 (n1 + n2)

/-- `args c k` runs `k` atoms (plus `k + 1` bookkeeping steps) and nothing else -/
theorem args_run {c : Callee} : ∀ (k : Nat) {n : Nat} {ks : List Frame} {st fin : St},
    StarN n (.args c k :: ks, st) ([], fin) → ∃ st' m n', Atoms k st st' m ∧ n = m + n' + k + 1 ∧ StarN n' (ks, st') ([], fin)
  | k, 0, _, _, _, h => absurd h.zero_nil.1 (by simp)
  | 0, n + 1, ks, st, fin, h => by
    obtain ⟨fr, st1, hs, h1⟩ := h.head
    rw [args_zero] at hs; cases hs
    exact ⟨st, 0, n, .nil st, by omega, h1⟩
  | k + 1, n + 1, ks, st, fin, h => by
    obtain ⟨fr, st1, hs, h1⟩ := h.head
    rw [args_succ] at hs; cases hs
    have h1' : StarN n ([.argAtom] ++ (.args c k :: ks), st) ([], fin) := h1
    obtain ⟨sta, n1, n2, rfl, ha, hr⟩ := h1'.split
    obtain ⟨st', m, n', hat, rfl, hk⟩ := args_run k hr
    exact ⟨st', n1 + m, n', .cons ha hat, by omega, hk⟩

end ParRun

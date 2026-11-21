/- Nano/Parser/ParRunTy: Layer-2 soundness for TYPES.  A run of `tyAtom :: ks` to the empty stack first parses a ParSpec type
(`pTy`, at every fuel ≥ 2·|toks| + 2) and then runs `ks` with the remaining tokens and `ty = trRes t`; nothing else in the state changes. -/
import Nano.Parser.ParRunStar
namespace ParRun
open ParSpec

/-- no `Nat` inside a pair (Par1 rejects code 4 as a pair component, v10) -/
def _root_.ParSpec.Sh.nnt : Sh → Bool
  | .p a b => a != .nt && b != .nt && a.nnt && b.nnt
  | _ => true

theorem _root_.ParSpec.Sh.hasN_of_nnt {s : Sh} (h : s.nnt = true) (hn : s ≠ .nt) : s.hasN = false := by
  induction s with
  | p a b iha ihb =>
    simp only [Sh.nnt, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨ha, hb⟩, ha'⟩, hb'⟩ := h
    simp [Sh.hasN, iha ha' ha, ihb hb' hb]
  | nt => exact absurd rfl hn
  | _ => rfl

/-- the state after a type: only the tokens and `ty` change -/
def St.withTy (st : St) (r : List Tok) (s : Sh) : St := { st with toks := r, ty := some s }

@[simp] theorem St.withTy_toks (st : St) (r : List Tok) (s : Sh) : (st.withTy r s).toks = r := rfl
@[simp] theorem St.withTy_ty (st : St) (r : List Tok) (s : Sh) : (st.withTy r s).ty = some s := rfl
@[simp] theorem St.withTy_upd (st : St) (r r' : List Tok) (s : Sh) : ({ st with toks := r' } : St).withTy r s = st.withTy r s := rfl
@[simp] theorem St.withTy_withTy (st : St) (r r' : List Tok) (s s' : Sh) : (st.withTy r s).withTy r' s' = st.withTy r' s' := rfl

/-- what `pTy` does after its first atom `a` with rest `r` -/
def crossK (f : Nat) (a : TyR) (r : List Tok) : Option (TyR × List Tok) :=
  match r with
  | .k 16 :: r1 => (pTy f r1).bind fun (b, r2) => some (.sh (.p (trRes a) (trRes b)), r2)
  | _ => some (a, r)

theorem pTy_succ' (f : Nat) (ts : List Tok) : pTy (f + 1) ts = (pTyAtom f ts).bind fun (a, r) => crossK f a r := by
  rw [pTy]; rfl

theorem tyAtom_inv {st k st'} (h : stepF .tyAtom st = some (k, st')) :
    (∃ r, st.toks = .k 6 :: r ∧ k = [.tyAtom, .rparen, .tyCross] ∧ st' = { st with toks := r }) ∨
    (∃ a r, k = [.tyCross] ∧ st' = st.withTy r (trRes a) ∧ r.length < st.toks.length ∧ (∀ f, pTyAtom (f + 1) st.toks = some (a, r)) ∧
      (trRes a).nnt = true) := by
  simp only [stepF] at h
  split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  next => exact Or.inl ⟨_, ‹_›, rfl, rfl⟩
  next => exact Or.inr ⟨.sh .uw, _, rfl, rfl, by simp [*], fun f => by rw [‹st.toks = _›]; simp only [pTyAtom], rfl⟩
  next => exact Or.inr ⟨.sh .bf, _, rfl, rfl, by simp [*], fun f => by rw [‹st.toks = _›]; simp only [pTyAtom], rfl⟩
  next => exact Or.inr ⟨.sh .nt, _, rfl, rfl, by simp [*], fun f => by rw [‹st.toks = _›]; simp only [pTyAtom], rfl⟩
  next => exact Or.inr ⟨.lst, _, rfl, rfl, by simp [*]; omega, fun f => by rw [‹st.toks = _›]; simp only [pTyAtom], rfl⟩

theorem rparen_inv {st k st'} (h : stepF .rparen st = some (k, st')) :
    ∃ r, st.toks = .k 7 :: r ∧ k = [] ∧ st' = { st with toks := r } := by
  simp only [stepF] at h
  split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨_, ‹_›, rfl, rfl⟩

theorem tyCross_inv {st k st'} (h : stepF .tyCross st = some (k, st')) :
    (∃ r l, st.toks = .k 16 :: r ∧ st.ty = some l ∧ k = [.tyAtom, .tyPair l] ∧ st' = { st with toks := r }) ∨
    ((∀ r, st.toks ≠ .k 16 :: r) ∧ k = [] ∧ st' = st) := by
  simp only [stepF] at h
  split at h
  next r heq =>
    split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨_, _, heq, ‹_›, rfl, rfl⟩
  next heq =>
    simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨fun r h => heq r h, rfl, rfl⟩

theorem tyPair_inv {st k st' l} (h : stepF (.tyPair l) st = some (k, st')) :
    ∃ r, st.ty = some r ∧ k = [] ∧ st' = { st with ty := some (.p l r) } ∧ l ≠ .nt ∧ r ≠ .nt := by
  simp only [stepF] at h
  split at h
  · rename_i r hr
    split at h
    · simp at h
    · rename_i hn
      split at h
      · simp at h
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, hr, rfl, rfl, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
  · simp at h

theorem St.withTy_self {st : St} {s : Sh} (h : st.ty = some s) : st.withTy st.toks s = st := by
  cases st; simp_all [St.withTy]

theorem crossK_other {f a r} (h : ∀ r1, r ≠ .k 16 :: r1) : crossK f a r = some (a, r) := by
  unfold crossK; split
  · exact absurd rfl (h _)
  · rfl

theorem ty_sound : ∀ n, (∀ {ks st fin}, StarN n (.tyAtom :: ks, st) ([], fin) →
      ∃ t r n', n' < n ∧ r.length < st.toks.length ∧ (∀ f, 2 * st.toks.length + 2 ≤ f → pTy f st.toks = some (t, r)) ∧
        StarN n' (ks, st.withTy r (trRes t)) ([], fin) ∧ (trRes t).nnt = true) ∧
    (∀ {ks st fin} (a : TyR), st.ty = some (trRes a) → (trRes a).nnt = true → StarN n (.tyCross :: ks, st) ([], fin) →
      ∃ t r n', n' < n ∧ r.length ≤ st.toks.length ∧ (∀ f, 2 * st.toks.length + 1 ≤ f → crossK f a st.toks = some (t, r)) ∧
        StarN n' (ks, st.withTy r (trRes t)) ([], fin) ∧ (trRes t).nnt = true) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  constructor
  · intro ks st fin h
    match n, h with
    | 0, h => exact absurd h.zero_nil.1 (by simp)
    | n + 1, h =>
    obtain ⟨k, st1, hs, h1⟩ := h.head
    rcases tyAtom_inv hs with ⟨r, hts, rfl, rfl⟩ | ⟨a, r, rfl, rfl, hl, hp, hann⟩
    · obtain ⟨t1, r1, n1, hn1, hl1, hp1, h2, hnn1⟩ := (ih n (by omega)).1 (ks := .rparen :: .tyCross :: ks) h1
      simp only [St.withTy_upd] at h2 hl1 hp1
      match n1, h2 with
      | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
      | n2 + 1, h2 =>
      obtain ⟨k3, st3, hs3, h3⟩ := h2.head
      obtain ⟨r2, hr1, rfl, rfl⟩ := rparen_inv hs3
      simp only [St.withTy_toks] at hr1
      subst hr1
      have h3' : StarN n2 (.tyCross :: ks, st.withTy r2 (trRes t1)) ([], fin) := h3
      obtain ⟨t, r', n', hn, hl, hp, hrun, hnn⟩ := (ih n2 (by omega)).2 t1 rfl hnn1 h3'
      simp only [St.withTy_toks, St.withTy_withTy] at hl hp hrun
      simp only [hts, List.length_cons] at hl1 ⊢
      refine ⟨t, r', n', by omega, by omega, ?_, hrun, hnn⟩
      intro f hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      rw [pTy_succ']
      simp only [pTyAtom]
      rw [hp1 g (by omega)]
      simp only [Option.bind_some]
      exact hp (g + 1) (by omega)
    · obtain ⟨t, r', n', hn, hl', hp', hrun, hnn⟩ := (ih n (by omega)).2 (st := st.withTy r (trRes a)) a rfl hann h1
      simp only [St.withTy_toks, St.withTy_withTy] at hl' hp' hrun
      refine ⟨t, r', n', by omega, by omega, ?_, hrun, hnn⟩
      intro f hf
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
      rw [pTy_succ', hp g]
      exact hp' (g + 1) (by omega)
  · intro ks st fin a hty hann h
    match n, h with
    | 0, h => exact absurd h.zero_nil.1 (by simp)
    | n + 1, h =>
    obtain ⟨k, st1, hs, h1⟩ := h.head
    rcases tyCross_inv hs with ⟨r, l, hts, hl, rfl, rfl⟩ | ⟨hne, rfl, hst⟩
    · rw [hty] at hl; cases hl
      obtain ⟨t1, r1, n1, hn1, hl1, hp1, h2, hnn1⟩ := (ih n (by omega)).1 (ks := .tyPair (trRes a) :: ks) h1
      simp only [St.withTy_upd] at h2 hl1 hp1
      match n1, h2 with
      | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
      | n2 + 1, h2 =>
      obtain ⟨k3, st3, hs3, h3⟩ := h2.head
      obtain ⟨r3, hr3, rfl, rfl, hln, hrn⟩ := tyPair_inv hs3
      simp only [St.withTy_ty, Option.some.injEq] at hr3
      subst hr3
      refine ⟨.sh (.p (trRes a) (trRes t1)), r1, n2, by omega, by rw [hts]; simp; omega, ?_, h3,
        by show (Sh.p (trRes a) (trRes t1)).nnt = true
           simp only [Sh.nnt, Bool.and_eq_true, bne_iff_ne, ne_eq]; exact ⟨⟨⟨hln, hrn⟩, hann⟩, hnn1⟩⟩
      intro f hf
      rw [hts] at hf ⊢
      simp at hf
      simp only [crossK]
      rw [hp1 f (by omega)]
      rfl
    · rw [hst] at h1
      refine ⟨a, st.toks, n, by omega, Nat.le_refl _, fun f _ => crossK_other hne, ?_, hann⟩
      rw [St.withTy_self hty]; exact h1

end ParRun

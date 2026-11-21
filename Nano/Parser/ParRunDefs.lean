/- Nano/Parser/ParRunDefs: Layer-2 def level (parser lead), pure.  A run that finishes a def body passes through `.defs`
with the def's header, flattened body and `21` emitted and the row appended (`defEnd_tail`). -/
import Nano.Parser.ParRunFlat
import Nano.Parser.ParRunTy
namespace ParRun
open ParSpec

/-- a counted run to the empty stack can be cut at any intermediate configuration -/
theorem StarN.cut {c d : List Frame × St} {m : Nat} {fin : St} (h1 : Star c d) (h2 : StarN m c ([], fin)) :
    ∃ m', m' ≤ m ∧ StarN m' d ([], fin) := by
  induction h1 generalizing m with
  | refl => exact ⟨m, Nat.le_refl _, h2⟩
  | step hs _ ih =>
    cases h2 with
    | refl => simp [stepS] at hs
    | step hs' h' =>
      rw [hs] at hs'; cases hs'
      obtain ⟨m', hm, h3⟩ := ih h'
      exact ⟨m', by omega, h3⟩

/-- the def header words `defEnd` emits -/
def defHdr (st : St) : List UInt64 :=
  [20, st.defs.length.toUInt64, st.cur.npw.toUInt64, st.nx.toUInt64, (if st.cur.loop then 1 else 0), (cw st.cur.res).toUInt64]

/-- **def tail**: `defEnd` checks the single body value, then the header, the flattened body and `21` are emitted, the row is
appended, and the run continues at `.defs` -/
theorem defEnd_tail {n : Nat} {ks : List Frame} {st fin : St} (h : StarN n (.defEnd :: ks, st) ([], fin)) :
    ∃ z n', n' < n ∧ st.vals = [z] ∧ z.sh = st.cur.res ∧ z.isInp = false ∧ st.nx < 2 ^ 20 ∧ cw st.cur.res < 2 ^ 20 ∧
      Star (.defEnd :: ks, st) (.defs :: ks, { st with out := st.out ++ defHdr st ++ z.words ++ [21], defs := st.defs ++ [st.cur] }) ∧
      StarN n' (.defs :: ks, { st with out := st.out ++ defHdr st ++ z.words ++ [21], defs := st.defs ++ [st.cur] }) ([], fin) := by
  match n, h with
  | n + 1, h =>
    obtain ⟨k, st1, h1, h2⟩ := h.head
    have hs0 := Star.one (fs := ks) h1
    obtain ⟨toks, nx, binds, defs, cur, vals, arena, ty, stash, arm, sslot, out, acc, all⟩ := st
    simp only [stepF] at h1
    match vals, h1 with
    | [z], h1 =>
      simp only at h1
      split at h1
      · rename_i hc
        cases h1
        refine ⟨z, ?_⟩
        have r1 := flat_run z (.defClose :: ks)
          ⟨toks, nx, binds, defs, cur, [z], arena, ty, stash, arm, sslot,
            out ++ defHdr ⟨toks, nx, binds, defs, cur, [z], arena, ty, stash, arm, sslot, out, acc, all⟩, acc, all⟩
        have r2 := Star.one (fs := ks) (f := .defClose) (st := ⟨toks, nx, binds, defs, cur, [z], arena, ty, stash, arm, sslot,
          out ++ defHdr ⟨toks, nx, binds, defs, cur, [z], arena, ty, stash, arm, sslot, out, acc, all⟩ ++ z.words, acc, all⟩)
          (by simp only [stepF]; rfl)
        obtain ⟨m', hm, h3⟩ := StarN.cut (r1.trans r2) h2
        exact ⟨m', by omega, rfl, hc.1, by simpa using hc.2.1, hc.2.2.1, hc.2.2.2, hs0.trans (r1.trans r2), h3⟩
      · cases h1


/-- the spec's type parser never yields `.sh .ls` (a `List UInt8` is `.lst`), so `trRes` loses nothing at the top -/
theorem pTy_noLs : ∀ f, (∀ ts t r, pTyAtom f ts = some (t, r) → t ≠ .sh .ls) ∧ (∀ ts t r, pTy f ts = some (t, r) → t ≠ .sh .ls) := by
  intro f
  induction f with
  | zero => exact ⟨fun ts t r h => by simp [pTyAtom] at h, fun ts t r h => by simp [pTy] at h⟩
  | succ f ih =>
    refine ⟨fun ts t r h => ?_, fun ts t r h => ?_⟩
    · rw [pTyAtom.eq_def] at h
      simp only at h
      split at h
      all_goals first
        | (cases h; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp)
        | (obtain rfl : f = _ := Nat.succ.inj ‹f + 1 = _›
           obtain ⟨⟨t1, r1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
           simp only at h2
           split at h2
           · simp only [Option.some.injEq, Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2; exact ih.2 _ _ _ h1
           · cases h2)
    · rw [pTy_succ'] at h
      obtain ⟨⟨a, r1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      unfold crossK at h2
      simp only at h2
      split at h2
      · obtain ⟨⟨b, r3⟩, _, h4⟩ := Option.bind_eq_some_iff.mp h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4; simp
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2; exact ih.1 _ _ _ h1

theorem trRes_ls {t : TyR} (h : t ≠ .sh .ls) : trRes t = .ls ↔ t = .lst := by
  cases t with
  | lst => simp [trRes]
  | sh s => simp only [trRes]; constructor
            · intro e; subst e; exact absurd rfl h
            · intro e; cases e


/-- B's `ty_sound` with the run prefix: the type run as a `Star` -/
theorem ty_star {n : Nat} {ks : List Frame} {st fin : St} (h : StarN n (.tyAtom :: ks, st) ([], fin)) :
    ∃ t r n', n' < n ∧ r.length < st.toks.length ∧ (∀ f, 2 * st.toks.length + 2 ≤ f → pTy f st.toks = some (t, r)) ∧
      Star (.tyAtom :: ks, st) (ks, st.withTy r (trRes t)) ∧ StarN n' (ks, st.withTy r (trRes t)) ([], fin) ∧
      (trRes t).nnt = true := by
  obtain ⟨st'', n1, n2, hn, e1, e2⟩ := StarN.split (k := [.tyAtom]) (ks := ks) h
  obtain ⟨t, r, n', hn', hl, hp, e3, hnt⟩ := (ty_sound n1).1 e1
  cases e3 with
  | refl => exact ⟨t, r, n2, by omega, hl, hp, by simpa using Star.append ks e1.toStar, e2, hnt⟩
  | step hs _ => simp [stepS] at hs


/-- the first step of a counted run, with its `Star` -/
theorem StarN.head_star {n : Nat} {f : Frame} {fs : List Frame} {st fin : St} (h : StarN (n + 1) (f :: fs, st) ([], fin)) :
    ∃ k st', stepF f st = some (k, st') ∧ Star (f :: fs, st) (k ++ fs, st') ∧ StarN n (k ++ fs, st') ([], fin) := by
  obtain ⟨k, st', h1, h2⟩ := h.head
  exact ⟨k, st', h1, Star.one h1, h2⟩

end ParRun

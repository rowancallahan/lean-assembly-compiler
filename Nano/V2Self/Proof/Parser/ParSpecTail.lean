/- Nano/V2Self/Proof/Parser/ParSpecTail: pure ParSpec facts about the tail flag.  `tl_up`: a parse that succeeds with `tl = false` succeeds
identically with `tl = true` (the flag only ADMITS self-calls).  Used by the Layer-2 refinement for `pBin`'s re-parse and the tuple re-parse. -/
import Nano.V2Self.Proof.Parser.ParSpec
namespace ParSpec

theorem tl_up : ∀ f, (∀ cx ts nx r, pExpr f cx false ts nx = some r → pExpr f cx true ts nx = some r) ∧
    (∀ cx m ts nx r, pBin f cx false m ts nx = some r → pBin f cx true m ts nx = some r) ∧
    (∀ cx ts nx r, pApp f cx false ts nx = some r → pApp f cx true ts nx = some r) ∧
    (∀ cx ts nx r, pAtom f cx false ts nx = some r → pAtom f cx true ts nx = some r) := by
  intro f
  induction f with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [pExpr, pBin, pApp, pAtom]
  | succ f ih =>
    obtain ⟨iE, iB, iP, iA⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cx ts nx r h
      rw [pExpr.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      all_goals (repeat (first
        | (obtain ⟨_, hx, h⟩ := Option.bind_eq_some_iff.mp h
           first | rw [hx] | rw [iE _ _ _ _ hx] | rw [iB _ _ _ _ _ hx] | rw [iP _ _ _ _ hx]
           simp only [Option.bind_some])
        | (obtain ⟨_, hx, rfl⟩ := Option.map_eq_some_iff.mp h
           first | rw [hx] | rw [iE _ _ _ _ hx] | rw [iB _ _ _ _ _ hx]
           rfl)
        | (revert h; split <;> intro h <;> (try (simp at h; done))) ))
    · intro cx m ts nx r h
      rw [pBin.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      all_goals (obtain ⟨_, hx, h⟩ := Option.bind_eq_some_iff.mp h; rw [iP _ _ _ _ hx]; simp only [Option.bind_some]
                 split <;> (try split) <;> first | rfl | exact h)
      all_goals (repeat (first
        | (obtain ⟨_, hx, h⟩ := Option.bind_eq_some_iff.mp h
           first | rw [hx] | rw [iE _ _ _ _ hx] | rw [iB _ _ _ _ _ hx] | rw [iP _ _ _ _ hx]
           simp only [Option.bind_some])
        | (obtain ⟨_, hx, rfl⟩ := Option.map_eq_some_iff.mp h
           first | rw [hx] | rw [iE _ _ _ _ hx] | rw [iB _ _ _ _ _ hx]
           rfl)
        | (revert h; split <;> intro h <;> (try (simp at h; done))) ))
    · intro cx ts nx r h
      rw [pApp.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall]) <;> (try exact iA _ _ _ _ h)
    · intro cx ts nx r h
      rw [pAtom.eq_def] at h ⊢
      split at h <;> (try simp_all [-Prod.forall])
      subst_vars
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      rw [iE _ _ _ _ hx]; simpa using h


/-- a CONTINUE on the tail spine (if branches, let body) -/
def Nd.tailCont : Nd → Bool
  | .cont _ => true
  | .ite _ _ _ t e => t.tailCont || e.tailCont
  | .letE _ _ _ b => b.tailCont
  | _ => false

theorem pLoop_noop {f cx m a ta ts nx res} (hts : ∀ t r', ts = .k t :: r' → opInfo t = none)
    (h : pLoop f cx m a ta ts nx = some res) : res = (a, ta, ts, nx) := by
  cases f with
  | zero => simp [pLoop] at h
  | succ f =>
    rw [pLoop.eq_def] at h
    simp only at h
    split at h
    · rw [hts _ _ rfl] at h; simp at h; exact h.symm
    · simp at h; exact h.symm

theorem tl_down : ∀ f, (∀ cx ts nx r, pExpr f cx true ts nx = some r → r.1.tailCont = false → pExpr f cx false ts nx = some r) ∧
    (∀ cx m ts nx r, pBin f cx true m ts nx = some r → r.1.tailCont = false → pBin f cx false m ts nx = some r) ∧
    (∀ cx ts nx r, pApp f cx true ts nx = some r → r.1.tailCont = false → pApp f cx false ts nx = some r) ∧
    (∀ cx ts nx r, pAtom f cx true ts nx = some r → r.1.tailCont = false → pAtom f cx false ts nx = some r) := by
  intro f
  induction f with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [pExpr, pBin, pApp, pAtom]
  | succ f ih =>
    obtain ⟨iE, iB, iP, iA⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cx ts nx r h hn
      rw [pExpr.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      · obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
        rw [hx]; simp only [Option.bind_some]
        revert h2; split
        · intro h2; obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h2
          simp only [Nd.tailCont] at hn; rw [iE _ _ _ _ hy hn]; rfl
        · intro h2; simp at h2
      · obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
        rw [hx]; simp only [Option.bind_some]
        revert h2; split
        · intro h2; obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h2
          simp only [Nd.tailCont] at hn; rw [iE _ _ _ _ hy hn]; rfl
        · intro h2; simp at h2
      · obtain ⟨a, ha, h2⟩ := Option.bind_eq_some_iff.mp h
        rw [ha]; simp only [Option.bind_some]
        revert h2; split
        · rename_i c r2 _
          split
          · intro h2
            obtain ⟨b, hb, h3⟩ := Option.bind_eq_some_iff.mp h2
            rw [hb]; simp only [Option.bind_some]
            revert h3; split
            · rename_i r4 heq4
              intro h3
              obtain ⟨t, ht, h4⟩ := Option.bind_eq_some_iff.mp h3
              revert h4; split
              · rename_i r6 heq6
                intro h4
                obtain ⟨e, he, h5⟩ := Option.bind_eq_some_iff.mp h4
                obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp h5
                simp only [Nd.tailCont, Bool.or_eq_false_iff] at hn
                rw [iE _ _ _ _ ht hn.1]; simp only [Option.bind_some, heq6]
                rw [iE _ _ _ _ he hn.2]; simp [hty]
              · intro h4; simp at h4
            · intro h3; simp at h3
          · intro h2; simp at h2
        · intro h2; simp at h2
    · intro cx m ts nx r h hn
      rw [pBin.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
      revert h2; split
      · rename_i t tl' heq
        split
        · intro h2; exact h2
        · rename_i hop
          intro h2
          have := pLoop_noop (fun t' r' he => by rw [heq] at he; cases he; simpa using hop) h2
          subst this
          rw [iP _ _ _ _ hx hn]; simpa using h2
      · rename_i hne
        intro h2
        have := pLoop_noop (fun t' r' he => by simp_all) h2
        subst this
        rw [iP _ _ _ _ hx hn]; simpa using h2
    · intro cx ts nx r h hn
      rw [pApp.eq_def] at h ⊢
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · simp at h
      · simp at h; subst h; simp [Nd.tailCont] at hn
    · intro cx ts nx r h hn
      rw [pAtom.eq_def] at h ⊢
      split at h <;> (try simp_all [-Prod.forall])
      subst_vars
      obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
      revert h2; split
      · rename_i r2 heq
        intro h2; simp at h2; subst h2
        rw [iE _ _ _ _ hx hn]; simp [heq]
      · rename_i tl' heq
        intro h2
        obtain ⟨y, hy, h3⟩ := Option.bind_eq_some_iff.mp h2
        have hy' := (tl_up _).1 _ _ _ _ hy
        rw [hx] at hy'; cases hy'
        rw [hy]; simpa [heq] using h3
      · intro h2; simp at h2


theorem join_ne_bot {a b c : Ty} (h : a.join b = some c) (ha : a ≠ .bot) : c ≠ .bot := by
  rintro rfl
  cases a <;> cases b <;> simp_all [Ty.join] <;> (try (split at h <;> simp_all))

theorem pLoop_ne_bot : ∀ f cx m a ta ts nx r, pLoop f cx m a ta ts nx = some r → ta ≠ .bot → r.2.1 ≠ .bot := by
  intro f
  induction f with
  | zero => intros; simp_all [pLoop]
  | succ f ih =>
    intro cx m a ta ts nx r h hta
    rw [pLoop.eq_def] at h
    (repeat' split at h) <;> (try simp_all [-Prod.forall]) <;> (try subst_vars)
    all_goals (first
      | (simpa using hta)
      | (subst h; simpa using hta)
      | (exact ih _ _ _ _ _ _ _ h (by simp))
      | (obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; split at h; exact ih _ _ _ _ _ _ _ h (by simp); simp at h))

theorem pCallDef_ne_bot {f cx n ts nx r} (h : pCallDef f cx n ts nx = some r) : r.2.1 ≠ .bot := by
  cases f with
  | zero => simp [pCallDef] at h
  | succ f =>
    simp only [pCallDef] at h
    split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; simp
    · simp at h

/-- with the tail flag off, no parse has type `bot` (a CONTINUE needs the flag) -/
theorem nobot : ∀ f, (∀ cx ts nx r, pExpr f cx false ts nx = some r → r.2.1 ≠ .bot) ∧
    (∀ cx m ts nx r, pBin f cx false m ts nx = some r → r.2.1 ≠ .bot) ∧
    (∀ cx ts nx r, pApp f cx false ts nx = some r → r.2.1 ≠ .bot) ∧
    (∀ cx ts nx r, pAtom f cx false ts nx = some r → r.2.1 ≠ .bot) := by
  intro f
  induction f with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [pExpr, pBin, pApp, pAtom]
  | succ f ih =>
    obtain ⟨iE, iB, iP, iA⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cx ts nx r h
      rw [pExpr.eq_def] at h
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      all_goals (repeat' (first
        | (split at h <;> (try (simp at h; done)))
        | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
        | (rw [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h)))
      all_goals (try (obtain ⟨_, _, _, _, rfl⟩ := h))
      all_goals (try (obtain ⟨_, _, _, _, _, rfl⟩ := h))
      all_goals (try simp only)
      all_goals (first
        | simp
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact join_ne_bot ‹_› (iE _ _ _ _ ‹_›)
        | exact pCallDef_ne_bot h
        | (subst h; simp))
    · intro cx m ts nx r h
      rw [pBin.eq_def] at h
      simp only at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      exact pLoop_ne_bot _ _ _ _ _ _ _ _ h (iP _ _ _ _ hx)
    · intro cx ts nx r h
      rw [pApp.eq_def] at h
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      all_goals (repeat' (first
        | (split at h <;> (try (simp at h; done)))
        | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
        | (rw [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h)))
      all_goals (try (obtain ⟨_, _, _, _, rfl⟩ := h))
      all_goals (try (obtain ⟨_, _, _, _, _, rfl⟩ := h))
      all_goals (try simp only)
      all_goals (first
        | simp
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact join_ne_bot ‹_› (iE _ _ _ _ ‹_›)
        | exact pCallDef_ne_bot h
        | (subst h; simp))
    · intro cx ts nx r h
      rw [pAtom.eq_def] at h
      (repeat' split at h) <;> (try simp_all [-Prod.forall])
      all_goals (repeat' (first
        | (split at h <;> (try (simp at h; done)))
        | (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
        | (rw [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h)))
      all_goals (try (obtain ⟨_, _, _, _, rfl⟩ := h))
      all_goals (try (obtain ⟨_, _, _, _, _, rfl⟩ := h))
      all_goals (try simp only)
      all_goals (first
        | simp
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact join_ne_bot ‹_› (iE _ _ _ _ ‹_›)
        | exact pCallDef_ne_bot h
        | (subst h; simp))

end ParSpec

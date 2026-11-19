/- Nano/V2Self/Proof/Parser/ParSpecLen: a spec-side typing fact (box G): a parse whose node is `len' x` (`.prim 1 _`) has type Nat.
(Par1's argument check accepts a `len'` node for a fuel parameter by its tag alone.) -/
import Nano.V2Self.Proof.Parser.ParSpecTail
namespace ParSpec

/-- the result is not `len'`, or it is typed Nat -/
def LenTy (r : Nd × Ty × List Tok × Nat) : Prop := ∀ as, r.1 = .prim 1 as → r.2.1 = .s .nt

theorem primSig_one {t : Nat} {ps : List Ps} {rs : Sh} (h : primSig t = some (1, ps, rs)) : rs = .nt := by
  unfold primSig at h
  split at h <;> simp at h
  exact h.2.symm

theorem pLoop_len : ∀ f cx m a ta ts nx r, pLoop f cx m a ta ts nx = some r → LenTy (a, ta, ts, nx) → LenTy r := by
  intro f
  induction f with
  | zero => intros; simp_all [pLoop]
  | succ f ih =>
    intro cx m a ta ts nx r h hta
    rw [pLoop.eq_def] at h
    (repeat' split at h) <;> (try simp_all [-Prod.forall]) <;> (try subst_vars)
    all_goals (first
      | (exact hta)
      | (subst h; exact hta)
      | (exact ih _ _ _ _ _ _ _ h (fun as e => by cases e))
      | (obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; split at h; exact ih _ _ _ _ _ _ _ h (fun as e => by cases e); simp at h))

theorem pCallDef_len {f cx n ts nx r} (h : pCallDef f cx n ts nx = some r) : LenTy r := by
  cases f with
  | zero => simp [pCallDef] at h
  | succ f =>
    simp only [pCallDef] at h
    split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; intro as e; cases e
    · simp at h

/-- with the tail flag off: a parse whose node is `len' …` has type Nat -/
theorem lenTy : ∀ f, (∀ cx ts nx r, pExpr f cx false ts nx = some r → LenTy r) ∧
    (∀ cx m ts nx r, pBin f cx false m ts nx = some r → LenTy r) ∧
    (∀ cx ts nx r, pApp f cx false ts nx = some r → LenTy r) ∧
    (∀ cx ts nx r, pAtom f cx false ts nx = some r → LenTy r) := by
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
        | (intro as e; cases e; done)
        | (intro as e; simp at e; done)
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact pCallDef_len h
        | (have q := iE _ _ _ _ ‹_›; unfold LenTy at q ⊢; exact q)
        | (intro as e; simp only [Nd.prim.injEq] at e; obtain ⟨rfl, _⟩ := e; exact congrArg _ (primSig_one ‹_›))
        | (subst h; intro as e; cases e; done))
    · intro cx m ts nx r h
      rw [pBin.eq_def] at h
      simp only at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      exact pLoop_len _ _ _ _ _ _ _ _ h (iP _ _ _ _ hx)
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
        | (intro as e; cases e; done)
        | (intro as e; simp at e; done)
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact pCallDef_len h
        | (have q := iE _ _ _ _ ‹_›; unfold LenTy at q ⊢; exact q)
        | (intro as e; simp only [Nd.prim.injEq] at e; obtain ⟨rfl, _⟩ := e; exact congrArg _ (primSig_one ‹_›))
        | (subst h; intro as e; cases e; done))
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
        | (intro as e; cases e; done)
        | (intro as e; simp at e; done)
        | exact iE _ _ _ _ ‹_› | exact iB _ _ _ _ _ ‹_› | exact iP _ _ _ _ ‹_› | exact iA _ _ _ _ ‹_›
        | exact iE _ _ _ _ h | exact iB _ _ _ _ _ h | exact iP _ _ _ _ h | exact iA _ _ _ _ h
        | exact pCallDef_len h
        | (have q := iE _ _ _ _ ‹_›; unfold LenTy at q ⊢; exact q)
        | (intro as e; simp only [Nd.prim.injEq] at e; obtain ⟨rfl, _⟩ := e; exact congrArg _ (primSig_one ‹_›))
        | (subst h; intro as e; cases e; done))

end ParSpec

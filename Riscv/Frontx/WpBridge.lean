/- Paged arrays (NOTES section 30), part 15: programs of the word-array front end (`Pg.Good`, `wa_compile`) run on the
paged back end.

`Pg.goodE_of_good`: a program without `push` and `extract` whose `Array.replicate` sizes are constants of at most
`P * P` elements satisfies `Pg.GoodE` (the meaning with page events) wherever it satisfies `Pg.Good`: the conditions
`E.ok` / `A.ok` / `T.ok` imply the paged ones (`A.ok` is false for `push`), and every `Runs` has events. -/
import Riscv.Frontx.WpProg

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc

theorem A.okP_of_ok {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ), a.ok v → a.okP v
  | .var _, _, _ => trivial
  | .set a i x, v, h => ⟨A.okP_of_ok a v h.1, h.2⟩
  | .push _ _, _, h => h.elim
  | .ite c a b, v, h => by
    refine ⟨h.1, ?_⟩
    have := h.2
    split at this
    · rw [if_pos ‹_›]; exact A.okP_of_ok a v this
    · rw [if_neg ‹_›]; exact A.okP_of_ok b v this

theorem Args.okP_of_ok {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (v : Vals Γ), as.ok v → as.okP v
  | _, .nil, _, _ => trivial
  | _, @Args.cons _ (.sc _) _ e as, v, h => ⟨h.1, Args.okP_of_ok as v h.2⟩
  | _, @Args.cons _ (.ar _) _ a as, v, h => ⟨A.okP_of_ok a v h.1, Args.okP_of_ok as v h.2⟩

theorem T.okP_of_ok {Γ Δ : List Sl} {R : Sl} : ∀ (b : T Γ Δ R) (v : Vals Γ), b.ok v → b.okP v
  | .ret (R := .sc _) _, _, h => h
  | .ret (R := .ar _) _, _, _ => trivial
  | .call as, v, h => by simp only [T.ok] at h; simp only [T.okP]; exact Args.okP_of_ok as v h
  | .ite c a b, v, h => by
    simp only [T.ok] at h; simp only [T.okP]
    refine ⟨h.1, ?_⟩
    have := h.2
    split at this
    · rw [if_pos ‹_›]; exact T.okP_of_ok a v this
    · rw [if_neg ‹_›]; exact T.okP_of_ok b v this
  | .let_ e k, v, h => by simp only [T.ok] at h; simp only [T.okP]; exact ⟨h.1, T.okP_of_ok k _ h.2⟩

theorem Runs.toE {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    (h : Runs b c s r) : ∃ E, RunsE b c s r E := by
  induction h with
  | ret ho => exact ⟨[], .ret ho⟩
  | call ho _ ih => obtain ⟨E, hE⟩ := ih; exact ⟨_, .call ho hE⟩

/-- the fresh arrays the paged back end takes from a word-array program: no `extract`, constant `replicate` sizes -/
def F.PlainP {Γ : List Sl} : {k : AK} → F Γ k → Prop
  | _, .rep n _ => ∃ c, n.natVal = some c ∧ c ≤ P * P
  | _, .extract _ _ _ => False
  | _, _ => True

def Inis.PlainP {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Prop
  | _, .nil => True
  | _, @Inis.cons _ (.sc _) _ _ xs => xs.PlainP
  | _, @Inis.cons _ (.ar _) _ f xs => F.PlainP f ∧ xs.PlainP

def Pg.PlainP : {Γ : List Sl} → {R : Sl} → Pg Γ R → Prop
  | _, _, .ret _ => True
  | _, _, @Pg.let_ _ _ (.sc _) _ k => k.PlainP
  | _, _, @Pg.let_ _ _ (.ar _) f k => F.PlainP f ∧ k.PlainP
  | _, _, .loop _ _ init k => init.PlainP ∧ k.PlainP

theorem Ini.okP_of_ok {Γ : List Sl} (s : Sl) (x : Ini Γ s) (v : Vals Γ) (hp : match s, x with
    | .sc _, _ => True | .ar _, f => F.PlainP f) (h : Ini.ok s x v) : Ini.okP s x v := by
  cases s with
  | sc t => exact h
  | ar k =>
    cases x with
    | rep n x =>
      obtain ⟨c, hc, hle⟩ := hp
      exact ⟨h.1, h.2, by rw [E.natVal_den v n c hc]; exact hle⟩
    | const c => trivial
    | empty => trivial
    | extract m lo hi => exact hp.elim
    | data m => trivial
    | alias m => trivial

theorem Inis.okP_of_ok {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (v : Vals Γ), xs.PlainP → xs.ok v → xs.okP v
  | _, .nil, _, _, _ => trivial
  | _, @Inis.cons _ (.sc _) _ x xs, v, hp, h => ⟨Ini.okP_of_ok (.sc _) x v trivial h.1, Inis.okP_of_ok xs v hp h.2⟩
  | _, @Inis.cons _ (.ar _) _ f xs, v, hp, h => ⟨Ini.okP_of_ok (.ar _) f v hp.1 h.1, Inis.okP_of_ok xs v hp.2 h.2⟩

/-- **A word-array program meets the paged meaning** -/
theorem Pg.goodE_of_good : ∀ {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List PLoc) (d : Nat) (v : Vals Γ) (y : R.T),
    p.PlainP → p.Good v y → ∃ E, p.GoodE L d v y E
  | _, .sc _, .ret e, L, d, v, y, _, h => ⟨[], h.1, h.2, rfl⟩
  | _, .ar _, .ret a, L, d, v, y, _, h => ⟨[], h, rfl⟩
  | _, _, @Pg.let_ _ _ (.sc _) x k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE]
    obtain ⟨E2, hE2⟩ := Pg.goodE_of_good k (Ini.locP L (.sc _) x d :: L) (d + 2) _ y hp h.2
    exact ⟨_, Ini.okP_of_ok (.sc _) x v trivial h.1, E2, hE2, rfl⟩
  | _, _, @Pg.let_ _ _ (.ar _) x k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE]
    obtain ⟨E2, hE2⟩ := Pg.goodE_of_good k (Ini.locP L (.ar _) x d :: L) (d + 2) _ y hp.2 h.2
    exact ⟨_, Ini.okP_of_ok (.ar _) x v hp.1 h.1, E2, hE2, rfl⟩
  | _, _, .loop Δ b init k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE]
    obtain ⟨hi, r, P', h0, hok, hstep, hruns, hk⟩ := h
    obtain ⟨Eb, hEb⟩ := hruns.toE
    obtain ⟨Ek, hEk⟩ := Pg.goodE_of_good k
      (resLocP _ (d + 2 * Δ.length) ((b.rlP (init.locP L d ++ L) (d + 2 * Δ.length + 2)).getD default) :: L)
      (d + 2 * Δ.length + 2) _ y hp.2 hk
    exact ⟨_, Inis.okP_of_ok init v hp.1 hi, r, P', Eb, Ek, h0, fun s hs => T.okP_of_ok b _ (hok s hs), hstep, hEb,
      hEk, rfl⟩

end Proven.WA

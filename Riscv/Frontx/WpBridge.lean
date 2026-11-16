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

/-- no `push` (so no page events) -/
def A.PushFree {Γ : List Sl} {k : AK} : A Γ k → Prop
  | .var _ => True
  | .set a _ _ => a.PushFree
  | .push _ _ => False
  | .ite _ a b => a.PushFree ∧ b.PushFree

def Args.PushFree {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Prop
  | _, .nil => True
  | _, @Args.cons _ (.sc _) _ _ as => as.PushFree
  | _, @Args.cons _ (.ar _) _ a as => a.PushFree ∧ as.PushFree

def T.PushFree {Γ Δ : List Sl} {R : Sl} : T Γ Δ R → Prop
  | .ret _ => True
  | .call as => as.PushFree
  | .ite _ a b => a.PushFree ∧ b.PushFree
  | .let_ _ k => k.PushFree

theorem A.evs_nil {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ), a.PushFree → a.evs v = []
  | .var _, _, _ => rfl
  | .set a _ _, v, h => A.evs_nil a v h
  | .push _ _, _, h => h.elim
  | .ite c a b, v, h => by
    simp only [A.evs]; split
    · exact A.evs_nil a v h.1
    · exact A.evs_nil b v h.2

theorem Args.evs_nil {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (v : Vals Γ), as.PushFree → as.evs v = []
  | _, .nil, _, _ => rfl
  | _, @Args.cons _ (.sc _) _ _ as, v, h => by simp only [Args.evs]; exact Args.evs_nil as v h
  | _, @Args.cons _ (.ar _) _ a as, v, h => by
    simp only [Args.evs, A.evs_nil a v h.1, Args.evs_nil as v h.2]; rfl

theorem T.evs_nil {Γ Δ : List Sl} {R : Sl} : ∀ (b : T Γ Δ R) (v : Vals Γ), b.PushFree → b.evs v = []
  | .ret _, _, _ => rfl
  | .call as, v, h => by simp only [T.evs]; exact Args.evs_nil as v h
  | .ite c a b, v, h => by
    simp only [T.evs]; split
    · exact T.evs_nil a v h.1
    · exact T.evs_nil b v h.2
  | .let_ e k, v, h => by simp only [T.evs]; exact T.evs_nil k _ h

theorem RunsE.nil {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T} {E : List MemEvent}
    (hb : b.PushFree) (h : RunsE b c s r E) : E = [] := by
  induction h with
  | ret ho => rfl
  | call ho _ ih => rw [T.evs_nil b _ hb, ih]; rfl

/-- the fresh arrays the paged back end takes from a word-array program: no `extract`, constant `replicate` sizes,
views of the input only -/
def F.PlainP (L : List PLoc) {Γ : List Sl} : {k : AK} → F Γ k → Prop
  | _, .rep n _ => ∃ c, n.natVal = some c ∧ c ≤ P * P
  | _, .extract _ _ _ => False
  | _, .data m => (m.locP L).inp = true
  | _, .alias m => (m.locP L).inp = true
  | _, _ => True

/-- the page events of such an array -/
def F.evsC {Γ : List Sl} : {k : AK} → F Γ k → List MemEvent
  | _, .rep n _ => .alloc 1 :: pushEvs (n.natVal.getD 0)
  | _, .empty => [.alloc 1]
  | _, _ => []

def Inis.PlainP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Prop
  | _, .nil => True
  | _, @Inis.cons _ (.sc _) _ _ xs => xs.PlainP L
  | _, @Inis.cons _ (.ar _) _ f xs => F.PlainP L f ∧ xs.PlainP L

def Inis.evsC {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → List MemEvent
  | _, .nil => []
  | _, @Inis.cons _ (.sc _) _ _ xs => xs.evsC
  | _, @Inis.cons _ (.ar _) _ f xs => f.evsC ++ xs.evsC

/-- a program the paged back end runs with the events of its fresh arrays only -/
def Pg.PlainP : {Γ : List Sl} → {R : Sl} → Pg Γ R → List PLoc → Nat → Prop
  | _, _, .ret _, _, _ => True
  | _, _, @Pg.let_ _ _ (.sc _) x k, L, d => k.PlainP (Ini.locP L (.sc _) x d :: L) (d + 2)
  | _, _, @Pg.let_ _ _ (.ar _) f k, L, d => F.PlainP L f ∧ k.PlainP (Ini.locP L (.ar _) f d :: L) (d + 2)
  | _, _, @Pg.loop _ _ s Δ b init k, L, d => init.PlainP L ∧ b.PushFree ∧
    k.PlainP (resLocP s (d + 2 * Δ.length) ((b.rlP (init.locP L d ++ L) (d + 2 * Δ.length + 2)).getD rlNone) :: L)
      (d + 2 * Δ.length + 2)

def Pg.evsC : {Γ : List Sl} → {R : Sl} → Pg Γ R → List PLoc → Nat → List MemEvent
  | _, _, .ret _, _, _ => []
  | _, _, @Pg.let_ _ _ (.sc _) x k, L, d => k.evsC (Ini.locP L (.sc _) x d :: L) (d + 2)
  | _, _, @Pg.let_ _ _ (.ar _) f k, L, d => f.evsC ++ k.evsC (Ini.locP L (.ar _) f d :: L) (d + 2)
  | _, _, @Pg.loop _ _ s Δ b init k, L, d => init.evsC ++
    k.evsC (resLocP s (d + 2 * Δ.length) ((b.rlP (init.locP L d ++ L) (d + 2 * Δ.length + 2)).getD rlNone) :: L)
      (d + 2 * Δ.length + 2)

theorem Ini.okP_of_ok {Γ : List Sl} (L : List PLoc) (s : Sl) (x : Ini Γ s) (v : Vals Γ) (hp : match s, x with
    | .sc _, _ => True | .ar _, f => F.PlainP L f) (h : Ini.ok s x v) : Ini.okP s x v ∧ Ini.evsP L s x v = (match s, x with
    | .sc _, _ => [] | .ar _, f => F.evsC f) := by
  cases s with
  | sc t => exact ⟨h, rfl⟩
  | ar k =>
    cases x with
    | rep n x =>
      obtain ⟨c, hc, hle⟩ := hp
      refine ⟨⟨h.1, h.2, by rw [E.natVal_den v n c hc]; exact hle⟩, ?_⟩
      simp only [Ini.evsP, F.evsP, F.evsC, hc, E.natVal_den v n c hc, Option.getD_some]
    | const c => exact ⟨trivial, rfl⟩
    | empty => exact ⟨trivial, rfl⟩
    | extract m lo hi => exact hp.elim
    | data m =>
      have hp' : (m.locP L).inp = true := hp
      exact ⟨trivial, by simp only [Ini.evsP, F.evsP, if_pos hp']; rfl⟩
    | alias m =>
      have hp' : (m.locP L).inp = true := hp
      exact ⟨trivial, by simp only [Ini.evsP, F.evsP, if_pos hp']; rfl⟩

theorem Inis.okP_of_ok {Γ : List Sl} (L : List PLoc) : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (v : Vals Γ), xs.PlainP L →
    xs.ok v → xs.okP v ∧ xs.evsP L v = xs.evsC
  | _, .nil, _, _, _ => ⟨trivial, rfl⟩
  | _, @Inis.cons _ (.sc _) _ x xs, v, hp, h => by
    obtain ⟨a, b⟩ := Ini.okP_of_ok L (.sc _) x v trivial h.1
    obtain ⟨c, d⟩ := Inis.okP_of_ok L xs v hp h.2
    refine ⟨⟨a, c⟩, ?_⟩
    simp only [Inis.evsP, Inis.evsC, b, d]; rfl
  | _, @Inis.cons _ (.ar _) _ f xs, v, hp, h => by
    obtain ⟨a, b⟩ := Ini.okP_of_ok L (.ar _) f v hp.1 h.1
    obtain ⟨c, d⟩ := Inis.okP_of_ok L xs v hp.2 h.2
    refine ⟨⟨a, c⟩, ?_⟩
    simp only [Inis.evsP, Inis.evsC, b, d]

/-- **A word-array program meets the paged meaning**, with the events of its fresh arrays -/
theorem Pg.goodE_of_good : ∀ {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List PLoc) (d : Nat) (v : Vals Γ) (y : R.T),
    p.PlainP L d → p.Good v y → p.GoodE L d v y (p.evsC L d)
  | _, .sc _, .ret e, L, d, v, y, _, h => ⟨h.1, h.2, rfl⟩
  | _, .ar _, .ret a, L, d, v, y, _, h => ⟨h, rfl⟩
  | _, _, @Pg.let_ _ _ (.sc _) x k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE, Pg.evsC]
    obtain ⟨a, b⟩ := Ini.okP_of_ok L (.sc _) x v trivial h.1
    exact ⟨a, _, Pg.goodE_of_good k _ _ _ y hp h.2, by rw [b]; rfl⟩
  | _, _, @Pg.let_ _ _ (.ar _) x k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE, Pg.evsC]
    obtain ⟨a, b⟩ := Ini.okP_of_ok L (.ar _) x v hp.1 h.1
    exact ⟨a, _, Pg.goodE_of_good k _ _ _ y hp.2 h.2, by rw [b]⟩
  | _, _, .loop Δ b init k, L, d, v, y, hp, h => by
    simp only [Pg.Good] at h; simp only [Pg.PlainP] at hp; simp only [Pg.GoodE, Pg.evsC]
    obtain ⟨hi, r, P', h0, hok, hstep, hruns, hk⟩ := h
    obtain ⟨Eb, hEb⟩ := hruns.toE
    have hEb0 := hEb.nil hp.2.1
    subst hEb0
    obtain ⟨a, hev⟩ := Inis.okP_of_ok L init v hp.1 hi
    exact ⟨a, r, P', [], _, h0, fun s hs => T.okP_of_ok b _ (hok s hs), hstep, hEb,
      Pg.goodE_of_good k _ _ _ y hp.2.2 hk, by rw [hev]; simp⟩

end Proven.WA

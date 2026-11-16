/- Paged arrays (NOTES section 35): the page events of a run, computed (`Pg.evRun`, with fuel), and the proof that
they are the events of every `GoodE` run (`Pg.evRun_of_goodE`), so the memory a compiled program needs on an input
(`PgProg.events`, `memoryNeeded`) can be evaluated: `memoryNeeded_eval`. -/
import Riscv.Frontx.PgTop

namespace Proven.WA
open Proven Proven.WP Proven.Top Proven.Top.Alloc

/-- iterating a loop body with fuel: the result and the events -/
def runEv {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) : Nat → Vals Δ → Option (R.T × List MemEvent)
  | 0, _ => none
  | n + 1, s => match b.out (Vals.app s c) with
    | .inr r => some (r, [])
    | .inl s' => (runEv b c n s').map fun q => (q.1, b.evs (Vals.app s c) ++ q.2)

/-- a program's result and events, with fuel for its loops -/
def Pg.evRun : {Γ : List Sl} → {R : Sl} → Pg Γ R → List PLoc → Nat → Nat → Vals Γ → Option (R.T × List MemEvent)
  | _, R, .ret r, _, _, _, v => some (Arg.den R r v, [])
  | _, _, .let_ (s := s) x k, L, d, n, v =>
    (k.evRun (Ini.locP L s x d :: L) (d + 2) n (Ini.den s x v, v)).map fun q => (q.1, Ini.evsP L s x v ++ q.2)
  | _, _, .loop (s := s) Δ b init k, L, d, n, v =>
    let st := init.locP L d
    let res := d + 2 * Δ.length
    let rl := (b.rlP (st ++ L) (res + 2)).getD rlNone
    match runEv b v n (init.den v) with
    | none => none
    | some (r, Eb) => (k.evRun (resLocP s res rl :: L) (res + 2) n (r, v)).map fun q =>
      (q.1, init.evsP L v ++ (Eb ++ q.2))

theorem runEv_mono {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) :
    ∀ n s x, runEv b c n s = some x → runEv b c (n + 1) s = some x
  | 0, _, _, h => nomatch h
  | n + 1, s, x, h => by
    unfold runEv at h ⊢
    split at h
    · exact h
    · next s' ho =>
      cases hr : runEv b c n s' with
      | none => rw [hr] at h; exact nomatch h
      | some q => rw [hr] at h; rw [runEv_mono b c n s' q hr]; exact h

theorem runEv_of_runsE {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    {E : List MemEvent} (h : RunsE b c s r E) : ∃ n, runEv b c n s = some (r, E) := by
  induction h with
  | ret ho => exact ⟨1, by simp only [runEv, ho]⟩
  | call ho _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [runEv, ho, hn, Option.map_some]⟩

theorem runEv_le {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) {n m : Nat} (hnm : n ≤ m) {s x}
    (h : runEv b c n s = some x) : runEv b c m s = some x := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact runEv_mono b c _ _ _ ih

theorem Pg.evRun_mono {Γ : List Sl} {R : Sl} (p : Pg Γ R) : ∀ (L : List PLoc) (d n : Nat) (v : Vals Γ) x,
    p.evRun L d n v = some x → p.evRun L d (n + 1) v = some x := by
  induction p with
  | ret r => intro L d n v x h; exact h
  | let_ x k ih =>
    intro L d n v y h
    simp only [Pg.evRun] at h ⊢
    cases hk : k.evRun _ _ n _ with
    | none => rw [hk] at h; exact nomatch h
    | some q => rw [hk] at h; rw [ih _ _ _ _ _ hk]; exact h
  | loop Δ b init k ih =>
    intro L d n v y h
    simp only [Pg.evRun] at h ⊢
    split at h
    · exact nomatch h
    · next r Eb hr =>
      rw [runEv_mono b v n _ _ hr]
      simp only
      cases hk : k.evRun _ _ n (r, v) with
      | none => rw [hk] at h; exact nomatch h
      | some q => rw [hk] at h; rw [ih _ _ _ _ _ hk]; exact h

theorem Pg.evRun_le {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List PLoc) (d : Nat) (v : Vals Γ) {n m : Nat}
    (hnm : n ≤ m) {x} (h : p.evRun L d n v = some x) : p.evRun L d m v = some x := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Pg.evRun_mono p _ _ _ _ _ ih

/-- **the computed events are those of the run** -/
theorem Pg.evRun_of_goodE {Γ : List Sl} {R : Sl} (p : Pg Γ R) : ∀ (L : List PLoc) (d : Nat) (v : Vals Γ) (y : R.T)
    (E : List MemEvent), p.GoodE L d v y E → ∃ n, p.evRun L d n v = some (y, E) := by
  induction p with
  | ret r =>
    intro L d v y E h
    rename_i R
    cases R
    · exact ⟨0, by rw [h.1, h.2.2]; rfl⟩
    · exact ⟨0, by rw [h.1, h.2]; rfl⟩
  | let_ x k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, E2, h2, rfl⟩ := h <;>
      obtain ⟨n, hn⟩ := ih _ _ _ _ _ h2 <;> exact ⟨n, by simp only [Pg.evRun, hn, Option.map_some]⟩
  | loop Δ b init k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, r, P, Eb, Ek, -, -, -, hr, hk, rfl⟩ := h <;>
      obtain ⟨n1, h1⟩ := runEv_of_runsE hr <;> obtain ⟨n2, h2⟩ := ih _ _ _ _ _ hk <;>
      exact ⟨max n1 n2, by
        simp only [Pg.evRun, runEv_le b v (Nat.le_max_left n1 n2) h1,
          Pg.evRun_le k _ _ _ (Nat.le_max_right n1 n2) h2, Option.map_some]⟩

/-- **`memoryNeeded` evaluated**: for an input the program accepts, the events computed with enough fuel give the
memory the compiled code needs: `8192 * (pk 0 E + 1)` -/
theorem memoryNeeded_eval {q : PgProg} (hg : q.Good) {input : List UInt8} (hs : input.length ≤ q.maxIn)
    {n : Nat} {y : q.R.T} {E : List MemEvent} (he : q.p.evRun [inLocP] 9 n (inArr input, ()) = some (y, E)) :
    memoryNeeded ⟨Proven.Top.wordBytes q.code, 8192, q.events⟩ input = 8192 * (pk 0 E + 1) := by
  have hsz : (inArr input).size ≤ q.maxIn := by simpa [inArr, ByteArray.size] using hs
  have hge := PgProg.res_spec (PgProg.good_total hg) (inArr input) hsz
  rw [inArr_toList] at hge
  obtain ⟨m, hm⟩ := Pg.evRun_of_goodE _ _ _ _ _ _ hge
  have h1 := Pg.evRun_le _ _ _ _ (Nat.le_max_left n m) he
  have h2 := Pg.evRun_le _ _ _ _ (Nat.le_max_right n m) hm
  rw [h1] at h2
  obtain ⟨-, hE⟩ := Prod.mk.inj (Option.some.inj h2)
  show 8192 * peak ((q.evs input).reverse ++ [.alloc 1]) = _
  rw [peak_pages _ (hE ▸ q.evs_allocs _), hE]

end Proven.WA

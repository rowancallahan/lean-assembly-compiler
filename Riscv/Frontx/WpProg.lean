/- Paged dynamic arrays (NOTES section 30), part 9: programs.

A program's stages (`let`, loops) in order; each stage after the first runs only while no page request has
failed (`guard`: variable 8 holds a copy of `vOk`).  A stage's arrays are fresh pages from the pool; arrays a
stage leaves behind (`X`) stay in use.  `Pg.compP_ok`: the code ends with the result (`ResP`) and the page events
(`Pg.GoodE`) within `C` pages, or with `vOk = 0` exactly when the events exceed `C` pages. -/
import Riscv.Frontx.WpPg

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB)

/-! ## Helpers -/

theorem pageCount_append (a b : List (Nat × W64)) : pageCount (a ++ b) = pageCount a + pageCount b := by
  simp [pageCount]

theorem pageCount_perm {a b : List (Nat × W64)} (h : a.Perm b) : pageCount a = pageCount b := by
  unfold pageCount; exact (h.map _).sum_nat

theorem arrsP_cons1 {s : Sl} {Γ : List Sl} {l : PLoc} {L : List PLoc} {x : s.T} {v : Vals Γ} {env : Mach.BEnv} :
    arrsP (s :: Γ) (l :: L) (x, v) env = arrsP [s] [l] (x, ()) env ++ arrsP Γ L v env := by
  cases s with
  | sc t => rfl
  | ar k => simp only [arrsP, List.headD_cons, List.tail_cons]; split <;> rfl

/-- permutations of appended lists, by counting -/
macro "perm_tac" : tactic => `(tactic| (rw [List.perm_iff_count]; intro a; simp only [List.count_append]; omega))

/-- the guard of a later stage: run `S` only while no page request has failed -/
def guard (S : MS) : MS := .seq (.assign 8 (.var vOk)) (when 8 S)

theorem guard_false {S : MS} {σ : MSt} (h : σ.env vOk = 0) :
    Mach.BExec (guard S) σ ⟨σ.env.set 8 0, σ.heap, σ.wheap⟩ := by
  have h1 : Mach.BExec (.assign 8 (.var vOk)) σ ⟨σ.env.set 8 0, σ.heap, σ.wheap⟩ := by
    have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := σ)
    simp only [Mach.BExp.denote, h] at this; exact this
  exact .seq h1 (when_false (by simp only [set_eq]))

theorem guard_true {S : MS} {σ σ₁ : MSt} (h : σ.env vOk = 1) (hS : Mach.BExec S ⟨σ.env.set 8 1, σ.heap, σ.wheap⟩ σ₁) :
    Mach.BExec (guard S) σ ⟨σ₁.env.set 8 0, σ₁.heap, σ₁.wheap⟩ := by
  have h1 : Mach.BExec (.assign 8 (.var vOk)) σ ⟨σ.env.set 8 1, σ.heap, σ.wheap⟩ := by
    have := Mach.BExec.assign (v := 8) (e := .var vOk) (σ := σ)
    simp only [Mach.BExp.denote, h] at this; exact this
  exact .seq h1 (when_true (by simp only [set_eq]; decide) hS)

/-- the slots of a program's scope: none of the pool's, none the guard -/
def SlotOK (L : List PLoc) : Prop := ∀ l ∈ L, NP l.v ∧ NP l.pt ∧ l.v ≠ 8 ∧ l.pt ≠ 8

/-- the outcome of a new slot `l` (value `x`) after a stage that started with arrays `X` (`u` pages) -/
def SOut (C : Nat) (s : Sl) (l : PLoc) (x : s.T) (X : List (Nat × W64)) (u : Nat) (E : List MemEvent) (σ' : MSt)
    (W' : W64) : Prop :=
  (σ'.env vOk = 1 ∧ SRP σ' s l x ∧ Store C σ'.env W' (arrsP [s] [l] (x, ()) σ'.env ++ X) ∧
      finE u E = pageCount (arrsP [s] [l] (x, ()) σ'.env ++ X) ∧ pk u E ≤ C) ∨
    (σ'.env vOk = 0 ∧ C < pk u E)

/-! ## Stage values -/

def Ini.compP (L : List PLoc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Nat → MS
  | .sc _, e, d => E.compP L e d
  | .ar _, f, d => F.compP L f d

def Ini.locP (L : List PLoc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Nat → PLoc
  | .sc _, _, d => ⟨d, false, 0⟩
  | .ar _, f, d => F.locP L f d

def Ini.wfP (L : List PLoc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Bool
  | .sc _, e => E.wfP L e
  | .ar _, f => F.wfP L f

def Ini.okP {Γ : List Sl} : (s : Sl) → Ini Γ s → Vals Γ → Prop
  | .sc _, e, v => E.ok e v
  | .ar _, f, v => F.okP f v

def Ini.evsP (L : List PLoc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Vals Γ → List MemEvent
  | .sc _, _, _ => []
  | .ar _, f, v => F.evsP L f v

theorem Ini.locP_cases (L : List PLoc) {Γ : List Sl} (s : Sl) (x : Ini Γ s) (d : Nat) :
    Ini.locP L s x d = ⟨d, false, 0⟩ ∨ Ini.locP L s x d = ⟨d, true, 0⟩ ∨ Ini.locP L s x d = ⟨d, false, d + 1⟩ := by
  cases s with
  | sc t => simp [Ini.locP]
  | ar k =>
    simp only [Ini.locP]
    cases x <;> simp only [F.locP] <;> (try split) <;> simp

theorem Ini.locP_lt (L : List PLoc) {Γ : List Sl} (s : Sl) (x : Ini Γ s) (d : Nat) :
    (Ini.locP L s x d).v = d ∧ (Ini.locP L s x d).pt < d + 2 ∧ ((Ini.locP L s x d).pt = 0 ∨ d ≤ (Ini.locP L s x d).pt) := by
  rcases Ini.locP_cases L s x d with h | h | h <;> rw [h] <;> simp

theorem Ini.locP_np (L : List PLoc) {Γ : List Sl} (s : Sl) (x : Ini Γ s) (d : Nat) (hd : 9 ≤ d) :
    NP (Ini.locP L s x d).v ∧ NP (Ini.locP L s x d).pt ∧ (Ini.locP L s x d).v ≠ 8 ∧ (Ini.locP L s x d).pt ≠ 8 := by
  rcases Ini.locP_cases L s x d with h | h | h <;> rw [h] <;> simp only [NP, vFh, vBump, vOk] <;> omega

set_option maxHeartbeats 4000000 in
theorem Ini.compP_ok (L : List PLoc) {Γ : List Sl} (C : Nat) (s : Sl) (x : Ini Γ s) (v : Vals Γ) (env : Mach.BEnv)
    (H : Heap) (W : W64) (d : Nat) (X : List (Nat × W64)) (hE : EnvOK Γ L v ⟨env, H, [W]⟩) (hb : BelowP L d)
    (hd : 8 ≤ d) (hLnp : ∀ l ∈ L, NP l.v ∧ NP l.pt) (hS : Store C env W (X ++ arrsP Γ L v env)) (hok1 : env vOk = 1)
    (hwf : Ini.wfP L s x = true) (hok : Ini.okP s x v) :
    ∃ σ' W', Mach.BExec (Ini.compP L s x d) ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧
      (∀ j, j < d → NP j → σ'.env j = env j) ∧
      SOut C s (Ini.locP L s x d) (Ini.den s x v) (X ++ arrsP Γ L v env) (pageCount (X ++ arrsP Γ L v env))
        (Ini.evsP L s x v) σ' W' := by
  cases s with
  | ar k => exact F.compP_ok L C x v env H W d X hE hb hd hLnp hS hok1 hwf hok
  | sc t =>
    simp only [Ini.compP, Ini.locP, Ini.evsP, Ini.den, Ini.wfP, Ini.okP] at hwf hok ⊢
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.compP_ok L x v ⟨env, H, [W]⟩ d hE hE.len hb hwf hok
    refine ⟨σ1, W, e1, h1, w1, fun j hj _ => k1 j hj, .inl ⟨?_, v1, ?_, ?_, hS.count_le⟩⟩
    · rw [k1 _ (by simp only [vOk]; omega)]; exact hok1
    · exact hS.env fun j hj => k1 j (by have := pool_vars hj; omega)
    · rfl

/-! ## Loop starts: slot `j` in variables `d + 2 j` (size or value) and `d + 2 j + 1` (page table) -/

def Inis.compP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Nat → MS
  | _, .nil, d => skipAt d
  | _, .cons (s := s) x xs, d => .seq (Ini.compP L s x d) (guard (xs.compP L (d + 2)))

def Inis.locP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Nat → List PLoc
  | _, .nil, _ => []
  | _, .cons (s := s) x xs, d => Ini.locP L s x d :: xs.locP L (d + 2)

def Inis.wfP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Bool
  | _, .nil => true
  | _, .cons (s := s) x xs => Ini.wfP L s x && xs.wfP L

def Inis.okP {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Vals Γ → Prop
  | _, .nil, _ => True
  | _, .cons (s := s) x xs, v => Ini.okP s x v ∧ xs.okP v

def Inis.evsP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Vals Γ → List MemEvent
  | _, .nil, _ => []
  | _, .cons (s := s) x xs, v => Ini.evsP L s x v ++ xs.evsP L v

theorem Inis.locP_length (L : List PLoc) {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (d : Nat),
    (xs.locP L d).length = Δ.length
  | _, .nil, _ => rfl
  | _, .cons _ xs, d => by simp only [Inis.locP, List.length_cons]; rw [Inis.locP_length L xs]

theorem Inis.locP_in (L : List PLoc) {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (d : Nat), ∀ l ∈ xs.locP L d,
    d ≤ l.v ∧ l.v < d + 2 * Δ.length ∧ l.pt < d + 2 * Δ.length ∧ (l.pt = 0 ∨ d ≤ l.pt)
  | _, .nil, _, _, h => by simp [Inis.locP] at h
  | _, .cons (s := s) x xs, d, l, h => by
    simp only [Inis.locP, List.mem_cons] at h
    rcases h with rfl | h
    · have := Ini.locP_lt L s x d
      simp only [List.length_cons]; omega
    · have := Inis.locP_in L xs (d + 2) l h
      simp only [List.length_cons]; omega

set_option maxHeartbeats 8000000 in
/-- **Loop starts**: the slots hold the start values (in fresh pages), or a page request failed -/
theorem Inis.compP_ok (L : List PLoc) {Γ : List Sl} (C : Nat) : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (v : Vals Γ)
    (env : Mach.BEnv) (H : Heap) (W : W64) (d : Nat) (X : List (Nat × W64)), EnvOK Γ L v ⟨env, H, [W]⟩ →
    BelowP L d → 9 ≤ d → SlotOK L → Store C env W (arrsP Γ L v env ++ X) → env vOk = 1 → xs.wfP L = true →
    xs.okP v →
    ∃ σ' W', Mach.BExec (xs.compP L d) ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧
      (∀ j, j < d → NP j → j ≠ 8 → σ'.env j = env j) ∧
      ((σ'.env vOk = 1 ∧ RelP Δ (xs.locP L d) (xs.den v) σ' ∧
          Store C σ'.env W' (arrsP Δ (xs.locP L d) (xs.den v) σ'.env ++ (arrsP Γ L v env ++ X)) ∧
          finE (pageCount (arrsP Γ L v env ++ X)) (xs.evsP L v) =
            pageCount (arrsP Δ (xs.locP L d) (xs.den v) σ'.env ++ (arrsP Γ L v env ++ X)) ∧
          pk (pageCount (arrsP Γ L v env ++ X)) (xs.evsP L v) ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount (arrsP Γ L v env ++ X)) (xs.evsP L v)))
  | _, .nil, v, env, H, W, d, X, hE, hb, hd, hL, hS, hok1, hwf, hok => by
    simp only [Inis.compP, Inis.locP, Inis.evsP, Inis.den]
    refine ⟨_, W, .assign, rfl, rfl, fun j hj _ _ => set_ne (by omega), .inl ⟨?_, trivial, ?_, by simp [arrsP, finE],
      by simp only [pk]; exact hS.count_le⟩⟩
    · simp only [Mach.BExp.denote, set_ne (show vOk ≠ d by simp only [vOk]; omega)]; exact hok1
    · simp only [arrsP, List.nil_append]; exact hS.env fun j hj => set_ne (by have := pool_vars hj; omega)
  | _, .cons (s := s) x xs, v, env, H, W, d, X, hE, hb, hd, hL, hS, hok1, hwf, hok => by
    simp only [Inis.wfP, Bool.and_eq_true] at hwf; simp only [Inis.okP] at hok
    simp only [Inis.compP, Inis.locP, Inis.evsP, Inis.den]
    have hLnp : ∀ l ∈ L, NP l.v ∧ NP l.pt := fun l h => ⟨(hL l h).1, (hL l h).2.1⟩
    have hS0 : Store C env W (X ++ arrsP Γ L v env) := hS.perm List.perm_append_comm
    obtain ⟨σ1, W1, e1, h1, w1, k1, o1⟩ := Ini.compP_ok L C s x v env H W d X hE hb (by omega) hLnp hS0 hok1
      hwf.1 hok.1
    have hu : pageCount (X ++ arrsP Γ L v env) = pageCount (arrsP Γ L v env ++ X) :=
      pageCount_perm List.perm_append_comm
    rw [hu] at o1
    have hlt := Ini.locP_lt L s x d
    have hnp := Ini.locP_np L s x d hd
    generalize hl0 : Ini.locP L s x d = l0 at hlt hnp o1
    have hpt1 : ∀ l ∈ L, σ1.env l.pt = env l.pt := fun l h => k1 _ (hb l h).2 (hL l h).2.1
    have hR1 : arrsP Γ L v σ1.env = arrsP Γ L v env := arrsP_congr hpt1 hE.len
    rcases o1 with ⟨ok1, sr1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    · -- the first slot holds its value: the rest runs
      obtain ⟨env1, H1, Ws1⟩ := σ1
      simp only at h1 w1 ok1 S1 fin1 k1 hR1 hpt1; subst H1 Ws1
      let env2 := env1.set 8 1
      have hk2 : ∀ j, j < d → NP j → j ≠ 8 → env2 j = env j := fun j hj hn h8 => by
        simp only [env2, set_ne h8]; exact k1 j hj hn
      have hE2 : EnvOK Γ L v ⟨env2, H, [W1]⟩ := by
        refine ⟨hE.rel.frame (fun l h => hk2 _ (hb l h).1 (hL l h).1 (hL l h).2.2.1) rfl hE.len, hE.len, W1, rfl,
          S1.1.wlen.2, ?_⟩
        unfold AllAt; rw [arrsP_congr (fun l h => hk2 _ (hb l h).2 (hL l h).2.1 (hL l h).2.2.2) hE.len]
        intro a ha; exact S1.2 a (by simp [ha])
      let X1 := arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ X
      have harr2 : arrsP Γ L v env2 = arrsP Γ L v env :=
        arrsP_congr (fun l h => hk2 _ (hb l h).2 (hL l h).2.1 (hL l h).2.2.2) hE.len
      have h0' : arrsP [s] [l0] (Ini.den s x v, ()) env2 = arrsP [s] [l0] (Ini.den s x v, ()) env1 := by
        apply arrsP_congr _ (by simp)
        intro l h; simp only [List.mem_singleton] at h; subst h
        simp only [env2, set_ne hnp.2.2.2]
      have hS2 : Store C env2 W1 (arrsP Γ L v env2 ++ X1) := by
        have := S1.env (env' := env2) fun j hj => by simp only [env2, set_ne (show j ≠ 8 by have := pool_vars hj; omega)]
        refine this.perm ?_
        rw [harr2]; simp only [X1]; perm_tac
      obtain ⟨σ3, W3, e3, h3, w3, k3, o3⟩ := Inis.compP_ok L C xs v env2 H W1 (d + 2) X1 hE2 (hb.mono (by omega))
        (by omega) hL hS2 (by simp only [env2, set_ne (show vOk ≠ 8 by decide)]; exact ok1) hwf.2 hok.2
      have e2 := guard_true (S := xs.compP L (d + 2)) (σ := ⟨env1, H, [W1]⟩) ok1 e3
      refine ⟨_, W3, .seq e1 e2, by simp [h3], by simp [w3], fun j hj hn h8 => ?_, ?_⟩
      · simp only [set_ne h8]; rw [k3 j (by omega) hn h8, hk2 j hj hn h8]
      have hsl : ∀ j, j = l0.v ∨ j = l0.pt → j < d + 2 ∧ NP j ∧ j ≠ 8 := fun j hj => by
        rcases hj with rfl | rfl
        · exact ⟨by omega, hnp.1, hnp.2.2.1⟩
        · exact ⟨hlt.2.1, hnp.2.1, hnp.2.2.2⟩
      have hkeep : ∀ j, j = l0.v ∨ j = l0.pt → (σ3.env.set 8 0) j = env1 j := fun j hj => by
        obtain ⟨a, b, c⟩ := hsl j hj
        simp only [set_ne c]; rw [k3 j a b c]; simp only [env2, set_ne c]
      have hfin : arrsP [s] [l0] (Ini.den s x v, ()) (σ3.env.set 8 0) = arrsP [s] [l0] (Ini.den s x v, ()) env1 :=
        arrsP_congr (fun l h => by simp only [List.mem_singleton] at h; subst h; exact hkeep _ (.inr rfl)) (by simp)
      have hfin2 : ∀ {Δ' : List Sl} (sv : Vals Δ'), arrsP (s :: Δ') (l0 :: xs.locP L (d + 2)) (Ini.den s x v, sv) (σ3.env.set 8 0) =
          arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ arrsP Δ' (xs.locP L (d + 2)) sv (σ3.env.set 8 0) := fun sv => by
        rw [arrsP_cons1, hfin]
      have hperm : ∀ (A : List (Nat × W64)), (A ++ (arrsP Γ L v env2 ++ X1)).Perm
          (arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ A ++ (arrsP Γ L v env ++ X)) := fun A => by
        rw [harr2]; simp only [X1]; perm_tac
      have hst3 : arrsP _ (xs.locP L (d + 2)) (xs.den v) (σ3.env.set 8 0) = arrsP _ (xs.locP L (d + 2)) (xs.den v) σ3.env :=
        arrsP_congr (fun l h => by
          have := Inis.locP_in L xs (d + 2) l h
          simp only [set_ne (show l.pt ≠ 8 by omega)]) (by rw [Inis.locP_length]; exact Nat.le_refl _)
      rcases o3 with ⟨ok3, rel3, S3, fin3, pk3⟩ | ⟨ok3, pk3⟩
      · have hpc : pageCount (arrsP Γ L v env2 ++ X1) = pageCount (arrsP [s] [l0] (Ini.den s x v, ()) env1 ++
            (arrsP Γ L v env ++ X)) := by
          have := pageCount_perm (hperm []); simpa using this
        refine .inl ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok3, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
        · exact sr1.frame (hkeep _ (.inl rfl)) h3
        · exact rel3.frameL (fun l h => by
            have := Inis.locP_in L xs (d + 2) l h
            simp only [set_ne (show l.v ≠ 8 by omega)]) rfl (by rw [Inis.locP_length]; exact Nat.le_refl _)
        · rw [hfin2]
          refine (S3.env fun j hj => by simp only [set_ne (show j ≠ 8 by have := pool_vars hj; omega)]).perm ?_
          rw [hst3, harr2]; simp only [X1]; perm_tac
        · rw [finE_append, fin1, show pageCount (arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ (X ++ arrsP Γ L v env)) =
            pageCount (arrsP Γ L v env2 ++ X1) from pageCount_perm (by rw [harr2]; simp only [X1]; perm_tac), fin3,
            hfin2, hst3]
          exact pageCount_perm (by rw [harr2]; simp only [X1]; perm_tac)
        · rw [pk_append, fin1, show pageCount (arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ (X ++ arrsP Γ L v env)) =
            pageCount (arrsP Γ L v env2 ++ X1) from pageCount_perm (by rw [harr2]; simp only [X1]; perm_tac)]
          exact Nat.max_le.2 ⟨pk1, pk3⟩
      · refine .inr ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok3, ?_⟩
        rw [pk_append, fin1, show pageCount (arrsP [s] [l0] (Ini.den s x v, ()) env1 ++ (X ++ arrsP Γ L v env)) =
            pageCount (arrsP Γ L v env2 ++ X1) from pageCount_perm (by rw [harr2]; simp only [X1]; perm_tac)]
        exact Nat.lt_of_lt_of_le pk3 (Nat.le_max_right _ _)
    · -- the first slot found no page: the rest is skipped
      have e2 := guard_false (S := xs.compP L (d + 2)) ok1
      refine ⟨_, W1, .seq e1 e2, h1, w1, fun j hj hn h8 => ?_, .inr ⟨?_, ?_⟩⟩
      · simp only [set_ne h8]; exact k1 j hj hn
      · simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok1
      · exact Nat.lt_of_lt_of_le pk1 (pk_mono_left _ _ _)

end Proven.WA

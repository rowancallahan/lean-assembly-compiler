/- Paged dynamic arrays (NOTES section 30), part 9: programs.

A program's stages (`let`, loops) in order; each stage after the first runs only while no page request has
failed (`guard`: variable 8 holds a copy of `vOk`).  A stage's arrays are fresh pages from the pool; arrays a
stage leaves behind (`X`) stay in use.  `Pg.compP_ok`: the code ends with the result (`ResP`) and the page events
(`Pg.GoodE`) within `C` pages, or with `vOk = 0` exactly when the events exceed `C` pages. -/
import Legacy.Riscv.Frontx.WpPg

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
  | ar k => simp only [arrsP, List.headD_cons, List.tail_cons]; by_cases hi : l.inp = true <;> simp [hi]

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
  | .sc _, _, d => ⟨d, false, d + 1⟩
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
    Ini.locP L s x d = ⟨d, false, 0⟩ ∨ Ini.locP L s x d = ⟨d, true, d + 1⟩ ∨ Ini.locP L s x d = ⟨d, false, d + 1⟩ := by
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

/-! ## Programs -/

instance (j : Nat) : Decidable (NP j) := by unfold NP; infer_instance

/-- where an array result of a loop body lives (the first `ret` leaf) -/
def T.rlP : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List PLoc → Nat → Option PLoc
  | _, _, .ar _, .ret a, L, _ => match a with | .var m => some (m.locP L) | _ => none
  | _, _, .sc _, .ret _, _, _ => none
  | _, _, _, .call _, _, _ => none
  | _, _, _, .ite _ a b, L, d => match a.rlP L (d + 2) with | some l => some l | none => b.rlP L (d + 2)
  | _, _, _, .let_ _ k, L, d => k.rlP (⟨d, false, 0⟩ :: L) (d + 1)

/-- the result location of a loop body without an array result (a scalar loop): read-only, so `LoopC` asks
nothing of it -/
def rlNone : PLoc := ⟨0, true, 0⟩

/-- the result location of a loop: `res` for a scalar, the array's slot otherwise -/
def resLocP : (s : Sl) → Nat → PLoc → PLoc
  | .sc _, res, _ => ⟨res, false, 0⟩
  | .ar _, _, rl => rl

/-- the work slot of a loop's state (a dummy without one) -/
def wP (Δ : List Sl) (st : List PLoc) (res fl : Nat) : PLoc := (workLocs Δ st).headD ⟨res, false, fl⟩

/-- the layout facts of a loop, as one decidable statement -/
abbrev LayC (st : List PLoc) (res fl : Nat) (rl w : PLoc) (d : Nat) : Prop :=
  (∀ l ∈ st, l.v < d ∧ l.pt < d) ∧ res < d ∧ fl < d ∧ (rl.v < d ∧ rl.pt < d) ∧ (vsOfP st).Nodup ∧
    res ∉ vsOfP st ∧ fl ∉ vsOfP st ∧ res ≠ fl ∧ rl.v ≠ fl ∧ (8 ≤ res ∧ 8 ≤ fl ∧ ∀ l ∈ st, 8 ≤ l.v ∧ 8 ≤ l.pt) ∧
    (∀ l ∈ st, l.pt ∉ vsOfP st ∧ l.pt ≠ res ∧ l.pt ≠ fl) ∧ (8 ≤ w.v ∧ 8 ≤ w.pt ∧ w.v ≠ w.pt ∧ w.v < d ∧ w.pt < d)

instance (st : List PLoc) (res fl : Nat) (rl w : PLoc) (d : Nat) : Decidable (LayC st res fl rl w d) := by
  unfold LayC; infer_instance

theorem LayC.lay {st : List PLoc} {res fl : Nat} {rl w : PLoc} {d : Nat} (h : LayC st res fl rl w d) :
    LoopLayP st res fl rl w d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- what a loop stage needs of its locations (all checked by the compiler) -/
abbrev LoopC (Δ : List Sl) (st L : List PLoc) (res fl : Nat) (s : Sl) (rl w : PLoc) (d : Nat) : Prop :=
  LayC st res fl rl w d ∧
    (∀ l ∈ L, (l.v ∉ vsOfP st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ NP l.v) ∧ (l.pt ∉ vsOfP st ∧ l.pt ≠ res ∧ l.pt ≠ fl ∧ NP l.pt)) ∧
    (workLocs Δ st = [w] ∨ workLocs Δ st = []) ∧ (∀ l ∈ st ++ L, l.v = w.v → l = w) ∧
    (rl.inp = false → rl = w ∧ workLocs Δ st = [w]) ∧
    (8 ∉ vsOfP st ∧ 8 ≠ res ∧ 8 ≠ fl ∧ ∀ l ∈ st, l.pt ≠ 8) ∧
    (NP (resLocP s res rl).v ∧ NP (resLocP s res rl).pt ∧ (resLocP s res rl).v ≠ 8 ∧ (resLocP s res rl).pt ≠ 8)

instance (Δ : List Sl) (st L : List PLoc) (res fl : Nat) (s : Sl) (rl w : PLoc) (d : Nat) :
    Decidable (LoopC Δ st L res fl s rl w d) := by
  unfold LoopC; infer_instance

def Pg.compP {Γ : List Sl} : {R : Sl} → Pg Γ R → List PLoc → Nat → MS × PLoc
  | .sc _, .ret e, L, d => (E.compP L e d, ⟨d, false, 0⟩)
  | .ar _, .ret a, L, d => (skipAt d, match a with | .var m => m.locP L | _ => default)
  | _, .let_ (s := s) x k, L, d =>
    (.seq (Ini.compP L s x d) (guard (k.compP (Ini.locP L s x d :: L) (d + 2)).1),
      (k.compP (Ini.locP L s x d :: L) (d + 2)).2)
  | _, .loop (s := s) Δ b init k, L, d =>
    let st := init.locP L d
    let res := d + 2 * Δ.length
    let rl := (b.rlP (st ++ L) (res + 2)).getD rlNone
    (.seq (init.compP L d) (guard (.seq (b.loopP st res (res + 1) (st ++ L) (res + 2))
      (guard (k.compP (resLocP s res rl :: L) (res + 2)).1))), (k.compP (resLocP s res rl :: L) (res + 2)).2)

def Pg.wfP {Γ : List Sl} : {R : Sl} → Pg Γ R → List PLoc → Nat → Bool
  | .sc _, .ret e, L, _ => E.wfP L e
  | .ar _, .ret a, _, _ => match a with | .var _ => true | _ => false
  | _, .let_ (s := s) x k, L, d => Ini.wfP L s x && k.wfP (Ini.locP L s x d :: L) (d + 2)
  | _, .loop (s := s) Δ b init k, L, d =>
    let st := init.locP L d
    let res := d + 2 * Δ.length
    let rl := (b.rlP (st ++ L) (res + 2)).getD rlNone
    let w := wP Δ st res (res + 1)
    init.wfP L && b.wfP st rl w (st ++ L) (res + 2) && decide (LoopC Δ st L res (res + 1) s rl w (res + 2)) &&
      k.wfP (resLocP s res rl :: L) (res + 2)

/-- **the meaning with page events** (oldest first): `Pg.Good` and the events of the run -/
def Pg.GoodE {Γ : List Sl} : {R : Sl} → Pg Γ R → List PLoc → Nat → Vals Γ → R.T → List MemEvent → Prop
  | .sc _, .ret e, _, _, v, y, Ev => y = E.den e v ∧ E.ok e v ∧ Ev = []
  | .ar _, .ret a, _, _, v, y, Ev => y = A.den a v ∧ Ev = []
  | _, .let_ (s := s) x k, L, d, v, y, Ev => Ini.okP s x v ∧ ∃ E2,
      k.GoodE (Ini.locP L s x d :: L) (d + 2) (Ini.den s x v, v) y E2 ∧ Ev = Ini.evsP L s x v ++ E2
  | _, .loop (s := s) Δ b init k, L, d, v, y, Ev =>
    let st := init.locP L d
    let res := d + 2 * Δ.length
    let rl := (b.rlP (st ++ L) (res + 2)).getD rlNone
    init.okP v ∧ ∃ r, ∃ P : Vals Δ → Prop, ∃ Eb Ek, P (init.den v) ∧
      (∀ s, P s → b.okP (Vals.app s v)) ∧ (∀ s s', P s → b.out (Vals.app s v) = .inl s' → P s') ∧
      RunsE b v (init.den v) r Eb ∧ k.GoodE (resLocP s res rl :: L) (res + 2) (r, v) y Ek ∧
      Ev = init.evsP L v ++ (Eb ++ Ek)

/-- the result: a scalar in its variable, an array (size variable, its pages) -/
def ResP (σ : MSt) (W : W64) : (R : Sl) → PLoc → R.T → Prop
  | .sc t, l, y => σ.env l.v = t.rep y
  | .ar k, l, y => SRP σ (.ar k) l y ∧ (l.inp = false → ArrAt W (σ.env l.pt).toNat (words k y))

theorem ResP.frame {σ σ' : MSt} {W : W64} {R : Sl} {l : PLoc} {y : R.T} (h : ResP σ W R l y)
    (hv : σ'.env l.v = σ.env l.v) (hp : σ'.env l.pt = σ.env l.pt) (hh : σ'.heap = σ.heap) : ResP σ' W R l y := by
  cases R with
  | sc t => show σ'.env l.v = _; rw [hv]; exact h
  | ar k => exact ⟨h.1.frame hv hh, fun hi => by rw [hp]; exact h.2 hi⟩

/-- after a loop: its result is the new slot; the state's other work array stays in use -/
theorem loop_post {C : Nat} {s : Sl} {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {r : s.T} {res : Nat} {rl : PLoc}
    {E0 A X : List (Nat × W64)} {σ : MSt} {env' : Mach.BEnv} {W : W64}
    (hr : RRP σ E0 s res rl r) (hS : Store C σ.env W (E0 ++ (A ++ X))) (hA : arrsP Γ L v env' = A)
    (hv : env' (resLocP s res rl).v = σ.env (resLocP s res rl).v)
    (hp : env' (resLocP s res rl).pt = σ.env (resLocP s res rl).pt)
    (hpool : ∀ j, j = vCap ∨ j = vBump ∨ j = vFh → env' j = σ.env j) :
    ∃ X', Store C env' W (arrsP (s :: Γ) (resLocP s res rl :: L) (r, v) env' ++ X') ∧
      pageCount (E0 ++ (A ++ X)) = pageCount (arrsP (s :: Γ) (resLocP s res rl :: L) (r, v) env' ++ X') ∧
      SRP ⟨env', σ.heap, σ.wheap⟩ s (resLocP s res rl) r := by
  have hS' := hS.env hpool
  cases s with
  | sc t =>
    simp only [resLocP] at hv hp ⊢
    refine ⟨E0 ++ X, ?_, ?_, ?_⟩
    · simp only [arrsP, List.tail_cons]; rw [hA]; exact hS'.perm (by perm_tac)
    · simp only [arrsP, List.tail_cons]; rw [hA]; exact pageCount_perm (by perm_tac)
    · show env' res = _; rw [hv]; exact hr
  | ar k =>
    simp only [resLocP] at hv hp ⊢
    obtain ⟨hsr, he⟩ := hr
    have hsrp : SRP ⟨env', σ.heap, σ.wheap⟩ (.ar k) rl r := hsr.frame hv rfl
    by_cases hi : rl.inp = true
    · refine ⟨E0 ++ X, ?_, ?_, hsrp⟩
      · simp only [arrsP, List.headD_cons, List.tail_cons, hi, if_true]; rw [hA]; exact hS'.perm (by perm_tac)
      · simp only [arrsP, List.headD_cons, List.tail_cons, hi, if_true]; rw [hA]; exact pageCount_perm (by perm_tac)
    · have hf : rl.inp = false := by simpa using hi
      have hE0 := he hf
      refine ⟨X, ?_, ?_, hsrp⟩
      · simp only [arrsP, List.headD_cons, List.tail_cons, hf, Bool.false_eq_true, if_false]; rw [hA, hp]
        rw [hE0] at hS'; simpa using hS'
      · simp only [arrsP, List.headD_cons, List.tail_cons, hf, Bool.false_eq_true, if_false]; rw [hA, hp, hE0]; simp

set_option maxHeartbeats 16000000 in
/-- **Programs**: the code ends with the result and the run's page events within `C` pages, or with `vOk = 0`
exactly when the events exceed `C` pages -/
theorem Pg.compP_ok (C : Nat) : ∀ {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List PLoc) (v : Vals Γ) (env : Mach.BEnv)
    (H : Heap) (W : W64) (d : Nat) (X : List (Nat × W64)) (y : R.T) (E : List MemEvent),
    EnvOK Γ L v ⟨env, H, [W]⟩ → BelowP L d → 9 ≤ d → SlotOK L → Store C env W (arrsP Γ L v env ++ X) →
    env vOk = 1 → p.wfP L d = true → p.GoodE L d v y E →
    ∃ σ' W', Mach.BExec (p.compP L d).1 ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧
      ((σ'.env vOk = 1 ∧ ResP σ' W' R (p.compP L d).2 y ∧ (p.compP L d).2.v ≠ 8 ∧ (p.compP L d).2.pt ≠ 8 ∧
          W'.length < 2 ^ 32 ∧ pk (pageCount (arrsP Γ L v env ++ X)) E ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount (arrsP Γ L v env ++ X)) E))
  | _, .sc t, .ret e, L, v, env, H, W, d, X, y, E, hE, hb, hd, hL, hS, hok1, hwf, hg => by
    simp only [Pg.wfP] at hwf; simp only [Pg.GoodE] at hg
    obtain ⟨rfl, hok, rfl⟩ := hg
    simp only [Pg.compP]
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.compP_ok L e v ⟨env, H, [W]⟩ d hE hE.len hb hwf hok
    refine ⟨σ1, W, e1, h1, w1, .inl ⟨by rw [k1 _ (by simp only [vOk]; omega)]; exact hok1, v1, by omega, by decide,
      hS.1.wlen.2, hS.count_le⟩⟩
  | _, .ar k, .ret a, L, v, env, H, W, d, X, y, E, hE, hb, hd, hL, hS, hok1, hwf, hg => by
    simp only [Pg.GoodE] at hg
    obtain ⟨rfl, rfl⟩ := hg
    cases a with
    | var m =>
      simp only [Pg.compP, skipAt, A.den]
      have hmL := Mem.locP_mem m L hE.len
      have hb1 := hb _ hmL
      refine ⟨_, W, .assign, rfl, rfl, .inl ⟨by simp only [set_ne (show vOk ≠ d by simp only [vOk]; omega)]; exact hok1,
        ⟨(hE.rel.get m).frame (set_ne (by omega)) rfl, fun hi => ?_⟩, (hL _ hmL).2.2.1, (hL _ hmL).2.2.2, hS.1.wlen.2,
        hS.count_le⟩⟩
      simp only [set_ne (show (m.locP L).pt ≠ d by omega)]
      exact hS.2 _ (List.mem_append_left _ (arrsP_mem env m hi))
    | set _ _ _ | push _ _ | ite _ _ _ => simp [Pg.wfP] at hwf
  | Γ, _, .let_ (s := s) x k, L, v, env, H, W, d, X, y, E, hE, hb, hd, hL, hS, hok1, hwf, hg => by
    simp only [Pg.wfP, Bool.and_eq_true] at hwf; simp only [Pg.GoodE] at hg
    obtain ⟨hok, E2, hg2, rfl⟩ := hg
    simp only [Pg.compP]
    have hLnp : ∀ l ∈ L, NP l.v ∧ NP l.pt := fun l h => ⟨(hL l h).1, (hL l h).2.1⟩
    obtain ⟨σ1, W1, e1, h1, w1, k1, o1⟩ := Ini.compP_ok L C s x v env H W d X hE hb (by omega) hLnp
      (hS.perm List.perm_append_comm) hok1 hwf.1 hok
    have hu : pageCount (X ++ arrsP Γ L v env) = pageCount (arrsP Γ L v env ++ X) :=
      pageCount_perm List.perm_append_comm
    rw [hu] at o1
    have hlt := Ini.locP_lt L s x d
    have hnp := Ini.locP_np L s x d hd
    generalize hl0 : Ini.locP L s x d = l0 at hlt hnp o1 hg2 hwf ⊢
    rcases o1 with ⟨ok1, sr1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    · obtain ⟨env1, H1, Ws1⟩ := σ1
      simp only at h1 w1 ok1 S1 fin1 k1 sr1; subst H1 Ws1
      let env2 := env1.set 8 1
      have hk2 : ∀ j, j < d → NP j → j ≠ 8 → env2 j = env j := fun j hj hn h8 => by
        simp only [env2, set_ne h8]; exact k1 j hj hn
      have harr2 : arrsP Γ L v env2 = arrsP Γ L v env :=
        arrsP_congr (fun l h => hk2 _ (hb l h).2 (hL l h).2.1 (hL l h).2.2.2) hE.len
      have h0' : arrsP [s] [l0] (Ini.den s x v, ()) env2 = arrsP [s] [l0] (Ini.den s x v, ()) env1 := by
        apply arrsP_congr _ (by simp)
        intro l h; simp only [List.mem_singleton] at h; subst h
        simp only [env2, set_ne hnp.2.2.2]
      have hS2 : Store C env2 W1 (arrsP (s :: Γ) (l0 :: L) (Ini.den s x v, v) env2 ++ X) := by
        have := S1.env (env' := env2) fun j hj => by simp only [env2, set_ne (show j ≠ 8 by have := pool_vars hj; omega)]
        refine this.perm ?_
        rw [arrsP_cons1 (Γ := Γ) (L := L), harr2, h0']; perm_tac
      have hE2 : EnvOK (s :: Γ) (l0 :: L) (Ini.den s x v, v) ⟨env2, H, [W1]⟩ := by
        refine ⟨⟨sr1.frame (by simp only [env2, set_ne hnp.2.2.1]) rfl,
          hE.rel.frame (fun l h => hk2 _ (hb l h).1 (hL l h).1 (hL l h).2.2.1) rfl hE.len⟩,
          by simp only [List.length_cons]; exact Nat.succ_le_succ hE.len, W1, rfl, S1.1.wlen.2, ?_⟩
        intro a ha; exact hS2.2 a (List.mem_append_left _ ha)
      have hb2 : BelowP (l0 :: L) (d + 2) := fun l h => by
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · omega
        · have := hb l h; omega
      have hL2 : SlotOK (l0 :: L) := fun l h => by
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact hnp
        · exact hL l h
      obtain ⟨σ3, W3, e3, h3, w3, o3⟩ := Pg.compP_ok C k (l0 :: L) (Ini.den s x v, v) env2 H W1 (d + 2) X y E2 hE2 hb2
        (by omega) hL2 hS2 (by simp only [env2, set_ne (show vOk ≠ 8 by decide)]; exact ok1) hwf.2 hg2
      have e2 := guard_true (S := (k.compP (l0 :: L) (d + 2)).1) (σ := ⟨env1, H, [W1]⟩) ok1 e3
      have hpc : finE (pageCount (arrsP Γ L v env ++ X)) (Ini.evsP L s x v) =
          pageCount (arrsP (s :: Γ) (l0 :: L) (Ini.den s x v, v) env2 ++ X) := by
        rw [fin1]; apply pageCount_perm; rw [arrsP_cons1 (Γ := Γ) (L := L), harr2, h0']; perm_tac
      refine ⟨_, W3, .seq e1 e2, by simp [h3], by simp [w3], ?_⟩
      rcases o3 with ⟨ok3, r3, n3, p3, wl3, pk3⟩ | ⟨ok3, pk3⟩
      · refine .inl ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok3,
          r3.frame (set_ne n3) (set_ne p3) rfl, n3, p3, wl3, ?_⟩
        rw [pk_append, hpc]; exact Nat.max_le.2 ⟨pk1, pk3⟩
      · refine .inr ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok3, ?_⟩
        rw [pk_append, hpc]; exact Nat.lt_of_lt_of_le pk3 (Nat.le_max_right _ _)
    · have e2 := guard_false (S := (k.compP (l0 :: L) (d + 2)).1) ok1
      refine ⟨_, W1, .seq e1 e2, h1, w1, .inr ⟨?_, Nat.lt_of_lt_of_le pk1 (pk_mono_left _ _ _)⟩⟩
      simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok1
  | Γ, _, .loop (s := s) Δ b init k, L, v, env, H, W, d, X, y, E, hE, hb, hd, hL, hS, hok1, hwf, hg => by
    simp only [Pg.wfP, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨hwi, hwb⟩, hC⟩, hwk⟩ := hwf
    simp only [Pg.GoodE] at hg
    obtain ⟨hoi, r, P, Eb, Ek, hP0, hPok, hPs, hruns, hgk, rfl⟩ := hg
    simp only [Pg.compP]
    obtain ⟨σ1, W1, e1, h1, w1, k1, o1⟩ := Inis.compP_ok L C init v env H W d X hE hb hd hL hS hok1 hwi hoi
    have hlen : (init.locP L d).length = Δ.length := Inis.locP_length L init d
    have hin := Inis.locP_in L init d
    generalize hst : init.locP L d = st at hwb hC hwk hgk o1 hlen hin ⊢
    generalize hrl : (b.rlP (st ++ L) (d + 2 * Δ.length + 2)).getD rlNone = rl at hwb hC hwk hgk ⊢
    generalize hw : wP Δ st (d + 2 * Δ.length) (d + 2 * Δ.length + 1) = w at hwb hC
    obtain ⟨hlay, hLd, hwl, hLw, hrl', ⟨h8s, h8r, h8f, h8p⟩, hres⟩ := hC
    have hy := hlay.lay
    have hu := Ini.locP_np
    rcases o1 with ⟨ok1, rel1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    rotate_left
    · have e2 := guard_false (S := (Mach.BStmt.seq (b.loopP st (d + 2 * Δ.length) (d + 2 * Δ.length + 1) (st ++ L)
        (d + 2 * Δ.length + 2)) (guard (k.compP (resLocP s (d + 2 * Δ.length) rl :: L) (d + 2 * Δ.length + 2)).1))) ok1
      refine ⟨_, W1, .seq e1 e2, h1, w1, .inr ⟨?_, Nat.lt_of_lt_of_le pk1 (pk_mono_left _ _ _)⟩⟩
      simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok1
    obtain ⟨env1, H1, Ws1⟩ := σ1
    simp only at h1 w1 ok1 S1 fin1 k1 rel1; subst H1 Ws1
    generalize hres' : d + 2 * Δ.length = res at *
    generalize hfl : res + 1 = fl at *
    let env3 := (env1.set 8 1).set fl 1
    have hk3L : ∀ l ∈ L, env3 l.v = env l.v ∧ env3 l.pt = env l.pt := fun l h => by
      simp only [env3, set_ne (hLd l h).1.2.2.1, set_ne (hLd l h).2.2.2.1, set_ne (hL l h).2.2.1,
        set_ne (hL l h).2.2.2]
      exact ⟨k1 _ (hb l h).1 (hL l h).1 (hL l h).2.2.1, k1 _ (hb l h).2 (hL l h).2.1 (hL l h).2.2.2⟩
    have hk3st : ∀ l ∈ st, env3 l.v = env1 l.v ∧ env3 l.pt = env1 l.pt := fun l h => by
      have hv : l.v ∈ vsOfP st := List.mem_map_of_mem h
      refine ⟨?_, ?_⟩
      · simp only [env3, set_ne (show l.v ≠ fl from fun e => hy.fs (e ▸ hv)),
          set_ne (show l.v ≠ 8 from fun e => h8s (e ▸ hv))]
      · simp only [env3, set_ne (hy.ptn l h).2.2, set_ne (h8p l h)]
    have hA3 : arrsP Γ L v env3 = arrsP Γ L v env := arrsP_congr (fun l h => (hk3L l h).2) hE.len
    have hst3 : arrsP Δ st (init.den v) env3 = arrsP Δ st (init.den v) env1 :=
      arrsP_congr (fun l h => (hk3st l h).2) (by omega)
    have hS3 : Store C env3 W1 (arrsP Δ st (init.den v) env3 ++ (arrsP Γ L v env3 ++ X)) := by
      rw [hA3, hst3]
      exact S1.env fun j hj => by
        have := pool_vars hj
        simp only [env3, set_ne (show j ≠ fl by have := hy.p8.2.1; omega), set_ne (show j ≠ 8 by omega)]
    have hE3 : EnvOK (Δ ++ Γ) (st ++ L) (Vals.app (init.den v) v) ⟨env3, H, [W1]⟩ := by
      refine ⟨(RelP.app hlen).2 ⟨rel1.frameL (fun l h => (hk3st l h).1) rfl (by omega),
          hE.rel.frame (fun l h => (hk3L l h).1) rfl hE.len⟩, by simp; have := hE.len; omega, W1, rfl, S1.1.wlen.2, ?_⟩
      unfold AllAt; rw [arrsP_append hlen]
      intro a ha; exact hS3.2 a (by rw [← List.append_assoc]; exact List.mem_append_left _ ha)
    have efl : Mach.BExec (.assign fl (.const 1)) ⟨env1.set 8 1, H, [W1]⟩ ⟨env3, H, [W1]⟩ := .assign
    have hfl1 : env3 fl = 1 := by simp only [env3, set_eq]
    have hok3 : env3 vOk = 1 := by
      simp only [env3, set_ne (show vOk ≠ fl by have := hy.p8.2.1; simp only [vOk]; omega),
        set_ne (show vOk ≠ 8 by decide)]; exact ok1
    obtain ⟨σ4, W4, e4, h4, w4, k4, o4⟩ := T.runP_ok b v st L res fl rl w (res + 2) C X hy hlen hE.len
      (hb.mono (by omega)) hLd hwb hwl hLw hrl' P hPok hPs (init.den v) r Eb hruns hP0 ⟨env3, H, [W1]⟩ W1 hE3
      (by show env3 fl ≠ 0; rw [hfl1]; decide) (.inr hfl1) hok3 rfl hS3
    simp only at h4 k4 o4
    have hu1 : finE (pageCount (arrsP Γ L v env ++ X)) (init.evsP L v) =
        pageCount (arrsP Δ st (init.den v) env3 ++ (arrsP Γ L v env3 ++ X)) := by rw [fin1, hA3, hst3]
    rcases o4 with ⟨ok4, sf, rel4, rr4, S4, fin4, pk4⟩ | ⟨ok4, pk4⟩
    rotate_left
    · -- the loop found no page
      have e5 := guard_false (S := (k.compP (resLocP s res rl :: L) (res + 2)).1) ok4
      have e6 := guard_true (S := Mach.BStmt.seq (b.loopP st res fl (st ++ L) (res + 2))
        (guard (k.compP (resLocP s res rl :: L) (res + 2)).1)) (σ := ⟨env1, H, [W1]⟩) ok1 (.seq (.seq efl e4) e5)
      refine ⟨_, W4, .seq e1 e6, by simp [h4], by simp [w4], .inr ⟨?_, ?_⟩⟩
      · simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok4
      · rw [pk_append, hu1, pk_append]
        exact Nat.lt_of_lt_of_le pk4 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    -- the loop's result; the rest runs
    let env5 := σ4.env.set 8 1
    have hk5L : ∀ l ∈ L, env5 l.v = env l.v ∧ env5 l.pt = env l.pt := fun l h => by
      simp only [env5, set_ne (hL l h).2.2.1, set_ne (hL l h).2.2.2]
      rw [k4 _ (by have := (hb l h).1; omega) (hLd l h).1.1 (hLd l h).1.2.1 (hLd l h).1.2.2.1 (hLd l h).1.2.2.2,
        k4 _ (by have := (hb l h).2; omega) (hLd l h).2.1 (hLd l h).2.2.1 (hLd l h).2.2.2.1 (hLd l h).2.2.2.2]
      exact hk3L l h
    have hA5 : arrsP Γ L v env5 = arrsP Γ L v env3 := by
      rw [arrsP_congr (fun l h => (hk5L l h).2) hE.len, hA3]
    obtain ⟨X', S5, pc5, sr5⟩ := loop_post (env' := env5) rr4 S4 hA5 (by simp only [env5, set_ne hres.2.2.1])
      (by simp only [env5, set_ne hres.2.2.2]) (fun j hj => by
        simp only [env5, set_ne (show j ≠ 8 by have := pool_vars hj; omega)])
    have hE5 : EnvOK (s :: Γ) (resLocP s res rl :: L) (r, v) ⟨env5, H, [W4]⟩ := by
      refine ⟨⟨by rw [← h4]; exact sr5, hE.rel.frame (fun l h => (hk5L l h).1) rfl hE.len⟩,
        by simp only [List.length_cons]; exact Nat.succ_le_succ hE.len, W4, rfl, S4.1.wlen.2, ?_⟩
      intro a ha; exact S5.2 a (List.mem_append_left _ ha)
    have hb5 : BelowP (resLocP s res rl :: L) (res + 2) := fun l h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · cases s with
        | sc t => simp only [resLocP]; omega
        | ar k => simp only [resLocP]; exact hy.hrl
      · have := hb l h; omega
    have hL5 : SlotOK (resLocP s res rl :: L) := fun l h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hres
      · exact hL l h
    have hok5 : env5 vOk = 1 := by simp only [env5, set_ne (show vOk ≠ 8 by decide)]; exact ok4
    obtain ⟨σ6, W6, e6, h6, w6, o6⟩ := Pg.compP_ok C k (resLocP s res rl :: L) (r, v) env5 H W4 (res + 2) X' y Ek hE5
      hb5 (by omega) hL5 S5 hok5 hwk hgk
    have e7 := guard_true (S := (k.compP (resLocP s res rl :: L) (res + 2)).1) (σ := σ4) ok4
      (by rw [show σ4 = ⟨σ4.env, H, [W4]⟩ by cases σ4; simp_all]; exact e6)
    have e8 := guard_true (S := Mach.BStmt.seq (b.loopP st res fl (st ++ L) (res + 2))
        (guard (k.compP (resLocP s res rl :: L) (res + 2)).1)) (σ := ⟨env1, H, [W1]⟩) ok1 (.seq (.seq efl e4) e7)
    refine ⟨_, W6, .seq e1 e8, by simp [h6], by simp [w6], ?_⟩
    have hpkE : pk (pageCount (arrsP Γ L v env ++ X)) (init.evsP L v ++ (Eb ++ Ek)) =
        max (pk (pageCount (arrsP Γ L v env ++ X)) (init.evsP L v))
          (max (pk (pageCount (arrsP Δ st (init.den v) env3 ++ (arrsP Γ L v env3 ++ X))) Eb)
            (pk (pageCount (arrsP (s :: Γ) (resLocP s res rl :: L) (r, v) env5 ++ X')) Ek)) := by
      rw [pk_append, hu1, pk_append, fin4, pc5]
    rcases o6 with ⟨ok6, r6, n6, p6, wl6, pk6⟩ | ⟨ok6, pk6⟩
    · refine .inl ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok6,
        r6.frame (by simp only [set_ne n6]) (by simp only [set_ne p6]) rfl, n6, p6, wl6, ?_⟩
      rw [hpkE]; exact Nat.max_le.2 ⟨pk1, Nat.max_le.2 ⟨pk4, pk6⟩⟩
    · refine .inr ⟨by simp only [set_ne (show vOk ≠ 8 by decide)]; exact ok6, ?_⟩
      rw [hpkE]; exact Nat.lt_of_lt_of_le pk6 (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end Proven.WA

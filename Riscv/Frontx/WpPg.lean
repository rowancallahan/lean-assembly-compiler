/- Paged dynamic arrays (NOTES section 30), part 8: fresh arrays, programs.

A fresh array of a `let` or a loop start (`F`) is a new array of its own pages: `ByteArray.empty` is one page
(`newArr`), `Array.replicate n x` and `xs.extract lo hi` and a copy of a work array are a new array filled by
pushes (`fillLoop`); a view of the input (`xs.data`, an alias of the input) is no array at all (`inp`).

A program's stages are guarded by `vOk`: once a push found no page, the rest is skipped.  At the end of a loop
with a scalar result the state's work array is freed (every page back to the pool). -/
import Riscv.Frontx.WpFill

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB)

/-! ## A new array, filled -/

/-- `newArr`, `i := 0`, the fill loop -/
def newFill (ptv sv x i n t tA : Nat) (Sv : MS) : MS :=
  .seq (newArr ptv sv tA) (.seq (.assign i (.const 0)) (fillLoop ptv sv x i n t Sv))

set_option maxHeartbeats 8000000 in
theorem newFill_ok (ptv sv x i n t tA : Nat) (Sv : MS) (C : Nat) (X : List (Nat × W64)) (f : Nat → BitVec 64)
    (N : Nat) (hN : N ≤ P * P)
    (hv : 8 ≤ ptv ∧ 8 ≤ sv ∧ 8 ≤ x ∧ 8 ≤ i ∧ 8 ≤ n ∧ ptv < t ∧ sv < t ∧ x < t ∧ i < t ∧ n < t ∧ sv ≠ ptv ∧ sv ≠ x ∧
      i ≠ ptv ∧ i ≠ sv ∧ i ≠ x ∧ n ≠ ptv ∧ n ≠ sv ∧ n ≠ x ∧ n ≠ i ∧ ptv ≠ x)
    (hA : 8 ≤ tA ∧ ptv ≠ tA ∧ ptv ≠ tA + 1 ∧ tA + 1 < t ∧ i ≠ tA ∧ i ≠ tA + 1 ∧ n ≠ tA ∧ n ≠ tA + 1 ∧ x ≠ tA ∧
      x ≠ tA + 1 ∧ sv ≠ tA ∧ sv ≠ tA + 1)
    (σ : MSt)
    (hSv : ∀ (pt : Nat) (σ1 : MSt) (W : W64) (xs : W64) (j : Nat), σ1.wheap = [W] → Store C σ1.env W ((pt, xs) :: X) →
      σ1.env i = rN j → j < N →
      (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ ptv → q ≠ tA → q ≠ tA + 1 → NP q → σ1.env q = σ.env q) →
      σ1.heap = σ.heap → ∃ σ', Mach.BExec Sv σ1 σ' ∧ σ'.env x = f j ∧
        (∀ q, q < t → q ≠ x → σ'.env q = σ1.env q) ∧ σ'.heap = σ1.heap ∧ σ'.wheap = σ1.wheap)
    (W : W64) (hW : σ.wheap = [W]) (hS : Store C σ.env W X) (hn : σ.env n = rN N) (hok : σ.env vOk = 1) :
    ∃ σ' W', Mach.BExec (newFill ptv sv x i n t tA Sv) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ ptv → q ≠ tA → q ≠ tA + 1 → NP q → σ'.env q = σ.env q) ∧
      ((σ'.env vOk = 1 ∧ ∃ pt, σ'.env ptv = rN pt ∧ σ'.env sv = rN N ∧
          Store C σ'.env W' ((pt, (List.range N).map f) :: X) ∧
          finE (pageCount X) (.alloc 1 :: pushEvs N) = pageCount ((pt, (List.range N).map f) :: X) ∧
          pk (pageCount X) (.alloc 1 :: pushEvs N) ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount X) (.alloc 1 :: pushEvs N))) := by
  obtain ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩ := hv
  obtain ⟨hA8, hpa, hpa1, hat, hia, hia1, hna, hna1, hxa, hxa1, hsa, hsa1⟩ := hA
  obtain ⟨env0, H0, Ws⟩ := σ
  simp only at hW hS hn hok ⊢; subst hW
  have hW32 := hS.1.wlen.2
  obtain ⟨env1, e1, k1, r1⟩ := newArr_ok H0 hS ptv sv tA ⟨hp8, hA8, hs8⟩ ⟨hpa, hpa1⟩ hsp
  have hk1 : ∀ q, ¬ AllocVars ptv tA q → q ≠ sv → env1 q = env0 q := k1
  rcases r1 with ⟨hlt, ok1, sz1, p, hp1, S1⟩ | ⟨heq, ok1⟩
  · let env2 := env1.set i 0
    have e2 : Mach.BExec (.assign i (.const 0)) ⟨env1, H0, [W]⟩ ⟨env2, H0, [W]⟩ := .assign
    have hn2 : env2 n = rN N := by
      simp only [env2, set_ne hni]
      rw [hk1 n (by simp only [AllocVars, vFh, vBump, vOk]; omega) hns]; exact hn
    have S2 : Store C env2 W ((p, (List.range 0).map f) :: X) := by
      simpa using S1.env (env' := env2) fun q hq => by simp only [env2]; rw [set_ne (by have := pool_vars hq; omega)]
    obtain ⟨σ3, W3, e3, h3, w3, k3, r3⟩ := fillLoop_ok ptv sv x i n t Sv C p X f N hN ⟨env2, H0, [W]⟩
      ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩
      (fun σ1 W1 xs j a b c' d' fr hh => hSv p σ1 W1 xs j a b c' d' (fun q q1 q2 q3 q4 q5 q6 q7 q8 => by
        rw [fr q q1 q2 q3 q4 q8]; simp only [env2, set_ne q4]
        exact hk1 q (by obtain ⟨n1, n2, n3⟩ := q8; simp only [AllocVars]; omega) q3) hh)
      N 0 ⟨env2, H0, [W]⟩ W (by omega) (Nat.zero_le _) rfl (fun _ _ _ _ _ _ => rfl) rfl S2
      (by simp only [env2, set_ne (Ne.symm hip)]; exact hp1)
      (by simp only [env2, set_ne (Ne.symm his)]; exact sz1) (by simp only [env2, set_eq]; rfl) hn2
      (by simp only [env2, set_ne (show vOk ≠ i by simp only [vOk]; omega)]; rw [ok1]; exact hok)
    have hu : pageCount ((p, (List.range 0).map f) :: X) = pageCount X + 1 := by
      simp [pageCount_cons, npages, P]; omega
    refine ⟨σ3, W3, .seq e1 (.seq e2 e3), h3, w3, fun q a b c' d' e' g h' hq => ?_, ?_⟩
    · obtain ⟨n1, n2, n3⟩ := hq
      rw [k3 q a b c' d' n1 n2 n3]
      simp only [env2, set_ne d']
      exact hk1 q (by simp only [AllocVars]; omega) c'
    · rcases r3 with ⟨o3, sz3, S3, p3⟩ | ⟨o3, p3⟩
      · refine .inl ⟨o3, p, ?_, sz3, S3, ?_, ?_⟩
        · rw [k3 ptv hpt hpx (Ne.symm hsp) (Ne.symm hip) (pool_ne hp8).2.2.1 (pool_ne hp8).2.1
            (pool_ne hp8).2.2.2]
          simp only [env2, set_ne (Ne.symm hip)]; exact hp1
        · simp only [finE, stepE, pushEvs]; rw [finE_pushFrom]
          simp [pageCount_cons, npages, P]; omega
        · simp only [pk, stepE, pushEvs]; rw [← hu]
          exact Nat.max_le.2 ⟨Nat.le_trans (by omega) (Store.count_le S2), p3⟩
      · exact .inr ⟨o3, by simp only [pk, stepE, pushEvs]; rw [← hu]; exact Nat.lt_of_lt_of_le p3 (Nat.le_max_right _ _)⟩
  · have hc : (Mach.BExp.bin .and (.bin .ult (.var i) (.var n)) (.var vOk)).denote (env1.set i 0) = 0 := by
      simp only [Mach.BExp.denote, Op.eval, set_ne (show vOk ≠ i by simp only [vOk]; omega), ok1]; simp
    refine ⟨⟨env1.set i 0, H0, [W]⟩, W, .seq e1 (.seq .assign (.loopF hc)), rfl, rfl,
      fun q a b c' d' e' g h' hq => ?_, .inr ⟨by simp only [set_ne (show vOk ≠ i by simp only [vOk]; omega)]; exact ok1, ?_⟩⟩
    · obtain ⟨n1, n2, n3⟩ := hq
      simp only [set_ne d', Mach.BExp.denote]; exact hk1 q (by simp only [AllocVars]; omega) c'
    simp only [pk, stepE]
    rw [heq]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans (le_pk _ _) (Nat.le_max_right _ _))

end Proven.WA

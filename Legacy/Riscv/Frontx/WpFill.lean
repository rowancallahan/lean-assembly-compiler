/- Paged dynamic arrays (NOTES section 30), part 7: filling a fresh array by pushes.

`fillLoopP`: `while (i <u n) &&& vOk { x := value(i); push x; i := i + 1 }` onto the array at the head of the
store.  `Array.replicate`, `extract`, copies of arrays all are a new array (`newArr`) and this loop; the value
code `Sv` is a parameter with its own specification.  The page events: `pushEvs n`, one page per `P`
elements. -/
import Legacy.Riscv.Frontx.WpStmt

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB)

/-- the page event of a push onto an array of `j` elements -/
def pushEv (j : Nat) : List MemEvent := if j % P = 0 then [.alloc 1] else []

/-- the page events of `m` pushes onto an array of `j` elements -/
def pushFrom : Nat → Nat → List MemEvent
  | _, 0 => []
  | j, m + 1 => pushEv j ++ pushFrom (j + 1) m

/-- the page events of `n` pushes onto an empty array -/
def pushEvs (n : Nat) : List MemEvent := pushFrom 0 n

def fillLoopP (ptv sv x i n t : Nat) (Sv : MS) : MS :=
  .loop (.bin .and (.bin .ult (.var i) (.var n)) (.var vOk))
    (.seq Sv (.seq (pushEl ptv sv x t) (.assign i (.bin .add (.var i) (.const 1)))))

theorem finE_pushFrom : ∀ (u j m : Nat), finE u (pushFrom j m) = u + (npages (j + m) - npages j)
  | u, j, 0 => by simp [pushFrom, finE]
  | u, j, m + 1 => by
    rw [pushFrom, finE_append, finE_pushFrom _ (j + 1) m, show j + (m + 1) = j + 1 + m by omega]
    have h1 := npages_push j
    have h2 : npages (j + 1) ≤ npages (j + 1 + m) := by unfold npages; exact Nat.div_le_div_right (by omega)
    unfold pushEv; split
    · rename_i hm; rw [if_pos hm] at h1; simp [finE, stepE]; omega
    · rename_i hm; rw [if_neg hm] at h1; simp [finE]; omega

theorem pk_pushFrom : ∀ (u j m : Nat), pk u (pushFrom j m) = finE u (pushFrom j m)
  | u, j, 0 => by simp [pushFrom, pk, finE]
  | u, j, m + 1 => by
    rw [pushFrom, pk_append, finE_append, pk_pushFrom _ (j + 1) m]
    unfold pushEv; split
    · simp only [pk, finE, stepE]
      have := finE_pushFrom (u + 1) (j + 1) m; omega
    · simp only [pk, finE]; have := finE_pushFrom u (j + 1) m; omega

set_option maxHeartbeats 8000000 in
/-- **the fill loop**: from `j` elements, pushes `f j, f (j + 1), …, f (n - 1)`; or a push found no page -/
theorem fillLoopP_ok (ptv sv x i n t : Nat) (Sv : MS) (C : Nat) (pt : Nat) (others : List (Nat × W64))
    (f : Nat → BitVec 64) (N : Nat) (hN : N ≤ P * P) (σ0 : MSt)
    (hv : 8 ≤ ptv ∧ 8 ≤ sv ∧ 8 ≤ x ∧ 8 ≤ i ∧ 8 ≤ n ∧ ptv < t ∧ sv < t ∧ x < t ∧ i < t ∧ n < t ∧ sv ≠ ptv ∧ sv ≠ x ∧
      i ≠ ptv ∧ i ≠ sv ∧ i ≠ x ∧ n ≠ ptv ∧ n ≠ sv ∧ n ≠ x ∧ n ≠ i ∧ ptv ≠ x)
    (hSv : ∀ (σ : MSt) (W : W64) (xs : W64) (j : Nat), σ.wheap = [W] → Store C σ.env W ((pt, xs) :: others) →
      σ.env i = rN j → j < N → (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → NP q → σ.env q = σ0.env q) →
      σ.heap = σ0.heap → ∃ σ', Mach.BExec Sv σ σ' ∧ σ'.env x = f j ∧
        (∀ q, q < t → q ≠ x → σ'.env q = σ.env q) ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap) :
    ∀ m j (σ : MSt) (W : W64), N - j = m → j ≤ N → σ.wheap = [W] →
      (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → NP q → σ.env q = σ0.env q) → σ.heap = σ0.heap →
      Store C σ.env W ((pt, (List.range j).map f) :: others) → σ.env ptv = rN pt → σ.env sv = rN j →
      σ.env i = rN j → σ.env n = rN N → σ.env vOk = 1 →
      ∃ σ' W', Mach.BExec (fillLoopP ptv sv x i n t Sv) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
        (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ vFh → q ≠ vBump → q ≠ vOk → σ'.env q = σ.env q) ∧
        ((σ'.env vOk = 1 ∧ σ'.env sv = rN N ∧ Store C σ'.env W' ((pt, (List.range N).map f) :: others) ∧
            pk (pageCount ((pt, (List.range j).map f) :: others)) (pushFrom j m) ≤ C) ∨
          (σ'.env vOk = 0 ∧ C < pk (pageCount ((pt, (List.range j).map f) :: others)) (pushFrom j m)))
  | 0, j, σ, W, hm, hj, hW, hf0, hh0, hS, h1, h2, h3, h4, h5 => by
    have hjN : j = N := by omega
    subst hjN
    have hc : (Mach.BExp.bin .and (.bin .ult (.var i) (.var n)) (.var vOk)).denote σ.env = 0 := by
      simp only [Mach.BExp.denote, Op.eval, h3, h4]; simp
    exact ⟨σ, W, .loopF hc, rfl, hW, fun _ _ _ _ _ _ _ _ => rfl, .inl ⟨h5, h2, hS, by simp only [pushFrom, pk]; exact hS.count_le⟩⟩
  | m + 1, j, σ, W, hm, hj, hW, hf0, hh0, hS, h1, h2, h3, h4, h5 => by
    obtain ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩ := hv
    have hjN : j < N := by omega
    have hN32 : N < 2 ^ 32 := by rw [P] at hN; omega
    have hc : (Mach.BExp.bin .and (.bin .ult (.var i) (.var n)) (.var vOk)).denote σ.env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, h3, h4, h5,
        rN_lt (show j < 2 ^ 64 by omega) (show N < 2 ^ 64 by omega), if_pos hjN]; decide
    obtain ⟨σ1, e1, v1, k1, hh1, hw1⟩ := hSv σ W _ j hW hS h3 hjN hf0 hh0
    have hW1 : σ1.wheap = [W] := by rw [hw1, hW]
    have hσ1 : σ1 = ⟨σ1.env, σ1.heap, [W]⟩ := by cases σ1; simp_all
    rw [hσ1] at e1
    have hS1 : Store C σ1.env W ((pt, (List.range j).map f) :: others) :=
      hS.env fun q hq => k1 q (by have := pool_vars hq; omega) (by have := pool_vars hq; omega)
    have hlenj : ((List.range j).map f).length = j := by simp
    obtain ⟨env2, W2, e2, k2, r2⟩ := pushEl_ok σ1.heap hS1 ptv sv x t
      ⟨hp8, hs8, hx8, hpt, hst, hxt, hsp, hsx⟩ (by rw [k1 _ hpt (by omega)]; exact h1)
      (by rw [k1 _ hst (by omega), hlenj]; exact h2) (by rw [hlenj]; omega)
      (by rw [k1 _ (by simp only [vOk]; omega) (by simp only [vOk]; omega)]; exact h5)
    rw [hlenj, v1] at r2
    have hi2 : env2 i = rN j := by rw [k2 i his (by simp only [vFh]; omega) (by simp only [vBump]; omega)
      (by simp only [vOk]; omega) (.inl hit), k1 i hit hix, h3]
    let env3 := env2.set i ((Mach.BExp.bin .add (.var i) (.const 1)).denote env2)
    have hi3 : env3 i = rN (j + 1) := by simp only [env3, set_eq, Mach.BExp.denote, Op.eval, hi2, rN_add]; rfl
    have k3 : ∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ vFh → q ≠ vBump → q ≠ vOk → env3 q = σ.env q :=
      fun q a b c' d' e' g h' => by
        simp only [env3, set_ne d']; rw [k2 q c' e' g h' (.inl a), k1 q a b]
    have hbody : Mach.BExec (.seq Sv (.seq (pushEl ptv sv x t) (.assign i (.bin .add (.var i) (.const 1))))) σ
        ⟨env3, σ.heap, [W2]⟩ := by
      refine .seq e1 (.seq e2 ?_); rw [hh1]; exact .assign
    have hfin1 : pageCount ((pt, (List.range j).map f ++ [f j]) :: others) =
        finE (pageCount ((pt, (List.range j).map f) :: others)) (pushEv j) := by
      simp only [pageCount_cons, List.length_append, List.length_cons, List.length_nil, hlenj, npages_push, pushEv]
      split <;> simp [finE, stepE] <;> omega
    have hrange : (List.range (j + 1)).map f = (List.range j).map f ++ [f j] := by
      rw [List.range_succ, List.map_append]; rfl
    rcases r2 with ⟨ok2, sz2, S2⟩ | ⟨ok2, hm2, hc2⟩
    · have hS3 : Store C env3 W2 ((pt, (List.range (j + 1)).map f) :: others) := by
        rw [hrange]; exact S2.env fun q hq => by simp only [env3]; rw [set_ne (by have := pool_vars hq; omega)]
      obtain ⟨σ4, W4, e4, h4', w4, k4, r4⟩ := fillLoopP_ok ptv sv x i n t Sv C pt others f N hN σ0
        ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩ hSv m (j + 1)
        ⟨env3, σ.heap, [W2]⟩ W2 (by omega) (by omega) rfl
        (fun q a b c' d' hq => by
          show env3 q = _; rw [k3 q a b c' d' hq.1 hq.2.1 hq.2.2]; exact hf0 q a b c' d' hq) hh0 hS3
        (by simp only; rw [k3 _ hpt (by omega) (by omega) (Ne.symm hip) (pool_ne hp8).2.2.1 (pool_ne hp8).2.1 (pool_ne hp8).2.2.2]; exact h1)
        (by simp only [env3, set_ne (Ne.symm his)]; exact sz2) hi3
        (by simp only; rw [k3 _ hnt hnx hns hni (pool_ne hn8).2.2.1 (pool_ne hn8).2.1 (pool_ne hn8).2.2.2]; exact h4)
        (by simp only [env3, set_ne (show vOk ≠ i by simp only [vOk]; omega)]; exact ok2)
      refine ⟨σ4, W4, .loopT hc hbody e4, h4', w4, fun q a b c' d' e' g h' => by
        rw [k4 q a b c' d' e' g h']; exact k3 q a b c' d' e' g h', ?_⟩
      have hpe : pk (pageCount ((pt, (List.range j).map f) :: others)) (pushEv j) =
          finE (pageCount ((pt, (List.range j).map f) :: others)) (pushEv j) := by
        unfold pushEv; split <;> simp [pk, finE, stepE]
      rw [pushFrom, pk_append, hpe, ← hfin1, ← hrange]
      rcases r4 with ⟨o4, sz4, S4, p4⟩ | ⟨o4, p4⟩
      · exact .inl ⟨o4, sz4, S4, Nat.max_le.2 ⟨hS3.count_le, p4⟩⟩
      · exact .inr ⟨o4, Nat.lt_of_lt_of_le p4 (Nat.le_max_right _ _)⟩
    · have hc3 : (Mach.BExp.bin .and (.bin .ult (.var i) (.var n)) (.var vOk)).denote env3 = 0 := by
        simp only [Mach.BExp.denote, Op.eval, env3, set_ne (show vOk ≠ i by simp only [vOk]; omega), ok2]; simp
      refine ⟨⟨env3, σ.heap, [W2]⟩, W2, .loopT hc hbody (.loopF hc3), rfl, rfl, k3, .inr ⟨?_, ?_⟩⟩
      · simp only [env3, set_ne (show vOk ≠ i by simp only [vOk]; omega)]; exact ok2
      · rw [pushFrom, pk_append]
        refine Nat.lt_of_lt_of_le ?_ (Nat.le_max_left _ _)
        simp only [pushEv, if_pos hm2, pk, stepE]; omega

end Proven.WA

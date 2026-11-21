/- Nano/Ownership/OwnP24: the walk loop `o34` (fuel) against `Reach`: a run that ends without the error flag went
through the `Reach` target; a finished body (no frames, phase 1) stops with the done flag. -/
import Nano.Ownership.OwnP23
namespace OwnP
open C OwnSpec ParSpec

def run (W : WCx) (n : Nat) (σ : SB) : Buf × (Buf × Buf) := o34 n W.x σ.1 σ.2.1 σ.2.2 W.t

theorem run_step (W : WCx) (n : Nat) (σ : SB) (hn : ¬ stopped σ) : run W (n + 1) σ = run W n (stp W σ) := by
  obtain ⟨s, f, v⟩ := σ
  have h1 : ¬ bget s 1 = 1 := fun h => hn (.inl h)
  have h5 : ¬ bget s 5 = 1 := fun h => hn (.inr h)
  unfold run; rw [o34]; simp only [beq_iff_eq, h1, h5, if_false]; rfl

theorem run_it (W : WCx) (n : Nat) : ∀ (k : Nat) (σ : SB), (∀ j < k, ¬ stopped (it W j σ)) →
    run W (n + k) σ = run W n (it W k σ)
  | 0, σ, _ => rfl
  | k + 1, σ, h => by
    rw [show n + (k + 1) = n + k + 1 by omega, run_step W _ σ (h 0 (by omega)),
      run_it W n k (stp W σ) (fun j hj => h (j + 1) (by omega))]
    rfl

theorem len2 {s : Buf} (h : bget s 1 = 1) : 2 ≤ s.length := by
  simp only [bget] at h; rw [show (1 : UInt64).toNat = 1 from rfl] at h
  rcases Nat.lt_or_ge s.length 2 with hc | hc
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h; exact absurd h (by decide)
  · exact hc

theorem err_o5'' {s : Buf} (h : 2 ≤ s.length) : bget (o5 s) 1 = 1 := err_bset (by decide) (err_set1 h)

theorem run_err (W : WCx) (n : Nat) (σ : SB) (h : bget σ.1 1 = 1) : bget (run W n σ).1 1 = 1 := by
  obtain ⟨s, f, v⟩ := σ
  rcases n with _ | n
  · unfold run; rw [o34]; exact err_o5'' (len2 h)
  · unfold run; rw [o34]; simp only at h ⊢; simp only [h, beq_self_eq_true, if_true]

theorem run_reach {W : WCx} {σ : SB} {P : SB → Prop} (h : Reach W σ P) (N : Nat) (hok : bget (run W N σ).1 1 ≠ 1) :
    ∃ k, k ≤ N ∧ P (it W k σ) ∧ run W N σ = run W (N - k) (it W k σ) := by
  obtain ⟨k, h1, h2⟩ := h
  by_cases hk : k ≤ N
  · have e := run_it W (N - k) k σ (fun j hj => (h1 j hj).1)
    rw [show N - k + k = N by omega] at e
    rcases h2 with hp | he
    · exact ⟨k, hk, hp, e⟩
    · exact absurd (by rw [e]; exact run_err W _ _ he) hok
  · have e := run_it W 0 N σ (fun j hj => (h1 j (by omega)).1)
    rw [show 0 + N = N by omega] at e
    have hl := (h1 N (by omega)).2
    refine absurd ?_ hok
    rw [e]; generalize it W N σ = τ at hl; obtain ⟨s, f, v⟩ := τ
    unfold run; rw [o34]; exact err_o5'' hl

/-- the body finished: one step sets the done flag, the loop stops -/
theorem run_fin {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hΦ : A.Φ = []) (hp : A.ph = 1) (m : Nat)
    (hok : bget (run W m (s, f, v)).1 1 ≠ 1) : run W m (s, f, v) = (bset s 5 1, (f, v)) := by
  have hS := hSt.1
  have hl := hS.1
  have r4 := (regs hS).2.2.2.1
  have r1 := (regs hS).2.1
  rw [hΦ] at r4
  have hstp : stp W (s, f, v) = (bset s 5 1, f, v) := by
    unfold stp; simp only; rw [o30_ph1 hS hp]; unfold o32; rw [r4]; rfl
  rcases m with _ | m
  · exact absurd (by unfold run; rw [o34]; exact err_o5'' (s := s) (by omega)) hok
  rw [run_step W m _ (st_run hS), hstp] at hok ⊢
  rcases m with _ | m
  · exact absurd (by unfold run; rw [o34]; exact err_o5'' (by simp [bset]; omega)) hok
  · unfold run; rw [o34]; simp only
    have e1 : bget (bset s 5 1) 1 = 0 := by
      rw [← r1]; simp only [bget, bset]; rw [getD_set]; simp
    have e5 : bget (bset s 5 1) 5 = 1 := by
      simp only [bget, bset]; rw [getD_set]; simp; omega
    simp only [e1, e5, beq_self_eq_true, if_true]; rfl

end OwnP

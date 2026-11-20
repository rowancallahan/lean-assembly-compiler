/- A-variants of the prologue / call lemmas with the REAL position-indexed capacity jumps (Gen emits three different jal offsets
to the stub word `tgt`): `proA`, `pro_runA`, `call_liveA`.  The statements of Call.lean are unchanged. -/
import Nano.V2Self.Proof.Machine.Expr
namespace CallProbe

def proA (tgt q r : Nat) : List J :=
  pushA tgt q 1 ++ (pushA tgt (q + 4) 8 ++ [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((q : Int) + 11))])

theorem pro_runA {C : List J} {f r tgt : Nat} {s : St} (hC : At C f (proA tgt f r)) (hlt : (s.x 31).toNat < 2 ^ 63)
    (hh : (s.x 30).toNat + 16 + 8 * r ≤ (s.x 31).toNat) :
    ∃ s1, run C 9 (f, s) = some (f + 12, s1) ∧
      (s1.x 31).toNat = (s.x 31).toNat - 16 - 8 * r ∧ (s1.x 8).toNat = (s.x 31).toNat - 16 ∧
      (∀ i, i ≠ 31 → i ≠ 8 → s1.x i = s.x i) ∧
      s1.m = upd (upd s.m ((s.x 31).toNat - 8) (s.x 1)) ((s.x 31).toNat - 16) (s.x 8) := by
  have A1 : At C f (push 1 ((tgt : Int) - ((f : Int) + 2))) := hC.left
  have R1 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2)) ++
      [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))]) := by
    simpa [proA, pushA, push] using hC.right
  have A2 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2))) := R1.left
  have A3 : At C (f + 8) [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))] := by
    simpa [push] using R1.right
  have r1 := push_run (s := s) A1 (by decide) (by decide) (by omega)
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have t8 : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp; omega
  have t16 : (UInt64.ofNat ((s.x 31).toNat - 8 - 8)).toNat = (s.x 31).toNat - 16 := by simp; omega
  have r2 := push_run (s := ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 1), s.b, s.wk⟩) A2 (by decide) (by decide)
    (by simp [upd, t8]; omega)
  simp only [upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), upd_other _ _ (show (8:Nat) ≠ 31 by decide), t8] at r2
  have r12 := run_add (l := 3) r1
  rw [r2] at r12
  have b0 := A3.at 0 (by simp); have b1 := A3.at 1 (by simp); have b2 := A3.at 2 (by simp)
  simp at b0 b1 b2
  have t16r : (UInt64.ofNat ((s.x 31).toNat - 16 - 8 * r)).toNat = (s.x 31).toNat - 16 - 8 * r := by simp; omega
  have t16' : (UInt64.ofNat ((s.x 31).toNat - 16)).toNat = (s.x 31).toNat - 16 := by simp; omega
  have e16 : (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 := by omega
  rw [e16] at r12
  refine ⟨⟨upd (upd (upd (upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8))) 31 (UInt64.ofNat ((s.x 31).toNat - 16)))
      8 (UInt64.ofNat ((s.x 31).toNat - 16))) 31 (UInt64.ofNat ((s.x 31).toNat - 16 - 8 * r)),
    upd (upd s.m ((s.x 31).toNat - 8) (s.x 1)) ((s.x 31).toNat - 16) (s.x 8), s.b, s.wk⟩, ?_, ?_, ?_, ?_, rfl⟩
  · rw [show 9 = (3 + 3) + 3 by rfl, run_add r12]
    have ea1 : ea (UInt64.ofNat ((s.x 31).toNat - 16)) 0 = (s.x 31).toNat - 16 := by simp [ea, t16']
    have ea2 : ea (UInt64.ofNat ((s.x 31).toNat - 16)) (-8 * (r : Int)) = (s.x 31).toNat - 16 - 8 * r := by
      simp only [ea, t16']; omega
    have c : (s.x 30).toNat ≤ (s.x 31).toNat - 16 - 8 * r := by omega
    simp [run, step, b0, b1, b2, wr, upd_same, upd_other _ _ (show (31:Nat) ≠ 8 by decide), ea1, ea2,
      upd_other _ _ (show (30:Nat) ≠ 31 by decide), upd_other _ _ (show (30:Nat) ≠ 8 by decide), t16r, c,
      show ((f : Int) + 8 + 2 + 2).toNat = f + 12 by omega]
    omega
  · simp [upd_same, t16r]
  · simp [upd_same, upd_other _ _ (show (8:Nat) ≠ 31 by decide), t16']
  · intro i h1 h2; simp [upd, h1, h2]


end CallProbe

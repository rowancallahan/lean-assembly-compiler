/- Machine bridge (Opus box E): the start code on the J machine.  `start_setup`: from word 0 (the jump to the start
code) to main's entry: heap base t5 = a2 + 16, expression stack t6 = sp rounded down to 8, ra / s0 saved at a2 / a2 + 8,
input registers t3 / t4, `jal ra main`. -/
import Nano.V2Self.Proof.StartCode
namespace Templates
open CallProbe

theorem At.get {C : List J} {h : Nat} {l : List J} (hC : At C h l) (j : Nat) (hj : j < l.length) :
    C[h + j]? = l[j]? := hC j hj

/-- the state at main's entry -/
structure Entry (s0 s1 : St) (S : Nat) : Prop where
  x0 : s1.x 0 = 0
  x1 : s1.x 1 = UInt64.ofNat (s0.b + 4 * (S + 12))
  x8 : s1.x 8 = s0.x 8
  x12 : s1.x 12 = s0.x 12
  x13 : s1.x 13 = s0.x 13
  x28 : s1.x 28 = s0.x 10
  x29 : s1.x 29 = s0.x 11
  x30 : s1.x 30 = UInt64.ofNat ((s0.x 12).toNat + 16)
  x31 : s1.x 31 = (s0.x 2 >>> 3) <<< 3
  m : s1.m = upd (upd s0.m (s0.x 12).toNat (s0.x 1)) ((s0.x 12).toNat + 8) (s0.x 8)
  b : s1.b = s0.b

theorem start_setup {C : List J} {S w : Nat} (h0 : At C 0 (stubJ S)) (hS : At C S (startJ S w)) (s0 : St)
    (z0 : s0.x 0 = 0) (ha2 : (s0.x 12).toNat + 16 < 2 ^ 64)
    (hroom : (s0.x 12).toNat + 16 ≤ ((s0.x 2 >>> 3) <<< 3).toNat) :
    ∃ s1, Star C (0, s0) (w, s1) ∧ Entry s0 s1 S := by
  have c := fun j (hj : j < 32) => At.get hS j (by rw [startJ_len]; exact hj)
  have j0 : C[0]? = some (.jal 0 (S : Int)) := by simpa [stubJ] using At.get h0 0 (by simp [stubJ])
  simp only [startJ] at c
  have c0 := c 0 (by omega); have c1 := c 1 (by omega); have c2 := c 2 (by omega); have c3 := c 3 (by omega)
  have c7 := c 7 (by omega); have c8 := c 8 (by omega); have c9 := c 9 (by omega); have c10 := c 10 (by omega)
  have c11 := c 11 (by omega)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c7 c8 c9 c10 c11
  have lt12 := (s0.x 12).toNat_lt
  have e16 : ea (s0.x 12) 16 = (s0.x 12).toNat + 16 := by simp [ea]; omega
  have e0 : ∀ v : UInt64, ea v 0 = v.toNat := by intro v; simp [ea]
  have e8 : ea (s0.x 12) 8 = (s0.x 12).toNat + 8 := by simp [ea]; omega
  have hd : ∀ {a b c}, step C a = some b → Star C b c → Star C a c := fun h1 h2 => (Star.one h1).trans h2
  have sj : step C (0, s0) = some (S, s0) := by simp [step, j0, CallProbe.wr]
  have jw : ∀ {s : St}, step C (S + 11, s) = some (w, CallProbe.wr s 1 (UInt64.ofNat (s.b + 4 * (S + 11 + 1)))) := by
    intro s; rw [s_jal (by simpa using c11)]; congr; omega
  have bg : ∀ {s : St}, (s.x 30).toNat ≤ (s.x 31).toNat → step C (S + 3, s) = some (S + 7, s) := by
    intro s h; rw [s_bgeu_t (by simpa using c3) h]; congr 2
  refine ⟨_, hd sj (hd (s_addi (by simpa using c0)) (hd (by simp [step, c1]; rfl) (hd (s_slli (by simpa using c2))
    (hd (bg ?_) (hd (s_sd (by simpa using c7)) (hd (s_sd (by simpa using c8))
    (hd (s_addi (by simpa using c9)) (hd (s_addi (by simpa using c10)) (Star.one jw))))))))), ?_⟩
  · simp [CallProbe.wr, CallProbe.upd, e16, UInt64.toNat_ofNat] at hroom ⊢; omega
  · have u30 : UInt64.ofNat (ea (s0.x 12) 16) = UInt64.ofNat ((s0.x 12).toNat + 16) := by rw [e16]
    constructor <;> simp [CallProbe.wr, CallProbe.upd, e0, e8, z0]
    · rw [UInt64.add_assoc]; rfl
    · rw [e16]; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]

end Templates

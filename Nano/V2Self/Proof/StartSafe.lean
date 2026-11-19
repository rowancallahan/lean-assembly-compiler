/- Machine bridge (Opus box E): the start code's runs are SAFE (`SimW.SStarX`), so `SimW.sim_starX` lifts them to
Sail.  Layout facts: the a2 save cells are work cells, the code is short enough for Gen's jumps. -/
import Nano.V2Self.Proof.StartRun
import Nano.V2Self.Proof.SimX
namespace Templates
open CallProbe SimW

theorem start_setupX {K : LayW} {C : List J} {S w : Nat} (h0 : At C 0 (stubJ S)) (hS : At C S (startJ S w))
    (s0 : St) (z0 : s0.x 0 = 0) (ha2 : (s0.x 12).toNat + 16 < 2 ^ 64)
    (hroom : (s0.x 12).toNat + 16 ≤ ((s0.x 2 >>> 3) <<< 3).toNat)
    (hw0 : wok K (s0.x 12).toNat) (hw8 : wok K ((s0.x 12).toNat + 8))
    (hCl : S + 32 ≤ C.length) (hC18 : C.length < 2 ^ 18) (hwl : w < C.length) :
    ∃ s1, SStarX K C (0, s0) (w, s1) ∧ Entry s0 s1 S := by
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
  have hd : ∀ {a b c}, SafeX K C a → step C a = some b → SStarX K C b c → SStarX K C a c :=
    fun h0 h1 h2 => .head h0 h1 h2
  have sj : step C (0, s0) = some (S, s0) := by simp [step, j0, CallProbe.wr]
  have jw : ∀ {s : St}, step C (S + 11, s) = some (w, CallProbe.wr s 1 (UInt64.ofNat (s.b + 4 * (S + 11 + 1)))) := by
    intro s; rw [s_jal (by simpa using c11)]; congr; omega
  have bg : ∀ {s : St}, (s.x 30).toNat ≤ (s.x 31).toNat → step C (S + 3, s) = some (S + 7, s) := by
    intro s h; rw [s_bgeu_t (by simpa using c3) h]; congr 2
  refine ⟨_, hd ?_ sj (hd ?_ (s_addi (by simpa using c0)) (hd ?_ (by simp [step, c1]; rfl) (hd ?_ (s_slli (by simpa using c2))
    (hd ?_ (bg ?_) (hd ?_ (s_sd (by simpa using c7)) (hd ?_ (s_sd (by simpa using c8))
    (hd ?_ (s_addi (by simpa using c9)) (hd ?_ (s_addi (by simpa using c10)) (hd ?_ jw (.refl _)))))))))), ?_⟩
  -- goals: SafeX ×5, the bgeu condition, SafeX ×5, Entry
  case refine_6 => simp [CallProbe.wr, CallProbe.upd, e16, UInt64.toNat_ofNat] at hroom ⊢; omega
  case refine_12 =>
    constructor <;> simp [CallProbe.wr, CallProbe.upd, e0, e8, z0]
    · rw [UInt64.add_assoc]; rfl
    · rw [e16]; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]
  all_goals simp only [SafeX]
  all_goals simp [j0, c0, c1, c2, c3, c7, c8, c9, c10, c11, CallProbe.wr, CallProbe.upd, e0, e8, e16, z0]
  all_goals have := (s0.x 10).toNat_lt
  all_goals have := (s0.x 11).toNat_lt
  all_goals first | exact hw0 | exact ⟨by omega, hw8⟩ | omega

end Templates

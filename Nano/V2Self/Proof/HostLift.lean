/- Opus box E: the host lift (Sail `ImplementsCW` ↔ `SimW.RelW`).  `sim_ret`: the final `jalr x0, 0(ra)` as one Sail
step to any (even) ra — J's pc cannot name a return address below the code. -/
import Nano.V2Self.Proof.GenMain
namespace SimW
open Proven Nano.V2B

/-- **the return**: `jalr x0, 0(a)` at a related state retires to pc = the register's value; registers and memory kept -/
theorem sim_ret {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a : Nat} (ha : a < 32) (hC : K.W[pc]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat a) 0).toNat)
    (he : (s.x a).toNat % 2 = 0) :
    ∃ t' v, Next t t' (s.x a).toBitVec 0 v t.mem := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  have haN : (UInt64.ofNat a).toNat = a := by simp; omega
  rw [Bridge.g2_jalr _ (by omega), haN] at hi
  let A : Fin 32 := ⟨a, ha⟩
  have e : getX t A + (0 : BitVec 12).signExtend 64 = (s.x a).toBitVec := by
    rw [hR.x A]; simp [A]
  obtain ⟨t', hN⟩ := G.step_jalr hR.cfg hR.pc hok 0 A 0 (by simpa using hi) (by rw [e]; simpa using he)
  rw [e] at hN
  exact ⟨t', _, hN⟩

end SimW

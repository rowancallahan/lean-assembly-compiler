/- The RISC-V adapter's machine steps beyond `SimX` (Sail): the return `jalr x0, 0(ra)` to any even address (`sim_ret`)
and addi with the hardware's wrapping sum (`sim_addiN`); Gen's 4 little-endian bytes per word (`le4`, `g40_bytes`). -/
import Nano.V2Self.Proof.Machine.GenMain
import Nano.V2Self.Proof.Machine.SimX
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

/-- the 4 little-endian bytes Gen emits for a word -/
def le4 (v : UInt64) : List UInt8 := [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

theorem g40_bytes (c : List UInt8) (ws : List UInt64) (hl : ws.length < 2 ^ 64) :
    ∀ n i (o : List UInt8), ws.length ≤ i + n → i ≤ ws.length →
      C.g40 n c ws (UInt64.ofNat i) o = o ++ (ws.drop i).flatMap le4
  | 0, i, o, h1, h2 => by
    rw [List.drop_of_length_le (by omega)]; simp [C.g40]
  | n + 1, i, o, h1, h2 => by
    simp only [C.g40, bsize, bget]
    have hi : (UInt64.ofNat i).toNat = i := by simp; omega
    by_cases h : i < ws.length
    · have : UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      have e1 : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        apply UInt64.toNat_inj.1; simp; all_goals omega
      simp only [this, if_true]
      rw [e1, g40_bytes c ws hl n (i + 1) _ (by omega) (by omega), hi]
      simp [put, le4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.drop_eq_getElem_cons h, List.flatMap_cons]; rfl
    · have : ¬ UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      simp only [this, if_false]
      rw [List.drop_of_length_le (by omega)]; simp

section
open Templates CallProbe C GenRef ParSpec

/-- **addi**, any sum: the J register gets the hardware's value `x[a] + imm` -/
theorem sim_addiN {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {imm : Int} (hC : K.W[pc]? = some (I.i .addi rd a imm).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ imm) (hi2 : imm < 2048) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a + UInt64.ofInt imm)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 0 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by
    rw [imm12_toNat]; exact hi
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc hok RD A _ hi'
  have hv : getX t A + (BitVec.ofNat 12 (bits imm 12)).signExtend 64 = (s.x a + UInt64.ofInt imm).toBitVec := by
    rw [hR.x A, sext_bits imm hi1 hi2, UInt64.toBitVec_add, ofInt_bv]
  rw [hv] at hN
  exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

end

end SimW

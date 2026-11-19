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

/-! ## the code bytes -/

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
      rw [if_pos this, e1, g40_bytes c ws hl n (i + 1) _ (by omega) (by omega), hi]
      simp [put, le4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.drop_eq_getElem_cons h, List.flatMap_cons]; rfl
    · have : ¬ UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      rw [if_neg this, List.drop_of_length_le (by omega)]; simp

theorem flat_le4 : ∀ (ws : List UInt64) (i k : Nat), i < ws.length → k < 4 →
    (ws.flatMap le4)[4 * i + k]? = (le4 ws[i]!)[k]?
  | [], i, k, h, _ => absurd h (by simp)
  | w :: ws, 0, k, _, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem?_append_left (by simp [le4]; omega)]; simp
  | w :: ws, i + 1, k, h, hk => by
    simp only [List.flatMap_cons]
    rw [List.getElem?_append_right (by simp [le4]; omega)]
    have := flat_le4 ws i k (by simp at h; omega) hk
    rw [show 4 * (i + 1) + k - (le4 w).length = 4 * i + k by simp [le4]; omega, this]; simp

theorem byte_le4 (v : UInt64) (hv : v.toNat < 2 ^ 32) (k : Nat) (hk : k < 4) :
    ∃ b, (le4 v)[k]? = some b ∧ b.toBitVec = (BitVec.ofNat 32 v.toNat).extractLsb' (8 * k) 8 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    refine ⟨_, rfl, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [le4, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, UInt64.toNat_shiftRight] <;> omega

theorem len_le4 (ws : List UInt64) : (ws.flatMap le4).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih]; simp [le4]; omega

/-- the code bytes at `e` give every word as an instruction -/
theorem code_at {t : Proven.St} {e : Nat} {ws : List UInt64} (hv : ∀ v ∈ ws, v.toNat < 2 ^ 32)
    (he : e + 4 * ws.length < 2 ^ 64)
    (hb : bytesAt t e (ws.flatMap le4).length = (ws.flatMap le4).map (some ·.toBitVec)) :
    ∀ i (h : i < ws.length), instrAt t (BitVec.ofNat 64 (e + 4 * i)) (BitVec.ofNat 32 ws[i].toNat) := by
  intro i h
  have hlen := len_le4 ws
  have g : ∀ k, k < 4 → t.mem[e + 4 * i + k]? = some ((BitVec.ofNat 32 ws[i].toNat).extractLsb' (8 * k) 8) := by
    intro k hk
    have h1 := congrArg (·[4 * i + k]?) hb
    simp only [bytesAt, List.getElem?_map, List.getElem?_range (show 4 * i + k < (ws.flatMap le4).length by omega),
      Option.map_some] at h1
    rw [flat_le4 ws i k h hk] at h1
    obtain ⟨b, hb1, hb2⟩ := byte_le4 ws[i] (hv _ (List.getElem_mem h)) k hk
    rw [getElem!_pos ws i h, hb1] at h1
    simp at h1; rw [Nat.add_assoc, h1, hb2]
  have hn : (BitVec.ofNat 64 (e + 4 * i)).toNat = e + 4 * i := by simp; omega
  unfold instrAt; rw [hn]
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)⟩

end SimW

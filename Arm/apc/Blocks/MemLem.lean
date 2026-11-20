/- DeepMind memory facts for the load/store blocks: byte reads after `write64`, permissions kept by stores, the code
(`CodeOK`) kept by stores to writable bytes, `read64` of 8 known bytes. -/
import Blocks.Block
import Apc.Mem8
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm

theorem allPerm_w8 (m : Arm64.Memory) (a : BitVec 64) (v : BitVec 8) (p : Option Arm64.Perm → Bool) :
    ∀ n b, (m.write8 a v).allPerm p b n = m.allPerm p b n
  | 0, _ => rfl
  | n + 1, b => by simp only [Arm64.Memory.allPerm, perm_w8, allPerm_w8 m a v p n]

theorem allPerm_byte (m : Arm64.Memory) (p : Option Arm64.Perm → Bool) :
    ∀ n b, m.allPerm p b n = true → ∀ i < n, m.allPerm p (b + BitVec.ofNat 64 i) 1 = true
  | 0, _, _, i, hi => absurd hi (by omega)
  | n + 1, b, h, i, hi => by
    simp only [Arm64.Memory.allPerm, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa [Arm64.Memory.allPerm] using h.1
    · have := allPerm_byte m p n (b + 1#64) h.2 i (by omega)
      rwa [show b + 1#64 + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (i + 1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this

/-- a store to a writable byte keeps the code -/
theorem CodeOK.w8 {C : List J} {b : Nat} {m : Arm64.Memory} (h : CodeOK C b m) {a : BitVec 64}
    (hw : m.canWrite a 1 = true) (v : BitVec 8) : CodeOK C b (m.write8 a v) := by
  refine ⟨h.lt, h.b4, fun i j hj k hk => ?_⟩
  obtain ⟨he, hr⟩ := h.w i j hj k hk
  refine ⟨by simp only [Arm64.Memory.canExec, allPerm_w8]; exact he, ?_⟩
  have hb := allPerm_byte m _ 4 _ he
  have ne : ∀ q < 4, ad (b + 16 * i + 4 * k) + BitVec.ofNat 64 q ≠ a := fun q hq =>
    exec_ne_write (hb q hq) hw
  rw [← hr]
  simp only [Arm64.Memory.read32, read_w8, ne 0 (by omega), ne 1 (by omega), ne 2 (by omega), ne 3 (by omega),
    ite_false]

/-- `write64` is eight byte stores -/
theorem write64_eq8 (m : Arm64.Memory) (e v : BitVec 64) : m.write64 e v =
    ((((((((m.write8 (e + 0#64) (v.extractLsb' 0 8)).write8 (e + 1#64) (v.extractLsb' 8 8)).write8 (e + 2#64)
      (v.extractLsb' 16 8)).write8 (e + 3#64) (v.extractLsb' 24 8)).write8 (e + 4#64) (v.extractLsb' 32 8)).write8
      (e + 5#64) (v.extractLsb' 40 8)).write8 (e + 6#64) (v.extractLsb' 48 8)).write8 (e + 7#64) (v.extractLsb' 56 8)) := rfl

/-- a property kept by every store to a writable byte is kept by `write64` to 8 writable bytes -/
theorem w64_keep (P : Arm64.Memory → Prop) (hP : ∀ m a v, m.canWrite a 1 = true → P m → P (m.write8 a v))
    (m : Arm64.Memory) (e v : BitVec 64) (hw : ∀ i < 8, m.canWrite (e + BitVec.ofNat 64 i) 1 = true) (h : P m) :
    P (m.write64 e v) := by
  rw [write64_eq8]
  have cw : ∀ (m' : Arm64.Memory), (∀ x, m'.canWrite x 1 = m.canWrite x 1) → ∀ i < 8,
      m'.canWrite (e + BitVec.ofNat 64 i) 1 = true := fun m' hm i hi => by rw [hm]; exact hw i hi
  have k : ∀ (m' : Arm64.Memory) a v', (∀ x, m'.canWrite x 1 = m.canWrite x 1) →
      ∀ x, (m'.write8 a v').canWrite x 1 = m.canWrite x 1 := fun m' a v' hm x => by rw [canWrite_w8, hm]
  have r0 : ∀ x, m.canWrite x 1 = m.canWrite x 1 := fun _ => rfl
  refine hP _ _ _ (cw _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ r0))))))) 7 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ r0)))))) 6 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ r0))))) 5 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ (k _ _ _ (k _ _ _ (k _ _ _ r0)))) 4 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ (k _ _ _ (k _ _ _ r0))) 3 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ (k _ _ _ r0)) 2 (by omega))
    (hP _ _ _ (cw _ (k _ _ _ r0) 1 (by omega))
    (hP _ _ _ (by simpa using hw 0 (by omega)) h)))))))

theorem read8_w64 (m : Arm64.Memory) (e v : BitVec 64) (k : Nat) (hk : k < 8) :
    (m.write64 e v).read8 (e + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8 := by
  rw [write64_eq8]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [read_w8]

theorem read8_w64_ne (m : Arm64.Memory) (e v x : BitVec 64) (h : ∀ k < 8, x ≠ e + BitVec.ofNat 64 k) :
    (m.write64 e v).read8 x = m.read8 x := by
  rw [write64_eq8]
  simp only [read_w8, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega), ite_false]

theorem canRead_w64 (m : Arm64.Memory) (e v x : BitVec 64) (h : m.canRead x 1 = true) :
    (m.write64 e v).canRead x 1 = true := by
  rw [write64_eq8]; repeat (apply canRead_w8)
  exact h
theorem canWrite_w64 (m : Arm64.Memory) (e v x : BitVec 64) : (m.write64 e v).canWrite x 1 = m.canWrite x 1 := by
  rw [write64_eq8]; simp only [canWrite_w8]

theorem ad_addk (a k : Nat) (h : a + k < 2 ^ 64) : ad a + BitVec.ofNat 64 k = ad (a + k) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ad_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : ad x ≠ ad y := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

/-- an 8-byte store to cell `e ∈ D`: the cells are J's `upd m e v`; code kept -/
theorem memOK_w64 {D : Nat → Prop} {m : Nat → UInt64} {mem : Arm64.Memory} (h : MemOK D m mem) {e : Nat} (he : D e)
    (v : UInt64) : MemOK D (CallProbe.upd m e v) (mem.write64 (ad e) v.toBitVec) := by
  obtain ⟨he8, hel, heb⟩ := h e he
  intro a ha
  obtain ⟨ha8, hal, hab⟩ := h a ha
  refine ⟨ha8, hal, fun k hk => ⟨canRead_w64 _ _ _ _ (hab k hk).1, by rw [canWrite_w64]; exact (hab k hk).2.1, ?_⟩⟩
  by_cases hae : a = e
  · subst hae
    rw [← ad_addk _ _ (by omega), read8_w64 _ _ _ _ hk]; simp [CallProbe.upd]
  · rw [read8_w64_ne _ _ _ _ fun k' hk' => by
      rw [ad_addk _ _ (by omega)]; exact ad_ne (by omega) (by omega) (by omega)]
    simp only [CallProbe.upd, hae, ite_false]; exact (hab k hk).2.2

/-- the 8 bytes of a cell, read at once -/
theorem read64_cell {D : Nat → Prop} {m : Nat → UInt64} {mem : Arm64.Memory} (h : MemOK D m mem) {e : Nat}
    (he : D e) : mem.canRead (ad e) 8 = true ∧ mem.read64 (ad e) = (m e).toBitVec := by
  obtain ⟨he8, hel, heb⟩ := h e he
  have hb : ∀ k < 8, mem.read8 (ad e + BitVec.ofNat 64 k) = (m e).toBitVec.extractLsb' (8 * k) 8 := fun k hk => by
    rw [ad_addk _ _ (by omega)]; exact (heb k hk).2.2
  refine ⟨canRead_of mem 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (heb k hk).1, ?_⟩
  unfold Arm64.Memory.read64
  simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
    hb 3 (by omega), hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
  exact bytes8 _

theorem canWrite_cell {D : Nat → Prop} {m : Nat → UInt64} {mem : Arm64.Memory} (h : MemOK D m mem) {e : Nat}
    (he : D e) : ∀ k < 8, mem.canWrite (ad e + BitVec.ofNat 64 k) 1 = true := fun k hk => by
  obtain ⟨he8, hel, heb⟩ := h e he
  rw [ad_addk _ _ (by omega)]; exact (heb k hk).2.1

end Proven.Apc.Blocks

/- **Linking two compiled stages into one binary** (integration glue, branch nano-int).

`link cf cg` = an 18-word stub, then `cg`, then `cf`.  If `cf` implements `f` (with the result length in `a1`,
`retLen = true`) and `cg` implements `g` (both in the sense of `Implements1With`, `Spec/Implements1.lean`), then
`link cf cg` implements `g ∘ f` (`link_implements`).  This is what makes ONE binary out of separately compiled
compiler stages (`asm ∘ genR ∘ nanoElab`).

The stub splits the work block `[wb, wb + W)` with `t = 8 * (W / 32)`:
`[wb, wb + t)` output of `f` = input of `g`; `[wb + t, wb + 2t)` work of `f`; `[wb + 2t, +32)` the stub's frame
(`ra`, `a3`, `sp`, `a2`); the rest, up to the original `sp`, work of `g`.  `f` is called with `jal`; `g` is
entered by falling through with the caller's `ra`, `a3` and `sp`, so `g`'s return is the binary's return. -/
import Riscv.Steps.GenUse
import Riscv.Direct.SortMachine
import Spec.Implements1
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Nano.Link
open Proven

/-- the stub; `o` = half the byte distance from the `jal` to `f`'s code -/
def stub (o : BitVec 20) : List (BitVec 32) :=
  [ encR 0x20 0 5 2 12,              --  0 sub t0, sp, a2        (W)
    encI 5 (0 <<< 6 ||| 5) 5 5,      --  1 srli t0, t0, 5
    encI 1 (0 <<< 6 ||| 3) 5 5,      --  2 slli t0, t0, 3        (t)
    encR 0 0 6 12 5,                 --  3 add t1, a2, t0
    encR 0 0 6 6 5,                  --  4 add t1, t1, t0        (frame = wb + 2t)
    G.encS 3 0 1 6,                  --  5 sd ra, 0(t1)
    G.encS 3 8 13 6,                 --  6 sd a3, 8(t1)
    G.encS 3 16 2 6,                 --  7 sd sp, 16(t1)
    G.encS 3 24 12 6,                --  8 sd a2, 24(t1)
    encI 0 0 13 12,                  --  9 addi a3, a2, 0        (f's output = wb)
    encR 0 0 12 12 5,                -- 10 add a2, a2, t0        (f's work = wb + t)
    encI 0 0 2 6,                    -- 11 addi sp, t1, 0        (f's work top = frame)
    wJ (.ofFin (1 : Fin 32)) o,      -- 12 jal ra, f
    G.encL 3 0 1 2,                  -- 13 ld ra, 0(sp)
    G.encL 3 8 13 2,                 -- 14 ld a3, 8(sp)
    G.encL 3 24 10 2,                -- 15 ld a0, 24(sp)         (g's input = wb)
    encI 0 32 12 2,                  -- 16 addi a2, sp, 32       (g's work = frame + 32)
    G.encL 3 16 2 2 ]                -- 17 ld sp, 16(sp)

/-- **the linked binary**: stub, `g`'s code, `f`'s code -/
def link (cf cg : List (BitVec 32)) : List (BitVec 32) :=
  stub (BitVec.ofNat 20 (2 * (6 + cg.length))) ++ cg ++ cf

/-! ## Helpers -/

theorem codeBytes_length (c : List (BitVec 32)) : (codeBytes c).length = 4 * c.length := by
  induction c with
  | nil => rfl
  | cons w ws ih =>
    rw [show codeBytes (w :: ws) = [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8,
      w.extractLsb' 24 8].map some ++ codeBytes ws from rfl, List.length_append, ih]
    simp only [List.length_map, List.length_cons, List.length_nil]; omega

theorem codeBytes_append (a b : List (BitVec 32)) : codeBytes (a ++ b) = codeBytes a ++ codeBytes b := by
  simp [codeBytes]

/-- the bytes of a concatenated code block, split -/
theorem bytesAt_split {s : St} {a : Nat} {c₁ c₂ : List (BitVec 32)}
    (h : bytesAt s a (4 * (c₁ ++ c₂).length) = codeBytes (c₁ ++ c₂)) :
    bytesAt s a (4 * c₁.length) = codeBytes c₁ ∧ bytesAt s (a + 4 * c₁.length) (4 * c₂.length) = codeBytes c₂ := by
  rw [List.length_append, Nat.mul_add, bytesAt_append, codeBytes_append] at h
  exact List.append_inj h (by simp [bytesAt, codeBytes_length])

theorem bytesAt_congr {s s' : St} {a n : Nat} (h : ∀ i < n, s'.mem[a + i]? = s.mem[a + i]?) :
    bytesAt s' a n = bytesAt s a n := by
  simp only [bytesAt]; exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

/-- an 8-byte store read back -/
theorem slot (m : Mem) (A : Nat) (v : BitVec 64) {k : Nat} (hk : k < 8) :
    (storeBytes m A (le8 v))[A + k]? = some (v.extractLsb' (8 * k) 8) := by
  rw [storeBytes_le8]; simp only [Std.ExtHashMap.getElem?_insert]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all <;> omega

/-- an 8-byte store elsewhere -/
theorem other (m : Mem) (A : Nat) (v : BitVec 64) {a : Nat} (h : a < A ∨ A + 8 ≤ a) :
    (storeBytes m A (le8 v))[a]? = m[a]? := by
  rw [storeBytes_le8]; simp only [Std.ExtHashMap.getElem?_insert]
  repeat rw [if_neg (by simp; omega)]

/-- `ld` of a slot whose eight bytes are known -/
theorem ld_slot {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
    (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (G.encL 3 imm rd rs1)) {A : Nat} {v : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = BitVec.ofNat 64 A) (hr : 0x80000000 ≤ A ∧ A + 8 ≤ 0x100000000)
    (hal : A % 8 = 0) (hv : ∀ k < 8, s.mem[A + k]? = some (v.extractLsb' (8 * k) 8)) :
    ∃ s', Next s s' (pc + 4) rd v s.mem := by
  have e : (BitVec.ofNat 64 A).toNat = A := by simp only [BitVec.toNat_ofNat]; omega
  have := G.step_ld h hpc hok rd rs1 imm hi hA (by rw [e]; exact hr) (by rw [e]; exact hal)
    (by rw [e]; exact hv 0 (by omega)) (by rw [e]; exact hv 1 (by omega)) (by rw [e]; exact hv 2 (by omega))
    (by rw [e]; exact hv 3 (by omega)) (by rw [e]; exact hv 4 (by omega)) (by rw [e]; exact hv 5 (by omega))
    (by rw [e]; exact hv 6 (by omega)) (by rw [e]; exact hv 7 (by omega))
  rwa [le8_cat] at this

/-- `sd` at a known address -/
theorem sd_slot {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
    (rs2 rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (G.encS 3 imm rs2 rs1)) {A : Nat}
    (hA : getX s rs1 + imm.signExtend 64 = BitVec.ofNat 64 A) (hr : 0x80000000 ≤ A ∧ A + 8 ≤ 0x100000000)
    (hal : A % 8 = 0) : ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem A (le8 (getX s rs2))) := by
  have e : (BitVec.ofNat 64 A).toNat = A := by simp only [BitVec.toNat_ofNat]; omega
  have := G.step_sd h hpc hok rs2 rs1 imm hi hA (by rw [e]; exact hr) (by rw [e]; exact hal)
  rwa [e] at this

theorem getX_next {s s' : St} {pc rd v m} (n : Next s s' pc rd v m) (j : Fin 32) :
    getX s' j = if j = rd ∧ j ≠ 0 then v else getX s j := n.x j

/-- the jump offset of the stub's `jal` -/
theorem joff_ofNat {k : Nat} (hk : k < 2 ^ 19) : joff (BitVec.ofNat 20 k) = BitVec.ofNat 64 (2 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [joff, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat]
  have : (BitVec.ofNat 20 k +++ (0#1 : BitVec 1)).toNat = 2 * k := by
    show (BitVec.ofNat 20 k ++ (0#1 : BitVec 1)).toNat = 2 * k
    simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.zero_mod, Nat.or_zero]
    omega
  have hm : (BitVec.ofNat 20 k +++ (0#1 : BitVec 1)).msb = false := by
    rw [BitVec.msb_eq_decide, this]; simp; omega
  simp [hm, this]

/-- the registers `abiSavedKept` speaks about -/
def saved : List (Fin 32) := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem abi_of_getX {s s' : St} (h : Cfg s) (h' : Cfg s') (k : ∀ j ∈ saved, getX s' j = getX s j) :
    abiSavedKept s s' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h'.x2, h.x2, k 2 (by decide)]
  · rw [h'.x3, h.x3, k 3 (by decide)]
  · rw [h'.x4, h.x4, k 4 (by decide)]
  · rw [h'.x8, h.x8, k 8 (by decide)]
  · rw [h'.x9, h.x9, k 9 (by decide)]
  · rw [h'.x18, h.x18, k 18 (by decide)]
  · rw [h'.x19, h.x19, k 19 (by decide)]
  · rw [h'.x20, h.x20, k 20 (by decide)]
  · rw [h'.x21, h.x21, k 21 (by decide)]
  · rw [h'.x22, h.x22, k 22 (by decide)]
  · rw [h'.x23, h.x23, k 23 (by decide)]
  · rw [h'.x24, h.x24, k 24 (by decide)]
  · rw [h'.x25, h.x25, k 25 (by decide)]
  · rw [h'.x26, h.x26, k 26 (by decide)]
  · rw [h'.x27, h.x27, k 27 (by decide)]

theorem getX_of_abi {s s' : St} (h : Cfg s) (h' : Cfg s') (k : abiSavedKept s s') :
    ∀ j ∈ saved, getX s' j = getX s j := by
  have g := fun r hr => k r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨k2, k3, k4, k8, k9, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27⟩ := g
  rw [h'.x2, h.x2] at k2; rw [h'.x3, h.x3] at k3; rw [h'.x4, h.x4] at k4; rw [h'.x8, h.x8] at k8
  rw [h'.x9, h.x9] at k9; rw [h'.x18, h.x18] at k18; rw [h'.x19, h.x19] at k19; rw [h'.x20, h.x20] at k20
  rw [h'.x21, h.x21] at k21; rw [h'.x22, h.x22] at k22; rw [h'.x23, h.x23] at k23; rw [h'.x24, h.x24] at k24
  rw [h'.x25, h.x25] at k25; rw [h'.x26, h.x26] at k26; rw [h'.x27, h.x27] at k27
  intro j hj
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Option.some.inj k2
  · exact Option.some.inj k3
  · exact Option.some.inj k4
  · exact Option.some.inj k8
  · exact Option.some.inj k9
  · exact Option.some.inj k18
  · exact Option.some.inj k19
  · exact Option.some.inj k20
  · exact Option.some.inj k21
  · exact Option.some.inj k22
  · exact Option.some.inj k23
  · exact Option.some.inj k24
  · exact Option.some.inj k25
  · exact Option.some.inj k26
  · exact Option.some.inj k27

/-! ## The frame -/

/-- the four slots the stub writes at `F` -/
def frame (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) : Mem :=
  storeBytes (storeBytes (storeBytes (storeBytes m F (le8 ra)) (F + 8) (le8 a3)) (F + 16) (le8 sp)) (F + 24)
    (le8 a2)

theorem frame_other (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) {a : Nat} (h : a < F ∨ F + 32 ≤ a) :
    (frame m F ra a3 sp a2)[a]? = m[a]? := by
  unfold frame
  rw [other _ _ _ (by omega), other _ _ _ (by omega), other _ _ _ (by omega), other _ _ _ (by omega)]

theorem frame_0 (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) {k : Nat} (hk : k < 8) :
    (frame m F ra a3 sp a2)[F + k]? = some (ra.extractLsb' (8 * k) 8) := by
  unfold frame
  rw [other _ _ _ (by omega), other _ _ _ (by omega), other _ _ _ (by omega)]; exact slot _ _ _ hk

theorem frame_8 (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) {k : Nat} (hk : k < 8) :
    (frame m F ra a3 sp a2)[F + 8 + k]? = some (a3.extractLsb' (8 * k) 8) := by
  unfold frame
  rw [other _ _ _ (by omega), other _ _ _ (by omega)]; exact slot _ _ _ hk

theorem frame_16 (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) {k : Nat} (hk : k < 8) :
    (frame m F ra a3 sp a2)[F + 16 + k]? = some (sp.extractLsb' (8 * k) 8) := by
  unfold frame
  rw [other _ _ _ (by omega)]; exact slot _ _ _ hk

theorem frame_24 (m : Mem) (F : Nat) (ra a3 sp a2 : BitVec 64) {k : Nat} (hk : k < 8) :
    (frame m F ra a3 sp a2)[F + 24 + k]? = some (a2.extractLsb' (8 * k) 8) := by
  unfold frame; exact slot _ _ _ hk

/-! ## Word arithmetic -/

theorem bv_sub (a b : Nat) : BitVec.ofNat 64 (a + b) - BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
  rw [Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem bv_shr {w : Nat} (h : w < 2 ^ 64) : BitVec.ofNat 64 w >>> 5 = BitVec.ofNat 64 (w / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

theorem bv_shl {w : Nat} (h : w < 2 ^ 60) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem P_succ (e : BitVec 64) (i : Nat) : e + BitVec.ofNat 64 (4 * i) + 4 = e + BitVec.ofNat 64 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]; congr 1
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; rfl

theorem instr_keep {s s' : St} {pc : BitVec 64} {w : BitVec 32} (h : instrAt s pc w)
    (hm : ∀ k < 4, s'.mem[pc.toNat + k]? = s.mem[pc.toNat + k]?) : instrAt s' pc w := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨by rw [← a]; exact hm 0 (by omega), by rw [← b]; exact hm 1 (by omega),
    by rw [← c]; exact hm 2 (by omega), by rw [← d]; exact hm 3 (by omega)⟩

theorem pcOK_of {e : BitVec 64} {n i : Nat} (h : codeOK e n) (hi : i < n) : pcOK (e + BitVec.ofNat 64 (4 * i)) := by
  have := pc_toNat h (a := i) (by omega)
  obtain ⟨h1, h2, h3⟩ := h
  simp only [pcOK, this]; omega

/-! ## The stub before the call of `f` -/

theorem pre_run {s : St} (h : Cfg s) {entry : BitVec 64} {o : BitVec 20} {wb W : Nat}
    (hpc : s.regs.get? .PC = some entry) (hok : codeOK entry 18) (hc : codeAt s entry (stub o))
    (hwb : wb % 8 = 0) (hlo : 0x80000000 ≤ wb) (hhi : wb + W ≤ 0x100000000) (hW : 64 ≤ W)
    (hcd : wb + W ≤ entry.toNat ∨ entry.toNat + 72 ≤ wb)
    (x2 : getX s 2 = BitVec.ofNat 64 (wb + W)) (x12 : getX s 12 = BitVec.ofNat 64 wb) :
    ∃ s', (∀ P, runsTo s' P → runsTo s P) ∧ Cfg s' ∧
      s'.regs.get? .PC = some (entry + BitVec.ofNat 64 (4 * 12) + joff o) ∧
      getX s' 1 = entry + BitVec.ofNat 64 (4 * 13) ∧
      getX s' 2 = BitVec.ofNat 64 (wb + 2 * (8 * (W / 32))) ∧
      getX s' 12 = BitVec.ofNat 64 (wb + 8 * (W / 32)) ∧
      getX s' 13 = BitVec.ofNat 64 wb ∧
      (∀ j : Fin 32, j ≠ 1 → j ≠ 2 → j ≠ 5 → j ≠ 6 → j ≠ 12 → j ≠ 13 → getX s' j = getX s j) ∧
      s'.mem = frame s.mem (wb + 2 * (8 * (W / 32))) (getX s 1) (getX s 13) (getX s 2) (getX s 12) := by
  have hE := fun i (hi : i < 18) => pc_toNat hok (a := i) (by omega)
  have I : ∀ (s' : St), (∀ a, a < wb + 2 * (8 * (W / 32)) ∨ wb + 2 * (8 * (W / 32)) + 32 ≤ a →
      s'.mem[a]? = s.mem[a]?) → ∀ i (hi : i < 18), instrAt s' (entry + BitVec.ofNat 64 (4 * i)) ((stub o)[i]'hi) :=
    fun s' hm i hi => instr_keep (hc i hi) fun k hk => hm _ (by rw [hE i hi]; omega)
  have ok := fun i (hi : i < 18) => pcOK_of hok hi
  have t5 : (getX s 2 - getX s 12) >>> (5 : BitVec 6).toNat <<< (3 : BitVec 6).toNat = BitVec.ofNat 64 (8 * (W / 32)) := by
    show (getX s 2 - getX s 12) >>> 5 <<< 3 = _
    rw [x2, x12, bv_sub, bv_shr (by omega), bv_shl (by omega)]
  obtain ⟨s1, n0⟩ := G.step_sub h (pc := entry + BitVec.ofNat 64 (4 * 0)) (by rw [hpc]; simp) (ok 0 (by omega))
    5 2 12 (I s (fun _ _ => rfl) 0 (by omega))
  have M1 : s1.mem = s.mem := n0.mem
  obtain ⟨s2, n1⟩ := G.step_srli n0.cfg (by rw [n0.pc, P_succ]) (ok 1 (by omega)) 5 5 5
    (I s1 (fun _ _ => by rw [M1]) 1 (by omega))
  have M2 : s2.mem = s.mem := by rw [n1.mem, M1]
  obtain ⟨s3, n2⟩ := G.step_slli n1.cfg (by rw [n1.pc, P_succ]) (ok 2 (by omega)) 5 5 3
    (I s2 (fun _ _ => by rw [M2]) 2 (by omega))
  have M3 : s3.mem = s.mem := by rw [n2.mem, M2]
  obtain ⟨s4, n3⟩ := G.step_add n2.cfg (by rw [n2.pc, P_succ]) (ok 3 (by omega)) 6 12 5 (by decide)
    (I s3 (fun _ _ => by rw [M3]) 3 (by omega))
  have M4 : s4.mem = s.mem := by rw [n3.mem, M3]
  obtain ⟨s5, n4⟩ := G.step_add n3.cfg (by rw [n3.pc, P_succ]) (ok 4 (by omega)) 6 6 5 (by decide)
    (I s4 (fun _ _ => by rw [M4]) 4 (by omega))
  have M5 : s5.mem = s.mem := by rw [n4.mem, M4]
  have e5 : getX s5 5 = BitVec.ofNat 64 (8 * (W / 32)) := by
    simp (config := { decide := true }) only [getX_next n4, getX_next n3, getX_next n2, getX_next n1,
      getX_next n0, if_true, if_false]
    exact t5
  have e6 : getX s5 6 = BitVec.ofNat 64 (wb + 2 * (8 * (W / 32))) := by
    simp (config := { decide := true }) only [getX_next n4, getX_next n3, getX_next n2, getX_next n1,
      getX_next n0, if_true, if_false]
    rw [t5, x12, ← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
  have r5 : ∀ j : Fin 32, j ≠ 5 → j ≠ 6 → getX s5 j = getX s j := fun j h5 h6 => by
    simp only [getX_next n4, getX_next n3, getX_next n2, getX_next n1, getX_next n0]
    simp [h5, h6]
  have z0 : (0 : BitVec 12).signExtend 64 = 0#64 := by decide
  have z8 : (8 : BitVec 12).signExtend 64 = BitVec.ofNat 64 8 := by decide
  have z16 : (16 : BitVec 12).signExtend 64 = BitVec.ofNat 64 16 := by decide
  have z24 : (24 : BitVec 12).signExtend 64 = BitVec.ofNat 64 24 := by decide
  generalize hF : wb + 2 * (8 * (W / 32)) = F at *
  obtain ⟨s6, n5⟩ := sd_slot n4.cfg (by rw [n4.pc, P_succ]) (ok 5 (by omega)) 1 6 0
    (I s5 (fun _ _ => by rw [M5]) 5 (by omega)) (A := F) (by rw [e6, z0, BitVec.add_zero]) (by omega) (by omega)
  have M6 : s6.mem = storeBytes s.mem F (le8 (getX s 1)) := by
    rw [n5.mem, M5, r5 1 (by decide) (by decide)]
  have k6 : ∀ j, getX s6 j = getX s5 j := fun j => by rw [getX_next n5]; simp
  obtain ⟨s7, n6⟩ := sd_slot n5.cfg (by rw [n5.pc, P_succ]) (ok 6 (by omega)) 13 6 8
    (I s6 (fun a ha => by rw [M6, other _ _ _ (by omega)]) 6 (by omega)) (A := F + 8)
    (by rw [k6, e6, z8, ← BitVec.ofNat_add]) (by omega) (by omega)
  have k7 : ∀ j, getX s7 j = getX s5 j := fun j => by rw [getX_next n6, ← k6]; simp
  have M7 : s7.mem = storeBytes (storeBytes s.mem F (le8 (getX s 1))) (F + 8) (le8 (getX s 13)) := by
    rw [n6.mem, M6, k6, r5 13 (by decide) (by decide)]
  obtain ⟨s8, n7⟩ := sd_slot n6.cfg (by rw [n6.pc, P_succ]) (ok 7 (by omega)) 2 6 16
    (I s7 (fun a ha => by rw [M7, other _ _ _ (by omega), other _ _ _ (by omega)]) 7 (by omega)) (A := F + 16)
    (by rw [k7, e6, z16, ← BitVec.ofNat_add]) (by omega) (by omega)
  have k8 : ∀ j, getX s8 j = getX s5 j := fun j => by rw [getX_next n7, ← k7]; simp
  have M8 : s8.mem = storeBytes (storeBytes (storeBytes s.mem F (le8 (getX s 1))) (F + 8) (le8 (getX s 13)))
      (F + 16) (le8 (getX s 2)) := by
    rw [n7.mem, M7, k7, r5 2 (by decide) (by decide)]
  obtain ⟨s9, n8⟩ := sd_slot n7.cfg (by rw [n7.pc, P_succ]) (ok 8 (by omega)) 12 6 24
    (I s8 (fun a ha => by rw [M8, other _ _ _ (by omega), other _ _ _ (by omega), other _ _ _ (by omega)]) 8
      (by omega)) (A := F + 24)
    (by rw [k8, e6, z24, ← BitVec.ofNat_add]) (by omega) (by omega)
  have k9 : ∀ j, getX s9 j = getX s5 j := fun j => by rw [getX_next n8, ← k8]; simp
  have M9 : s9.mem = frame s.mem F (getX s 1) (getX s 13) (getX s 2) (getX s 12) := by
    rw [n8.mem, M8, k8, r5 12 (by decide) (by decide)]; rfl
  have H9 : ∀ (s' : St), s'.mem = s9.mem → ∀ a, a < F ∨ F + 32 ≤ a → s'.mem[a]? = s.mem[a]? :=
    fun s' e a ha => by rw [e, M9, frame_other _ _ _ _ _ _ ha]
  obtain ⟨s10, n9⟩ := G.step_addi n8.cfg (by rw [n8.pc, P_succ]) (ok 9 (by omega)) 13 12 0
    (I s9 (H9 s9 rfl) 9 (by omega))
  obtain ⟨s11, n10⟩ := G.step_add n9.cfg (by rw [n9.pc, P_succ]) (ok 10 (by omega)) 12 12 5 (by decide)
    (I s10 (H9 s10 n9.mem) 10 (by omega))
  obtain ⟨s12, n11⟩ := G.step_addi n10.cfg (by rw [n10.pc, P_succ]) (ok 11 (by omega)) 2 6 0
    (I s11 (H9 s11 (by rw [n10.mem, n9.mem])) 11 (by omega))
  obtain ⟨s13, n12⟩ := G.step_jal n11.cfg (by rw [n11.pc, P_succ]) (ok 12 (by omega)) 1 o
    (I s12 (H9 s12 (by rw [n11.mem, n10.mem, n9.mem])) 12 (by omega))
  refine ⟨s13, fun P hP => runsTo_next n0 (runsTo_next n1 (runsTo_next n2 (runsTo_next n3 (runsTo_next n4
    (runsTo_next n5 (runsTo_next n6 (runsTo_next n7 (runsTo_next n8 (runsTo_next n9 (runsTo_next n10
    (runsTo_next n11 (runsTo_next n12 hP)))))))))))), n12.cfg, n12.pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getX_next n12, if_pos (by decide), P_succ]
  · simp (config := { decide := true }) only [getX_next n12, getX_next n11, getX_next n10, getX_next n9,
      if_true, if_false]
    rw [k9, e6, z0, BitVec.add_zero]
  · simp (config := { decide := true }) only [getX_next n12, getX_next n11, getX_next n10, getX_next n9,
      if_true, if_false]
    rw [k9, k9, e5, r5 12 (by decide) (by decide), x12, ← BitVec.ofNat_add]
  · simp (config := { decide := true }) only [getX_next n12, getX_next n11, getX_next n10, getX_next n9,
      if_true, if_false]
    rw [k9, r5 12 (by decide) (by decide), x12, z0, BitVec.add_zero]
  · intro j h1 h2 h5 h6 h12 h13
    simp only [getX_next n12, getX_next n11, getX_next n10, getX_next n9]
    simp only [h1, h2, h12, h13, false_and, if_false]
    rw [k9, r5 j h5 h6]
  · rw [n12.mem, n11.mem, n10.mem, n9.mem, M9]

end Nano.Link

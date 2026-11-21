/- The L2 group of `JT.JArmBits` (Nano/Run/JArmView.lean): the accessor layer `e25` / `e21` / `e22` / `e23` / `e24` of
the nano J → AArch64 translator on the RISC-V words `encG j` of `JOK` instructions.
`jab_l2_lt`, `jab_l2_big`, `jab_l2_kind`, `jab_l2_A`, `jab_l2_B`, `jab_l2_C`, `jab_l2_op`, `jab_l2_zero` are the fields
as stated. -/
import Nano.Run.JArmView
import Nano.Run.CjUnique
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-- evaluation of the closed tests of the accessor layer -/
macro "jred" : tactic => `(tactic| simp (config := { decide := true }) only [reduceIte])

/-! ## the bodies of `e21` / `e22` / `e23` as functions of the word and its kind -/
def gA (v k : UInt64) : UInt64 :=
  if k == 5 then e5 v else if k == 6 then e5 v else if 8 < k then (if k < 13 then e4 v else e2 v) else e2 v
def gB (v k : UInt64) : UInt64 := if k == 13 then 0 else if 8 < k then (if k < 13 then e5 v else e4 v) else e4 v
def gC (v k : UInt64) : UInt64 :=
  if k == 1 then e6 v else if k == 4 then e6 v else if k == 7 then e6 v
  else if k == 2 then (v >>> 20) &&& e_4 else if k == 3 then (v >>> 20) &&& e_4
  else if k == 5 then e7 v else if k == 6 then e7 v
  else if k == 8 then e5 v
  else if k == 13 then e13 (e9 v)
  else if 8 < k then (if k < 13 then e13 (e8 v) else 0) else 0

theorem e21_f (c : Buf) (i : UInt64) : e21 c i = gA (bget c i) (e25 (bget c i)) := rfl
theorem e22_f (c : Buf) (i : UInt64) : e22 c i = gB (bget c i) (e25 (bget c i)) := rfl
theorem e23_f (c : Buf) (i : UInt64) : e23 c i = gC (bget c i) (e25 (bget c i)) := rfl

/-! ## the field extractors (they are `RA.o0` … `RA.o8` of the rv2arm decoder) -/
theorem x1 {v : UInt64} {r : Nat} (h : v.toNat % 128 = r) : e1 v = r.toUInt64 := ArmRA.o0_eq h
theorem x2 {v : UInt64} {r : Nat} (h : v.toNat / 128 % 32 = r) : e2 v = r.toUInt64 := ArmRA.o1_eq h
theorem x3 {v : UInt64} {r : Nat} (h : v.toNat / 4096 % 8 = r) : e3 v = r.toUInt64 := ArmRA.o2_eq h
theorem x4 {v : UInt64} {r : Nat} (h : v.toNat / 32768 % 32 = r) : e4 v = r.toUInt64 := ArmRA.o3_eq h
theorem x5 {v : UInt64} {r : Nat} (h : v.toNat / 1048576 % 32 = r) : e5 v = r.toUInt64 := ArmRA.o4_eq h
theorem x6 {v : UInt64} {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) (h : v.toNat / 2 ^ 20 = (z % 4096).toNat) :
    e6 v = iu z := ArmRA.o5_eq h1 h2 h
theorem x7 {v : UInt64} {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) (hv : v.toNat < 2 ^ 32)
    (h : v.toNat / 2 ^ 25 * 32 + v.toNat / 128 % 32 = (z % 4096).toNat) : e7 v = iu z := ArmRA.o6_eq h1 h2 hv h
theorem xsh {v : UInt64} {k r : Nat} (hk : k < 64) (h : v.toNat / 2 ^ k = r) : v >>> k.toUInt64 = r.toUInt64 :=
  ArmRA.shr_eq hk h
theorem xC {v : UInt64} {sh : Nat} (h : v.toNat / 2 ^ 20 % 64 = sh) : (v >>> 20) &&& e_4 = sh.toUInt64 := by
  apply ArmRA.u64; show ((v >>> 20) &&& 63).toNat = _; wnorm; omega

/-- a byte offset `4 * o` in instructions -/
theorem x13 {o : Int} (h1 : -2 ^ 18 ≤ o) (h2 : o < 2 ^ 18) : e13 (iu (4 * o)) = iu o := by
  have hn := iu_toNat (4 * o)
  apply ArmRA.u64
  rw [iu_toNat]
  unfold e13 e14
  by_cases ho : o < 0
  · have hl : (9223372036854775807 : UInt64) < iu (4 * o) := by
      rw [UInt64.lt_iff_toNat_lt, hn]; simp; omega
    simp (config := { decide := true }) only [hl, reduceIte]
    simp only [e_0, UInt64.toNat_sub, UInt64.toNat_shiftRight, hn, Nat.shiftRight_eq_div_pow]
    simp
    omega
  · have hl : ¬ (9223372036854775807 : UInt64) < iu (4 * o) := by
      rw [UInt64.lt_iff_toNat_lt, hn]; simp; omega
    simp (config := { decide := true }) only [hl, reduceIte]
    simp only [UInt64.toNat_shiftRight, hn, Nat.shiftRight_eq_div_pow]
    simp
    omega

theorem and3_e (o : Int) : (iu (4 * o) &&& e_5 == 0) = true := ArmRA.and3_iu o

/-- `e25` without its range test -/
def e25o (v : UInt64) : UInt64 :=
  let p := e1 v;
  let f := e3 v;
  if p == 19 then
    (if f == 0 then 1 else if f == 1 then (if (v >>> 26) == 0 then 2 else 0)
     else if f == 5 then (if (v >>> 26) == 0 then 3 else 0) else 0)
  else if p == 3 then (if f == 3 then 4 else if f == 4 then 7 else 0)
  else if p == 35 then (if f == 3 then 5 else if f == 0 then 6 else 0)
  else if p == 51 then (if e15 f (v >>> 25) == 0 then 0 else 8)
  else if p == 99 then
    (if (e8 v &&& e_5) == 0 then
      (if f == 0 then 9 else if f == 1 then 10 else if f == 6 then 11 else if f == 7 then 12 else 0)
     else 0)
  else if p == 111 then (if (e9 v &&& e_5) == 0 then 13 else 0)
  else if p == 103 then (if f == 0 then (if (v >>> 20) == 0 then (if e2 v == 0 then 14 else 0) else 0) else 0)
  else 0

theorem e25_o {v : UInt64} (h : v.toNat < 2 ^ 32) : e25 v = e25o v := by
  have hl : ¬ (4294967295 : UInt64) < v := by
    rw [UInt64.lt_iff_toNat_lt]; simp; omega
  show (if 4294967295 < v then 0 else e25o v) = _
  rw [if_neg hl]

/-! ## the accessor layer, per constructor -/
theorem core0 (j : J) (hj : JOK j) :
    e25o (encG j) = jk j ∧ gA (encG j) (jk j) = jA j ∧ gB (encG j) (jk j) = jB j ∧
      gC (encG j) (jk j) = jC j := by
  obtain ⟨g, hjal⟩ := hj
  cases j with
  | addi rd rs imm =>
    have hV := CjU.V_addi _ _ _ g
    obtain ⟨h1, h2, h3, h4⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 19 := x1 (r := 19) (by omega)
    have a3 : e3 v = 0 := x3 (r := 0) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x6 h3 h4 (by omega)
  | ld rd rs imm =>
    have hV := CjU.V_ld _ _ _ g
    obtain ⟨h1, h2, h3, h4⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 3 := x1 (r := 3) (by omega)
    have a3 : e3 v = 3 := x3 (r := 3) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x6 h3 h4 (by omega)
  | lbu rd rs imm =>
    have hV := CjU.V_lbu _ _ _ g
    obtain ⟨h1, h2, h3, h4⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 3 := x1 (r := 3) (by omega)
    have a3 : e3 v = 4 := x3 (r := 4) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x6 h3 h4 (by omega)
  | sd r2 r1 imm =>
    have hV := CjU.V_sd _ _ _ g
    obtain ⟨h1, h2, h3, h4⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 35 := x1 (r := 35) (by omega)
    have a3 : e3 v = 3 := x3 (r := 3) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x5 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x7 h3 h4 (by omega) (by omega)
  | sb r2 r1 imm =>
    have hV := CjU.V_sb _ _ _ g
    obtain ⟨h1, h2, h3, h4⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 35 := x1 (r := 35) (by omega)
    have a3 : e3 v = 0 := x3 (r := 0) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x5 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x7 h3 h4 (by omega) (by omega)
  | slli rd rs sh =>
    have hV := CjU.V_slli _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 19 := x1 (r := 19) (by omega)
    have a3 : e3 v = 1 := x3 (r := 1) (by omega)
    have a4 : v >>> 26 = 0 := xsh (k := 26) (r := 0) (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a4, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact xC (by omega)
  | srli rd rs sh =>
    have hV := CjU.V_srli _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 19 := x1 (r := 19) (by omega)
    have a3 : e3 v = 5 := x3 (r := 5) (by omega)
    have a4 : v >>> 26 = 0 := xsh (k := 26) (r := 0) (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a4, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact xC (by omega)
  | jalr rd rs =>
    have hV := CjU.V_jalr _ _ g
    obtain ⟨h1, h2⟩ := g
    subst h1
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 103 := x1 (r := 103) (by omega)
    have a3 : e3 v = 0 := x3 (r := 0) (by omega)
    have a4 : v >>> 20 = 0 := xsh (k := 20) (r := 0) (by omega) (by omega)
    have a2 : e2 v = 0 := x2 (r := 0) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a4, a2, jk]; jred
    · simp only [gA, jk, jA]; jred; exact a2
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred
  | alu op rd a b =>
    have hV := CjU.V_alu _ _ _ _ g
    obtain ⟨h1, h2, h3, h4, h5⟩ := g
    obtain ⟨f1, -, -, -, f5, f6, -⟩ := ArmRA.alu_facts op h4 h5
    generalize encG _ = v at hV ⊢
    have a1 : e1 v = 51 := x1 (r := 51) (by omega)
    have a3 : e3 v = (aluF op).2 := by
      rw [x3 (r := (aluF op).2.toNat) (by omega)]; exact ArmRA.u64 (ArmRA.tU (by omega))
    have a4 : v >>> 25 = (aluF op).1 := by
      have := xsh (v := v) (k := 25) (r := (aluF op).1.toNat) (by omega) (by omega)
      exact this.trans (ArmRA.u64 (ArmRA.tU (by omega)))
    have a5 : e15 (aluF op).2 (aluF op).1 = op.toUInt64 := f1
    have a6 : (op.toUInt64 == 0) = false := by rw [ArmRA.beq0 (by omega)]; simp; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a4, a5, a6, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 (by omega)
    · simp only [gB, jk, jB]; jred; exact x4 (by omega)
    · simp only [gC, jk, jC]; jred; exact x5 (by omega)
  | beq a b o =>
    have hV := CjU.V_beq _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    unfold CjU.VB at hV
    generalize encG _ = v at hV ⊢
    obtain ⟨q0, q2, q3, q4⟩ := ArmRA.B_fields h1 h2 (by omega) hV
    have a1 : e1 v = 99 := x1 (r := 99) q0
    have a3 : e3 v = 0 := x3 (r := 0) q2
    have a8 : e8 v = iu (4 * o) := ArmRA.br_o7 (by omega) (by omega) (by omega) h1 h2 hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a8, and3_e, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x4 q3
    · simp only [gB, jk, jB]; jred; exact x5 q4
    · simp only [gC, jk, jC]; jred; rw [a8]; exact x13 (by omega) (by omega)
  | bne a b o =>
    have hV := CjU.V_bne _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    unfold CjU.VB at hV
    generalize encG _ = v at hV ⊢
    obtain ⟨q0, q2, q3, q4⟩ := ArmRA.B_fields h1 h2 (by omega) hV
    have a1 : e1 v = 99 := x1 (r := 99) q0
    have a3 : e3 v = 1 := x3 (r := 1) q2
    have a8 : e8 v = iu (4 * o) := ArmRA.br_o7 (by omega) (by omega) (by omega) h1 h2 hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a8, and3_e, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x4 q3
    · simp only [gB, jk, jB]; jred; exact x5 q4
    · simp only [gC, jk, jC]; jred; rw [a8]; exact x13 (by omega) (by omega)
  | bltu a b o =>
    have hV := CjU.V_bltu _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    unfold CjU.VB at hV
    generalize encG _ = v at hV ⊢
    obtain ⟨q0, q2, q3, q4⟩ := ArmRA.B_fields h1 h2 (by omega) hV
    have a1 : e1 v = 99 := x1 (r := 99) q0
    have a3 : e3 v = 6 := x3 (r := 6) q2
    have a8 : e8 v = iu (4 * o) := ArmRA.br_o7 (by omega) (by omega) (by omega) h1 h2 hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a8, and3_e, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x4 q3
    · simp only [gB, jk, jB]; jred; exact x5 q4
    · simp only [gC, jk, jC]; jred; rw [a8]; exact x13 (by omega) (by omega)
  | bgeu a b o =>
    have hV := CjU.V_bgeu _ _ _ g
    obtain ⟨h1, h2, h3⟩ := g
    unfold CjU.VB at hV
    generalize encG _ = v at hV ⊢
    obtain ⟨q0, q2, q3, q4⟩ := ArmRA.B_fields h1 h2 (by omega) hV
    have a1 : e1 v = 99 := x1 (r := 99) q0
    have a3 : e3 v = 7 := x3 (r := 7) q2
    have a8 : e8 v = iu (4 * o) := ArmRA.br_o7 (by omega) (by omega) (by omega) h1 h2 hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a3, a8, and3_e, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x4 q3
    · simp only [gB, jk, jB]; jred; exact x5 q4
    · simp only [gC, jk, jC]; jred; rw [a8]; exact x13 (by omega) (by omega)
  | jal rd o =>
    have hV := CjU.V_jal _ _ g
    have h1 : rd < 32 := g
    obtain ⟨b1, b2⟩ := hjal rd o rfl
    obtain ⟨q0, q1, q2, q3⟩ := ArmRA.J_fields h1 (by omega) (by omega) (by omega) hV
    generalize encG _ = v at hV q0 q1 q2 q3 ⊢
    have a1 : e1 v = 111 := x1 (r := 111) q0
    have a9 : e9 v = iu (4 * o) := ArmRA.o8_eq (by omega) (by omega) q2 q3
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [e25o, a1, a9, and3_e, jk]; jred
    · simp only [gA, jk, jA]; jred; exact x2 q1
    · simp only [gB, jk, jB]; jred
    · simp only [gC, jk, jC]; jred; rw [a9]; exact x13 b1 b2

/-! ## the fields of `JArmBits` -/

theorem jab_l2_lt : ∀ j : J, JOK j → (encG j).toNat < 2 ^ 32 := fun j hj => ArmRA.encG_lt j hj.1

theorem core (j : J) (hj : JOK j) :
    e25 (encG j) = jk j ∧ gA (encG j) (jk j) = jA j ∧ gB (encG j) (jk j) = jB j ∧
      gC (encG j) (jk j) = jC j := by
  rw [e25_o (jab_l2_lt j hj)]; exact core0 j hj

theorem jab_l2_big : ∀ v : UInt64, 4294967295 < v → e25 v = 0 := by
  intro v h
  show (if 4294967295 < v then 0 else e25o v) = _
  rw [if_pos h]

theorem jab_l2_kind : ∀ j : J, JOK j → e25 (encG j) = jk j := fun j hj => (core j hj).1

theorem jab_l2_A : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e21 c i = jA j := by
  intro c i j h hj
  rw [e21_f, h, (core j hj).1]; exact (core j hj).2.1

theorem jab_l2_B : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e22 c i = jB j := by
  intro c i j h hj
  rw [e22_f, h, (core j hj).1]; exact (core j hj).2.2.1

theorem jab_l2_C : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e23 c i = jC j := by
  intro c i j h hj
  rw [e23_f, h, (core j hj).1]; exact (core j hj).2.2.2

theorem e24_f (c : Buf) (i : UInt64) :
    e24 c i = if e25 (bget c i) == 8 then e15 (e3 (bget c i)) (bget c i >>> 25) else 0 := rfl

theorem jab_l2_op : ∀ (c : Buf) (i : UInt64) (j : J), bget c i = encG j → JOK j → e24 c i = jop j := by
  intro c i j h hj
  rw [e24_f, h, jab_l2_kind j hj]
  cases j with
  | alu op rd a b =>
    obtain ⟨g, -⟩ := hj
    have hV := CjU.V_alu _ _ _ _ g
    obtain ⟨h1, h2, h3, h4, h5⟩ := g
    obtain ⟨f1, -, -, -, f5, f6, -⟩ := ArmRA.alu_facts op h4 h5
    simp only [jk, jop]; jred
    generalize encG _ = v at hV ⊢
    have a3 : e3 v = (aluF op).2 := by
      rw [x3 (r := (aluF op).2.toNat) (by omega)]; exact ArmRA.u64 (ArmRA.tU (by omega))
    have a4 : v >>> 25 = (aluF op).1 := by
      have := xsh (v := v) (k := 25) (r := (aluF op).1.toNat) (by omega) (by omega)
      exact this.trans (ArmRA.u64 (ArmRA.tU (by omega)))
    rw [a3, a4]; exact f1
  | _ => simp only [jk, jop]; jred

theorem jab_l2_zero : ∀ (c : Buf) (i : UInt64), bget c i = 0 →
    e21 c i = 0 ∧ e22 c i = 0 ∧ e23 c i = 0 ∧ e24 c i = 0 := by
  intro c i h
  have hk : e25 0 = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e21_f, h, hk]; decide
  · rw [e22_f, h, hk]; decide
  · rw [e23_f, h, hk]; decide
  · rw [e24_f, h, hk]; decide

end JT

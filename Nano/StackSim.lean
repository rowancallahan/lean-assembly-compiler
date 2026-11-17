/- Route (a): one record step of `genR`'s records is one retired instruction of the Sail model (`sim`), `ret` returns
(`sim_halt`), and runs of the record machine are Sail runs (`sim_star`).  Per family: `case_*`, from the generic
step lemmas `Riscv/Steps/Gen*.lean` and the family's word (`Nano/StackFam.lean`). -/
import Nano.StackSail
import Riscv.Back.Implements1

set_option linter.unusedVariables false

namespace Nano.S
open Proven Proven.G Nano Nano.R Nano.F

theorem sx12_sext_n : ∀ n, n < 256 → (sx12 n.toUInt8).signExtend 64 = sext8 n.toUInt8 := by decide +kernel
theorem sx12_sext (c : UInt8) : (sx12 c).signExtend 64 = sext8 c := by
  have := sx12_sext_n c.toNat c.toNat_lt; simpa using this
theorem sx_small : ∀ n, n < 256 → (BitVec.ofNat 12 n).signExtend 64 = BitVec.ofNat 64 n := by decide +kernel
theorem sx_8 : ∀ n, n < 256 → (BitVec.ofNat 12 (8 * n)).signExtend 64 = BitVec.ofNat 64 (8 * n) := by decide +kernel
theorem cat_rd64 (m : Nat → UInt8) (A : Nat) :
    ((m (A + 7)).toBitVec ++ (m (A + 6)).toBitVec ++ (m (A + 5)).toBitVec ++ (m (A + 4)).toBitVec ++
      (m (A + 3)).toBitVec ++ (m (A + 2)).toBitVec ++ (m (A + 1)).toBitVec ++ (m A).toBitVec : BitVec 64) = rd64 m A := by
  generalize hc : ((m (A + 7)).toBitVec ++ (m (A + 6)).toBitVec ++ (m (A + 5)).toBitVec ++ (m (A + 4)).toBitVec ++
      (m (A + 3)).toBitVec ++ (m (A + 2)).toBitVec ++ (m (A + 1)).toBitVec ++ (m A).toBitVec : BitVec 64) = c
  have h1 := Proven.Mach.Riscv.le8_cat8 (m A).toBitVec (m (A + 1)).toBitVec (m (A + 2)).toBitVec (m (A + 3)).toBitVec
    (m (A + 4)).toBitVec (m (A + 5)).toBitVec (m (A + 6)).toBitVec (m (A + 7)).toBitVec
  rw [hc] at h1
  have h2 : (leN 8 c.toNat).map (·.toBitVec) = (rdL m A 8).map (·.toBitVec) := by
    rw [← le8_leN]; exact h1.trans (by simp [rdL, List.range, List.range.loop])
  have h3 : leN 8 c.toNat = rdL m A 8 := (List.map_inj_right (fun x y h => UInt8.toBitVec_inj.mp h)).mp h2
  unfold rd64; rw [← h3, unle_leN]; apply BitVec.eq_of_toNat_eq; simp
  exact (Nat.mod_eq_of_lt (by have := c.isLt; simpa using this)).symm

theorem uc (c : UInt8) : c.toNat.toUInt8 = c := by simp

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {C : Ctx} {s s' : R.St} {t : Proven.St} {rest : List UInt8}

theorem toNat_W (hC : C.Ok) (hR : Rel C s t) : (s.get 12).toNat = C.W := by
  rw [hR.r12]; have := hC.whi; have := hC.wsp; simp; omega
theorem toNat_SP (hC : C.Ok) (hR : Rel C s t) : (s.get 2).toNat = C.SP := by
  rw [hR.r2]; have := hC.whi; simp; omega

/-- `addi rd, rs1, sext c` -/
theorem case_addi (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1)
    (hw : ∀ n, n < 256 → asm [0, a, b, n.toUInt8] = wb (encI 0 (sx12 n.toUInt8).toNat rd rs1))
    (hd : C.P.drop (4 * s.pc) = 0 :: a :: b :: c :: rest) (he : exec s 0 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc (pcok_of hC hd) rd rs1 (sx12 c) hi
  have e : Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat (s.get b.toNat + sext8 c)) = .next s' := he
  cases e
  rw [hR.x rs1, sx12_sext] at hN
  rw [ha, hb]
  exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩

/-- `addi rd, rs1, 8c` -/
theorem case_addi8 (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1)
    (hw : ∀ n, n < 256 → asm [8, a, b, n.toUInt8] = wb (encI 0 (BitVec.ofNat 12 (8 * n)).toNat rd rs1))
    (hd : C.P.drop (4 * s.pc) = 8 :: a :: b :: c :: rest) (he : exec s 8 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ hi
  have e : Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat
    (s.get b.toNat + BitVec.ofNat 64 (8 * c.toNat))) = .next s' := he
  cases e
  rw [hR.x rs1, sx_8 _ c.toNat_lt] at hN
  rw [ha, hb]
  exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩

/-- `ori rd, rs1, c` -/
theorem case_ori (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h0 : rd ≠ 0) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1)
    (hw : ∀ n, n < 256 → asm [6, a, b, n.toUInt8] = wb (encI 6 (BitVec.ofNat 12 n).toNat rd rs1))
    (hd : C.P.drop (4 * s.pc) = 6 :: a :: b :: c :: rest) (he : exec s 6 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  obtain ⟨t', hN⟩ := G.step_ori hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ h0 hi
  have e : Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat
    (s.get b.toNat ||| BitVec.ofNat 64 c.toNat)) = .next s' := he
  cases e
  rw [hR.x rs1, sx_small _ c.toNat_lt] at hN
  rw [ha, hb]
  exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩

/-- `slli rd, rs1, c` -/
theorem case_slli (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1) (hc : c < 64)
    (hw : ∀ n, n < 64 → asm [1, a, b, n.toUInt8] = wb (encI 1 (0 <<< 6 ||| (BitVec.ofNat 6 n).toNat) rd rs1))
    (hd : C.P.drop (4 * s.pc) = 1 :: a :: b :: c :: rest) (he : exec s 1 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hc' : c.toNat < 64 := hc
  have hi := instr_of hC hR hd (by have := hw c.toNat hc'; rwa [uc] at this)
  obtain ⟨t', hN⟩ := G.step_slli hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ hi
  have e : Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat (s.get b.toNat <<< c.toNat)) = .next s' := he
  cases e
  rw [hR.x rs1, show (BitVec.ofNat 6 c.toNat).toNat = c.toNat by simp; omega] at hN
  rw [ha, hb]
  exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩

/-- `srli rd, rs1, c` -/
theorem case_srli (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1) (hc : c < 64)
    (hw : ∀ n, n < 64 → asm [5, a, b, n.toUInt8] = wb (encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 n).toNat) rd rs1))
    (hd : C.P.drop (4 * s.pc) = 5 :: a :: b :: c :: rest) (he : exec s 5 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hc' : c.toNat < 64 := hc
  have hi := instr_of hC hR hd (by have := hw c.toNat hc'; rwa [uc] at this)
  obtain ⟨t', hN⟩ := G.step_srli hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ hi
  have e : Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat (s.get b.toNat >>> c.toNat)) = .next s' := he
  cases e
  rw [hR.x rs1, show (BitVec.ofNat 6 c.toNat).toNat = c.toNat by simp; omega] at hN
  rw [ha, hb]
  exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩

/-- `or/add/sub/mul t0, t0, t1` -/
theorem case_r (hC : C.Ok) (hR : Rel C s t) {op : UInt8} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hex : ∀ s : R.St, exec s op 5 5 6 = .next ((({ s with pc := s.pc + 1 } : R.St)).set 5 (f (s.get 5) (s.get 6))))
    {w : BitVec 32} (hw : asm [op, 5, 5, 6] = wb w)
    (hstep : ∀ (t : Proven.St) (h : Cfg t) {pc : BitVec 64} (hpc : t.regs.get? .PC = some pc) (hok : pcOK pc),
      instrAt t pc w → ∃ t', Next t t' (pc + 4) 5 (f (getX t 5) (getX t 6)) t.mem)
    (hd : C.P.drop (4 * s.pc) = op :: 5 :: 5 :: 6 :: rest) (he : exec s op 5 5 6 = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd hw
  obtain ⟨t', hN⟩ := hstep t hR.cfg hR.pc (pcok_of hC hd) hi
  rw [hex] at he; cases he
  rw [hR.x 5, hR.x 6] at hN
  exact ⟨t', hN.ret, rel_reg (rd := 5) hR hN (by decide) (by decide) (by decide)⟩

/-- `ld rd, 8c(rs1)` -/
theorem case_ld (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1)
    (hw : ∀ n, n < 256 → asm [3, a, b, n.toUInt8] = wb (encL 3 (BitVec.ofNat 12 (8 * n)) rd rs1))
    (hd : C.P.drop (4 * s.pc) = 3 :: a :: b :: c :: rest) (he : exec s 3 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  generalize hA : (s.get b.toNat + BitVec.ofNat 64 (8 * c.toNat)).toNat = A
  have e : (if WOk s A then Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat (rd64 s.m A)) else .stuck) =
    .next s' := by rw [← hA]; exact he
  by_cases hv : WOk s A
  · rw [if_pos hv] at e; cases e
    obtain ⟨v1, v2, v3⟩ := hv
    rw [toNat_W hC hR] at v1; rw [toNat_SP hC hR] at v2
    have hwl := hC.wlo; have hwh := hC.whi
    have hA64 : (BitVec.ofNat 64 A).toNat = A := by simp; omega
    have hm : ∀ i, i < 8 → t.mem[(BitVec.ofNat 64 A).toNat + i]? = some (s.m (A + i)).toBitVec := fun i hi => by
      rw [hA64]; exact hR.mem _ (.inl ⟨by omega, by omega⟩)
    obtain ⟨t', hN⟩ := G.step_ld hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ hi
      (A := BitVec.ofNat 64 A) (by rw [hR.x rs1, sx_8 _ c.toNat_lt, ← hb, ← hA, ofNat_toNat64])
      (by rw [hA64]; omega) (by rw [hA64]; omega)
      (by have := hm 0 (by decide); simpa using this) (hm 1 (by decide)) (hm 2 (by decide)) (hm 3 (by decide))
      (hm 4 (by decide)) (hm 5 (by decide)) (hm 6 (by decide)) (hm 7 (by decide))
    rw [cat_rd64] at hN
    rw [ha]
    exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩
  · rw [if_neg hv] at e; cases e

/-- `lbu rd, c(rs1)` -/
theorem case_lbu (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rd rs1 : Fin 32) (ha : a.toNat = rd.val)
    (hb : b.toNat = rs1.val) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2) (h1 : rd.val ≠ 1)
    (hw : ∀ n, n < 256 → asm [4, a, b, n.toUInt8] = wb (encL 4 (BitVec.ofNat 12 n) rd rs1))
    (hd : C.P.drop (4 * s.pc) = 4 :: a :: b :: c :: rest) (he : exec s 4 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  generalize hA : (s.get b.toNat + BitVec.ofNat 64 c.toNat).toNat = A
  have e : (if IOk s A then Out.next ((({ s with pc := s.pc + 1 } : R.St)).set a.toNat
      (BitVec.ofNat 64 (s.m A).toNat)) else .stuck) = .next s' := by rw [← hA]; exact he
  by_cases hv : IOk s A
  · rw [if_pos hv] at e; cases e
    obtain ⟨v1, v2⟩ := hv
    rw [hR.g] at v1 v2; simp only at v1 v2
    have hil := hC.ilo; have hih := hC.ihi
    have hA64 : (BitVec.ofNat 64 A).toNat = A := by simp; omega
    obtain ⟨t', hN⟩ := G.step_lbu hR.cfg hR.pc (pcok_of hC hd) rd rs1 _ hi
      (A := BitVec.ofNat 64 A) (by rw [hR.x rs1, sx_small _ c.toNat_lt, ← hb, ← hA, ofNat_toNat64])
      (by rw [hA64]; omega) (by rw [hA64]; exact hR.mem _ (.inr (.inr ⟨v1, v2⟩)))
    rw [show ((s.m A).toBitVec.setWidth 64 : BitVec 64) = BitVec.ofNat 64 (s.m A).toNat by
      apply BitVec.eq_of_toNat_eq; simp] at hN
    rw [ha]
    exact ⟨t', hN.ret, rel_reg hR hN h12 h2 h1⟩
  · rw [if_neg hv] at e; cases e

/-- `sd rs2, 8c(rs1)` -/
theorem case_sd (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rs2 rs1 : Fin 32) (ha : a.toNat = rs2.val)
    (hb : b.toNat = rs1.val)
    (hw : ∀ n, n < 256 → asm [11, a, b, n.toUInt8] = wb (encS 3 (BitVec.ofNat 12 (8 * n)) rs2 rs1))
    (hd : C.P.drop (4 * s.pc) = 11 :: a :: b :: c :: rest) (he : exec s 11 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd (by have := hw c.toNat c.toNat_lt; rwa [uc] at this)
  generalize hA : (s.get b.toNat + BitVec.ofNat 64 (8 * c.toNat)).toNat = A
  have e : (if WOk s A then Out.next { s with pc := s.pc + 1, m := wr64 s.m A (s.get a.toNat) } else .stuck) =
    .next s' := by rw [← hA]; exact he
  by_cases hv : WOk s A
  · rw [if_pos hv] at e; cases e
    obtain ⟨v1, v2, v3⟩ := hv
    rw [toNat_W hC hR] at v1; rw [toNat_SP hC hR] at v2
    have hwl := hC.wlo; have hwh := hC.whi
    have hA64 : (BitVec.ofNat 64 A).toNat = A := by simp; omega
    obtain ⟨t', hN⟩ := G.step_sd hR.cfg hR.pc (pcok_of hC hd) rs2 rs1 _ hi
      (A := BitVec.ofNat 64 A) (by rw [hR.x rs1, sx_8 _ c.toNat_lt, ← hb, ← hA, ofNat_toNat64])
      (by rw [hA64]; omega) (by rw [hA64]; omega)
    rw [hA64, hR.x rs2] at hN
    rw [ha]
    exact ⟨t', hN.ret, rel_sd hR ⟨v1, v2⟩ hN⟩
  · rw [if_neg hv] at e; cases e

/-- `sb rs2, c(rs1)` -/
theorem case_sb (hC : C.Ok) (hR : Rel C s t) {a b c : UInt8} (rs2 rs1 : Fin 32) (ha : a.toNat = rs2.val)
    (hb : b.toNat = rs1.val) (hc : c < 32)
    (hw : ∀ n, n < 32 → asm [16, a, b, n.toUInt8] = wb (encS 0 (BitVec.ofNat 12 n) rs2 rs1))
    (hd : C.P.drop (4 * s.pc) = 16 :: a :: b :: c :: rest) (he : exec s 16 a b c = .next s') :
    ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hc' : c.toNat < 32 := hc
  have hi := instr_of hC hR hd (by have := hw c.toNat hc'; rwa [uc] at this)
  generalize hA : (s.get b.toNat + BitVec.ofNat 64 c.toNat).toNat = A
  have e : (if OOk s A then Out.next { s with pc := s.pc + 1, m := wrL s.m A [UInt8.ofBitVec ((s.get a.toNat).setWidth 8)] }
    else .stuck) = .next s' := by rw [← hA]; exact he
  by_cases hv : OOk s A
  · rw [if_pos hv] at e; cases e
    obtain ⟨v1, v2⟩ := hv
    rw [hR.g] at v1 v2; simp only at v1 v2
    have hol := hC.olo; have hoh := hC.ohi
    have hA64 : (BitVec.ofNat 64 A).toNat = A := by simp; omega
    obtain ⟨t', hN⟩ := G.step_sb hR.cfg hR.pc (pcok_of hC hd) rs2 rs1 _ hi
      (A := BitVec.ofNat 64 A) (by rw [hR.x rs1, sx_small _ (by omega), ← hb, ← hA, ofNat_toNat64])
      (by rw [hA64]; omega)
    rw [hA64, hR.x rs2] at hN
    rw [ha]
    exact ⟨t', hN.ret, rel_sb hR ⟨v1, by simpa using v2⟩ hN⟩
  · rw [if_neg hv] at e; cases e

theorem boff6 : boff 6#12 = BitVec.ofNat 64 (4 * 3) := by decide

/-- `bgeu t6, a2, +12` -/
theorem case_bgeu (hC : C.Ok) (hR : Rel C s t) (hd : C.P.drop (4 * s.pc) = 7 :: 0 :: 31 :: 12 :: rest)
    (he : exec s 7 0 31 12 = .next s') : ∃ t', Retires t t' ∧ Rel C s' t' := by
  have hi := instr_of hC hR hd w_bgeu
  have e : Out.next (if s.get 12 ≤ s.get 31 then { s with pc := s.pc + 3 } else { s with pc := s.pc + 1 }) =
    .next s' := he
  cases e
  have x31 : getX t 31 = s.get 31 := hR.x 31
  have x12 : getX t 12 = s.get 12 := hR.x 12
  by_cases hle : s.get 12 ≤ s.get 31
  · rw [if_pos hle]
    obtain ⟨t', hN⟩ := G.bgeu_t hR.cfg hR.pc (pcok_of hC hd) 31 12 _ hi
      (by rw [x31, x12]; rw [BitVec.le_def] at hle; omega)
    rw [boff6] at hN
    exact ⟨t', hN.ret, rel_pc hR 3 hN⟩
  · rw [if_neg hle]
    obtain ⟨t', hN⟩ := G.bgeu_n hR.cfg hR.pc (pcok_of hC hd) 31 12 _ hi
      (by rw [x31, x12]; rw [BitVec.le_def] at hle; omega)
    exact ⟨t', hN.ret, rel_pc hR 1 (by rw [show BitVec.ofNat 64 (4 * 1) = 4 from rfl]; exact hN)⟩

end

theorem exec_halt {s s'' : R.St} {op a b c : UInt8} (h : exec s op a b c = .halt s'') : op.toNat = 48 ∧ s'' = s := by
  unfold exec at h
  split at h
  all_goals (dsimp only at h)
  all_goals first | (cases h; done) | (split at h <;> cases h; done) | skip
  rename_i heq; cases h; exact ⟨heq, rfl⟩

section
variable {C : Ctx} {s s' : R.St} {t : Proven.St}

/-- **one record step is one retired Sail instruction** -/
theorem sim (hC : C.Ok) (hR : Rel C s t) (he : step C.P s = .next s') : ∃ t', Retires t t' ∧ Rel C s' t' := by
  unfold R.step at he
  split at he
  · rename_i op a b c rest hd
    have hF := allFam_get C.P s.pc hC.fam hd
    simp only [Fam, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
    rcases hF with hF | ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    rotate_left
    · have e : exec s 48 0 1 0 = .halt s := rfl
      rw [e] at he; cases he
    rcases hF with hF | ⟨⟨⟨rfl, rfl⟩, rfl⟩, hc⟩
    rotate_left
    · exact case_sb hC hR 6 13 rfl rfl hc w_sb hd he
    rcases hF with hF | ⟨⟨⟨hop, rfl⟩, rfl⟩, rfl⟩
    rotate_left
    · rcases hop with ((rfl | rfl) | rfl) | rfl
      · exact case_r hC hR (· ||| ·) (fun _ => rfl) w_or (fun t h _ hpc hok hi => G.step_or h hpc hok 5 5 6 hi) hd he
      · exact case_r hC hR (· + ·) (fun _ => rfl) w_add
          (fun t h _ hpc hok hi => G.step_add h hpc hok 5 5 6 (by decide) hi) hd he
      · exact case_r hC hR (· - ·) (fun _ => rfl) w_sub (fun t h _ hpc hok hi => G.step_sub h hpc hok 5 5 6 hi) hd he
      · exact case_r hC hR (· * ·) (fun _ => rfl) w_mul (fun t h _ hpc hok hi => G.step_mul h hpc hok 5 5 6 hi) hd he
    rcases hF with hF | ⟨⟨rfl, rfl⟩, rfl⟩
    rotate_left
    · exact case_sd hC hR 5 31 rfl rfl w_sd hd he
    rcases hF with hF | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    rotate_left
    · exact case_addi8 hC hR 31 31 rfl rfl (by decide) (by decide) (by decide) w_addi8_31 hd he
    · exact case_addi8 hC hR 28 28 rfl rfl (by decide) (by decide) (by decide) w_addi8_28 hd he
    rcases hF with hF | ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    rotate_left
    · exact case_bgeu hC hR hd he
    rcases hF with hF | ⟨⟨rfl, rfl⟩, rfl⟩
    rotate_left
    · exact case_ori hC hR 5 5 rfl rfl (by decide) (by decide) (by decide) (by decide) w_ori hd he
    rcases hF with hF | ⟨⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hc⟩
    rotate_left
    · exact case_srli hC hR 6 5 rfl rfl (by decide) (by decide) (by decide) hc w_srli_6_5 hd he
    · exact case_srli hC hR 31 2 rfl rfl (by decide) (by decide) (by decide) hc w_srli_31_2 hd he
    rcases hF with hF | ⟨⟨rfl, rfl | rfl⟩, rfl⟩
    rotate_left
    · exact case_lbu hC hR 5 28 rfl rfl (by decide) (by decide) (by decide) w_lbu_5 hd he
    · exact case_lbu hC hR 6 28 rfl rfl (by decide) (by decide) (by decide) w_lbu_6 hd he
    rcases hF with hF | ⟨⟨rfl, rfl | rfl⟩, rfl⟩
    rotate_left
    · exact case_ld hC hR 5 31 rfl rfl (by decide) (by decide) (by decide) w_ld_5 hd he
    · exact case_ld hC hR 6 31 rfl rfl (by decide) (by decide) (by decide) w_ld_6 hd he
    rcases hF with ⟨rfl, ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hc⟩
    · exact case_addi hC hR 31 31 rfl rfl (by decide) (by decide) (by decide) w_addi_31_31 hd he
    · exact case_addi hC hR 10 0 rfl rfl (by decide) (by decide) (by decide) w_addi_10_0 hd he
    · exact case_addi hC hR 5 0 rfl rfl (by decide) (by decide) (by decide) w_addi_5_0 hd he
    · exact case_addi hC hR 28 10 rfl rfl (by decide) (by decide) (by decide) w_addi_28_10 hd he
    · exact case_slli hC hR 5 5 rfl rfl (by decide) (by decide) (by decide) hc w_slli_5_5 hd he
    · exact case_slli hC hR 31 31 rfl rfl (by decide) (by decide) (by decide) hc w_slli_31_31 hd he
  · cases he

end

section
variable {C : Ctx} {s : R.St} {t : Proven.St}
open Proven.Top

/-- **`ret`**: back at `ra`, registers and memory as before -/
theorem sim_halt (hC : C.Ok) (hR : Rel C s t) {s'' : R.St} (he : step C.P s = .halt s'') :
    ∃ t', Retires t t' ∧ Cfg t' ∧ t'.regs.get? .PC = some (BitVec.ofNat 64 C.RA) ∧ (∀ j, getX t' j = getX t j) ∧
      t'.mem = t.mem := by
  unfold R.step at he
  split at he
  · rename_i op a b c rest hd
    have hF := allFam_get C.P s.pc hC.fam hd
    obtain ⟨h48, -⟩ := exec_halt he
    have hop : op = 48 := by
      apply UInt8.toNat_inj.mp; rw [h48]; rfl
    subst hop
    simp only [Fam, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hF
    have hF' : a = 0 ∧ b = 1 ∧ c = 0 := by
      revert hF; simp (config := { decide := true }); exact fun h1 h2 h3 => ⟨h1, h2, h3⟩
    obtain ⟨rfl, rfl, rfl⟩ := hF'
    have hi := instr_of hC hR hd w_ret
    have x1 : getX t 1 = BitVec.ofNat 64 C.RA := (hR.x 1).trans hR.r1
    obtain ⟨t', hN⟩ := G.step_jalr hR.cfg hR.pc (pcok_of hC hd) 0 1 0 hi
      (by rw [x1]; have := hC.ra; simp; omega)
    refine ⟨t', hN.ret, hN.cfg, by rw [hN.pc, x1]; simp, fun j => ?_, hN.mem⟩
    rw [hN.x j]; by_cases hj : j = 0 <;> simp [hj]
  · cases he

theorem runs_snoc : ∀ {a b c : riscv.State}, Runs riscv a b → riscv.step b = some c → Runs riscv a c
  | _, _, _, .stop, h => .step h .stop
  | _, _, _, .step e r, h => .step e (runs_snoc r h)

/-- **record runs are Sail runs** -/
theorem sim_star (hC : C.Ok) : ∀ {s s' : R.St}, Star C.P s s' → ∀ {t : Proven.St}, Rel C s t →
    ∃ t', Runs riscv t t' ∧ Rel C s' t'
  | _, _, .refl _, t, hR => ⟨t, .stop, hR⟩
  | _, _, .step e rest, t, hR => by
    obtain ⟨t1, r1, hR1⟩ := sim hC hR e
    obtain ⟨t', r', hR'⟩ := sim_star hC rest hR1
    exact ⟨t', .step (step_of_retires r1) r', hR'⟩

end

end Nano.S

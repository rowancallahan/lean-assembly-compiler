/- Gen's RISC-V bytes determine the J program (`cjUnique`): the bytes are the words' little-endian bytes (`g40_le4`),
4 bytes give back a word below 2^32 (`ArmRA.word_back`), and `encG` is injective on `JOK` instructions
(`encG_inj`: the opcode and funct3 fields tell the constructors apart, `key`; the fields of one constructor are
read back from the word because `GoodX`/`JOK` bound each of them). -/
import Nano.Run.ArmEncOK
namespace CjU
open CallProbe SimW ArmRA

/-! ## the words as sums of fields -/

theorem V_addi (rd rs : Nat) (imm : Int) (h : GoodX (.addi rd rs imm)) :
    (encG (.addi rd rs imm)).toNat = (imm % 4096).toNat * 2 ^ 20 + rs * 2 ^ 15 + 0 * 2 ^ 12 + rd * 2 ^ 7 + 19 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; rw [addi_V rd rs imm h1 h2 h3 h4]; omega
theorem V_ld (rd rs : Nat) (f : Int) (h : GoodX (.ld rd rs f)) :
    (encG (.ld rd rs f)).toNat = (f % 4096).toNat * 2 ^ 20 + rs * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact I_V 3 3 rd rs f (by omega) (by omega) h1 h2
theorem V_lbu (rd rs : Nat) (f : Int) (h : GoodX (.lbu rd rs f)) :
    (encG (.lbu rd rs f)).toNat = (f % 4096).toNat * 2 ^ 20 + rs * 2 ^ 15 + 4 * 2 ^ 12 + rd * 2 ^ 7 + 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact I_V 3 4 rd rs f (by omega) (by omega) h1 h2
theorem V_sd (r2 r1 : Nat) (f : Int) (h : GoodX (.sd r2 r1 f)) :
    (encG (.sd r2 r1 f)).toNat =
      (f % 4096).toNat / 32 * 2 ^ 25 + r2 * 2 ^ 20 + r1 * 2 ^ 15 + 3 * 2 ^ 12 + (f % 4096).toNat % 32 * 2 ^ 7 + 35 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact S_V 3 r2 r1 f (by omega) h1 h2
theorem V_sb (r2 r1 : Nat) (f : Int) (h : GoodX (.sb r2 r1 f)) :
    (encG (.sb r2 r1 f)).toNat =
      (f % 4096).toNat / 32 * 2 ^ 25 + r2 * 2 ^ 20 + r1 * 2 ^ 15 + 0 * 2 ^ 12 + (f % 4096).toNat % 32 * 2 ^ 7 + 35 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact S_V 0 r2 r1 f (by omega) h1 h2
theorem V_alu (op rd a b : Nat) (h : GoodX (.alu op rd a b)) :
    (encG (.alu op rd a b)).toNat = (aluF op).1.toNat * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + (aluF op).2.toNat * 2 ^ 12 +
      rd * 2 ^ 7 + 51 := by
  obtain ⟨hd, ha, hb, ho1, ho2⟩ := h
  obtain ⟨-, -, -, -, f5, f6, -⟩ := alu_facts op ho1 ho2
  have := g1_sum (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64 f5 f6 (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
  rw [tU (by omega), tU (by omega), tU (by omega)] at this
  exact this
theorem V_slli (rd rs sh : Nat) (h : GoodX (.slli rd rs sh)) :
    (encG (.slli rd rs sh)).toNat = sh * 2 ^ 20 + rs * 2 ^ 15 + 1 * 2 ^ 12 + rd * 2 ^ 7 + 19 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact sh_V 1 rd rs sh (by omega) h1 h2 h3
theorem V_srli (rd rs sh : Nat) (h : GoodX (.srli rd rs sh)) :
    (encG (.srli rd rs sh)).toNat = sh * 2 ^ 20 + rs * 2 ^ 15 + 5 * 2 ^ 12 + rd * 2 ^ 7 + 19 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact sh_V 5 rd rs sh (by omega) h1 h2 h3

/-- the branch word with funct3 `f3` -/
def VB (f3 a b : Nat) (o : Int) : Nat :=
  ((4 * o) % 8192).toNat / 4096 % 2 * 2 ^ 31 + ((4 * o) % 8192).toNat / 32 % 64 * 2 ^ 25 + b * 2 ^ 20 +
    a * 2 ^ 15 + f3 * 2 ^ 12 + ((4 * o) % 8192).toNat / 2 % 16 * 2 ^ 8 + ((4 * o) % 8192).toNat / 2048 % 2 * 2 ^ 7 + 99

theorem V_beq (a b : Nat) (o : Int) (h : GoodX (.beq a b o)) : (encG (.beq a b o)).toNat = VB 0 a b o := by
  obtain ⟨h1, h2, -⟩ := h
  exact B_V 0 a b o (by omega) h1 h2
theorem V_bne (a b : Nat) (o : Int) (h : GoodX (.bne a b o)) : (encG (.bne a b o)).toNat = VB 1 a b o := by
  obtain ⟨h1, h2, -⟩ := h
  exact B_V 1 a b o (by omega) h1 h2
theorem V_bltu (a b : Nat) (o : Int) (h : GoodX (.bltu a b o)) : (encG (.bltu a b o)).toNat = VB 6 a b o := by
  obtain ⟨h1, h2, -⟩ := h
  exact B_V 6 a b o (by omega) h1 h2
theorem V_bgeu (a b : Nat) (o : Int) (h : GoodX (.bgeu a b o)) : (encG (.bgeu a b o)).toNat = VB 7 a b o := by
  obtain ⟨h1, h2, -⟩ := h
  exact B_V 7 a b o (by omega) h1 h2
theorem V_jal (rd : Nat) (o : Int) (h : GoodX (.jal rd o)) :
    (encG (.jal rd o)).toNat = ((4 * o) % 2097152).toNat / 2 ^ 20 % 2 * 2 ^ 31 +
      ((4 * o) % 2097152).toNat / 2 % 1024 * 2 ^ 21 + ((4 * o) % 2097152).toNat / 2048 % 2 * 2 ^ 20 +
      ((4 * o) % 2097152).toNat / 4096 % 256 * 2 ^ 12 + rd * 2 ^ 7 + 111 := by
  have hd : rd < 32 := h
  exact jal_V rd o hd
theorem V_jalr (rd rs : Nat) (h : GoodX (.jalr rd rs)) :
    (encG (.jalr rd rs)).toNat = 0 * 2 ^ 20 + rs * 2 ^ 15 + 0 * 2 ^ 12 + rd * 2 ^ 7 + 103 := by
  obtain ⟨h1, h2⟩ := h
  have := g2_sum C.g_103 0 rd.toUInt64 rs.toUInt64 0 (by decide) (by decide) (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega)
  rw [tU (by omega), tU (by omega), show C.g_103.toNat = 103 from rfl, show (0 : UInt64).toNat = 0 from rfl] at this
  simp only [encG]; omega

/-! ## opcode and funct3 tell the constructors apart -/

def opj : J → Nat
  | .addi .. => 19 | .slli .. => 19 | .srli .. => 19
  | .ld .. => 3 | .lbu .. => 3
  | .sd .. => 35 | .sb .. => 35
  | .alu .. => 51
  | .beq .. => 99 | .bne .. => 99 | .bltu .. => 99 | .bgeu .. => 99
  | .jal .. => 111
  | .jalr .. => 103

def f3j : J → Nat
  | .addi .. => 0 | .slli .. => 1 | .srli .. => 5
  | .ld .. => 3 | .lbu .. => 4
  | .sd .. => 3 | .sb .. => 0
  | .alu .. => 9
  | .beq .. => 0 | .bne .. => 1 | .bltu .. => 6 | .bgeu .. => 7
  | .jal .. => 9
  | .jalr .. => 0

/-- constructor index -/
def cj : J → Nat
  | .addi .. => 0 | .slli .. => 1 | .srli .. => 2 | .ld .. => 3 | .lbu .. => 4 | .sd .. => 5 | .sb .. => 6
  | .alu .. => 7 | .beq .. => 8 | .bne .. => 9 | .bltu .. => 10 | .bgeu .. => 11 | .jal .. => 12 | .jalr .. => 13

theorem key (j : J) (h : GoodX j) :
    (encG j).toNat % 128 = opj j ∧ (opj j ≠ 51 → opj j ≠ 111 → (encG j).toNat / 4096 % 8 = f3j j) := by
  cases j with
  | addi rd rs imm => have := V_addi _ _ _ h; obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | ld rd rs f => have := V_ld _ _ _ h; obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | lbu rd rs f => have := V_lbu _ _ _ h; obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | sd r2 r1 f => have := V_sd _ _ _ h; obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | sb r2 r1 f => have := V_sb _ _ _ h; obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | alu op rd a b => have := V_alu _ _ _ _ h; exact ⟨by simp only [opj]; omega, fun h1 _ => absurd rfl h1⟩
  | slli rd rs sh => have := V_slli _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | srli rd rs sh => have := V_srli _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | beq a b o => have := V_beq _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; unfold VB at this; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | bne a b o => have := V_bne _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; unfold VB at this; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | bltu a b o => have := V_bltu _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; unfold VB at this; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | bgeu a b o => have := V_bgeu _ _ _ h; obtain ⟨h1, h2, h3⟩ := h; unfold VB at this; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩
  | jal rd o => have := V_jal _ _ h; exact ⟨by simp only [opj]; omega, fun _ h2 => absurd rfl h2⟩
  | jalr rd rs => have := V_jalr _ _ h; obtain ⟨h1, h2⟩ := h; exact ⟨by simp only [opj]; omega, fun _ _ => by simp only [f3j]; omega⟩

/-- the constructor from opcode and funct3 -/
theorem cj_of (j : J) : cj j = if opj j = 51 then 7 else if opj j = 111 then 12 else
    if opj j = 19 then (if f3j j = 0 then 0 else if f3j j = 1 then 1 else 2) else
    if opj j = 3 then (if f3j j = 3 then 3 else 4) else
    if opj j = 35 then (if f3j j = 3 then 5 else 6) else
    if opj j = 103 then 13 else
    (if f3j j = 0 then 8 else if f3j j = 1 then 9 else if f3j j = 6 then 10 else 11) := by
  cases j <;> rfl

theorem cj_eq (j j' : J) (h : GoodX j) (h' : GoodX j') (e : encG j = encG j') : cj j = cj j' := by
  obtain ⟨a1, b1⟩ := key j h
  obtain ⟨a2, b2⟩ := key j' h'
  rw [e] at a1 b1
  have eo : opj j = opj j' := a1.symm.trans a2
  rw [cj_of j, cj_of j', eo]
  by_cases c1 : opj j' = 51
  · rw [if_pos c1, if_pos c1]
  by_cases c2 : opj j' = 111
  · rw [if_neg c1, if_neg c1, if_pos c2, if_pos c2]
  have ef : f3j j = f3j j' := (b1 (eo ▸ c1) (eo ▸ c2)).symm.trans (b2 c1 c2)
  rw [ef]

/-! ## equal constructors: the fields are read back -/

theorem alu_code (op : Nat) (h1 : 1 ≤ op) (h2 : op ≤ 8) :
    (op = 1 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 0) ∨ (op = 2 ∧ (aluF op).1.toNat = 32 ∧ (aluF op).2.toNat = 0) ∨
    (op = 3 ∧ (aluF op).1.toNat = 1 ∧ (aluF op).2.toNat = 0) ∨ (op = 4 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 7) ∨
    (op = 5 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 6) ∨ (op = 6 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 1) ∨
    (op = 7 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 5) ∨ (op = 8 ∧ (aluF op).1.toNat = 0 ∧ (aluF op).2.toNat = 4) := by
  have : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem I_inj {x x' rs rs' rd rd' f3 p : Nat} (hx : x < 4096) (hx' : x' < 4096) (h1 : rs < 32) (h1' : rs' < 32)
    (h2 : rd < 32) (h2' : rd' < 32)
    (e : x * 2 ^ 20 + rs * 2 ^ 15 + f3 * 2 ^ 12 + rd * 2 ^ 7 + p = x' * 2 ^ 20 + rs' * 2 ^ 15 + f3 * 2 ^ 12 + rd' * 2 ^ 7 + p) :
    x = x' ∧ rs = rs' ∧ rd = rd' := by omega

theorem S_inj {x x' r2 r2' r1 r1' f3 : Nat} (hx : x < 4096) (hx' : x' < 4096) (h1 : r2 < 32) (h1' : r2' < 32)
    (h2 : r1 < 32) (h2' : r1' < 32)
    (e : x / 32 * 2 ^ 25 + r2 * 2 ^ 20 + r1 * 2 ^ 15 + f3 * 2 ^ 12 + x % 32 * 2 ^ 7 + 35 =
      x' / 32 * 2 ^ 25 + r2' * 2 ^ 20 + r1' * 2 ^ 15 + f3 * 2 ^ 12 + x' % 32 * 2 ^ 7 + 35) :
    x = x' ∧ r2 = r2' ∧ r1 = r1' := by omega

theorem recB (x : Nat) (hx : x < 8192) (h0 : x % 2 = 0) :
    x = x / 4096 % 2 * 4096 + x / 2048 % 2 * 2048 + x / 32 % 64 * 32 + x / 2 % 16 * 2 := by omega
theorem recJ (x : Nat) (hx : x < 2097152) (h0 : x % 2 = 0) :
    x = x / 2 ^ 20 % 2 * 2 ^ 20 + x / 4096 % 256 * 4096 + x / 2048 % 2 * 2048 + x / 2 % 1024 * 2 := by omega

theorem exB (p1 p2 p3 p4 a b f3 V : Nat) (h1 : p1 < 2) (h2 : p2 < 64) (h3 : p3 < 16) (h4 : p4 < 2) (ha : a < 32)
    (hb : b < 32) (hf : f3 < 8)
    (hV : V = p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) :
    p1 = V / 2 ^ 31 % 2 ∧ p2 = V / 2 ^ 25 % 64 ∧ p3 = V / 256 % 16 ∧ p4 = V / 128 % 2 ∧ a = V / 2 ^ 15 % 32 ∧
      b = V / 2 ^ 20 % 32 := by
  subst hV
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem exJ (p1 p2 p3 p4 d V : Nat) (h1 : p1 < 2) (h2 : p2 < 1024) (h3 : p3 < 2) (h4 : p4 < 256) (hd : d < 32)
    (hV : V = p1 * 2 ^ 31 + p2 * 2 ^ 21 + p3 * 2 ^ 20 + p4 * 2 ^ 12 + d * 2 ^ 7 + 111) :
    p1 = V / 2 ^ 31 % 2 ∧ p2 = V / 2 ^ 21 % 1024 ∧ p3 = V / 2 ^ 20 % 2 ∧ p4 = V / 2 ^ 12 % 256 ∧ d = V / 128 % 32 := by
  subst hV
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem B_inj {x x' a a' b b' f3 : Nat} (hx : x < 8192) (hx' : x' < 8192) (h0 : x % 2 = 0) (h0' : x' % 2 = 0)
    (h1 : a < 32) (h1' : a' < 32) (h2 : b < 32) (h2' : b' < 32) (hf : f3 < 8)
    (e : x / 4096 % 2 * 2 ^ 31 + x / 32 % 64 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + x / 2 % 16 * 2 ^ 8 +
        x / 2048 % 2 * 2 ^ 7 + 99 =
      x' / 4096 % 2 * 2 ^ 31 + x' / 32 % 64 * 2 ^ 25 + b' * 2 ^ 20 + a' * 2 ^ 15 + f3 * 2 ^ 12 + x' / 2 % 16 * 2 ^ 8 +
        x' / 2048 % 2 * 2 ^ 7 + 99) :
    x = x' ∧ a = a' ∧ b = b' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := exB (x / 4096 % 2) (x / 32 % 64) (x / 2 % 16) (x / 2048 % 2) a b f3 _ (by omega) (by omega) (by omega) (by omega) h1 h2 hf rfl
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := exB (x' / 4096 % 2) (x' / 32 % 64) (x' / 2 % 16) (x' / 2048 % 2) a' b' f3 _ (by omega) (by omega) (by omega) (by omega) h1' h2' hf e
  have c1 := a1.trans b1.symm
  have c2 := a2.trans b2.symm
  have c3 := a3.trans b3.symm
  have c4 := a4.trans b4.symm
  refine ⟨?_, a5.trans b5.symm, a6.trans b6.symm⟩
  rw [recB x hx h0, recB x' hx' h0', c1, c2, c3, c4]

theorem J_inj {x x' d d' : Nat} (hx : x < 2097152) (hx' : x' < 2097152) (h0 : x % 2 = 0) (h0' : x' % 2 = 0)
    (h1 : d < 32) (h1' : d' < 32)
    (e : x / 2 ^ 20 % 2 * 2 ^ 31 + x / 2 % 1024 * 2 ^ 21 + x / 2048 % 2 * 2 ^ 20 + x / 4096 % 256 * 2 ^ 12 + d * 2 ^ 7 + 111 =
      x' / 2 ^ 20 % 2 * 2 ^ 31 + x' / 2 % 1024 * 2 ^ 21 + x' / 2048 % 2 * 2 ^ 20 + x' / 4096 % 256 * 2 ^ 12 + d' * 2 ^ 7 + 111) :
    x = x' ∧ d = d' := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := exJ (x / 2 ^ 20 % 2) (x / 2 % 1024) (x / 2048 % 2) (x / 4096 % 256) d _ (by omega) (by omega) (by omega) (by omega) h1 rfl
  obtain ⟨b1, b2, b3, b4, b5⟩ := exJ (x' / 2 ^ 20 % 2) (x' / 2 % 1024) (x' / 2048 % 2) (x' / 4096 % 256) d' _ (by omega) (by omega) (by omega) (by omega) h1' e
  have c1 := a1.trans b1.symm
  have c2 := a2.trans b2.symm
  have c3 := a3.trans b3.symm
  have c4 := a4.trans b4.symm
  refine ⟨?_, a5.trans b5.symm⟩
  rw [recJ x hx h0, recJ x' hx' h0', c1, c2, c3, c4]

theorem VB_inj {f3 a b a' b' : Nat} {o o' : Int} (hf : f3 < 8) (h1 : a < 32) (h1' : a' < 32) (h2 : b < 32) (h2' : b' < 32)
    (ho : -1024 ≤ o ∧ o < 1024) (ho' : -1024 ≤ o' ∧ o' < 1024) (e : VB f3 a b o = VB f3 a' b' o') :
    a = a' ∧ b = b' ∧ o = o' := by
  unfold VB at e
  have := B_inj (x := ((4 * o) % 8192).toNat) (x' := ((4 * o') % 8192).toNat) (by omega) (by omega) (by omega) (by omega)
    h1 h1' h2 h2' hf e
  omega

theorem encG_inj (j j' : J) (h : JOK j) (h' : JOK j') (e : encG j = encG j') : j = j' := by
  have hc := cj_eq j j' h.1 h'.1 e
  have eN : (encG j).toNat = (encG j').toNat := by rw [e]
  obtain ⟨g, hj⟩ := h
  obtain ⟨g', hj'⟩ := h'
  cases j with
  | addi rd rs imm =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs' imm'
    rw [V_addi _ _ _ g, V_addi _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4⟩ := g; obtain ⟨h1', h2', h3', h4'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (by omega) (by omega) h2 h2' h1 h1' eN
    subst b c; rw [show imm = imm' by omega]
  | ld rd rs imm =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs' imm'
    rw [V_ld _ _ _ g, V_ld _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4⟩ := g; obtain ⟨h1', h2', h3', h4'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (by omega) (by omega) h2 h2' h1 h1' eN
    subst b c; rw [show imm = imm' by omega]
  | lbu rd rs imm =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs' imm'
    rw [V_lbu _ _ _ g, V_lbu _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4⟩ := g; obtain ⟨h1', h2', h3', h4'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (by omega) (by omega) h2 h2' h1 h1' eN
    subst b c; rw [show imm = imm' by omega]
  | sd r2 r1 imm =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i r2' r1' imm'
    rw [V_sd _ _ _ g, V_sd _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4⟩ := g; obtain ⟨h1', h2', h3', h4'⟩ := g'
    obtain ⟨a, b, c⟩ := S_inj (by omega) (by omega) h1 h1' h2 h2' eN
    subst b c; rw [show imm = imm' by omega]
  | sb r2 r1 imm =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i r2' r1' imm'
    rw [V_sb _ _ _ g, V_sb _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4⟩ := g; obtain ⟨h1', h2', h3', h4'⟩ := g'
    obtain ⟨a, b, c⟩ := S_inj (by omega) (by omega) h1 h1' h2 h2' eN
    subst b c; rw [show imm = imm' by omega]
  | slli rd rs sh =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs' sh'
    rw [V_slli _ _ _ g, V_slli _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (by omega) (by omega) h2 h2' h1 h1' eN
    subst a b c; rfl
  | srli rd rs sh =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs' sh'
    rw [V_srli _ _ _ g, V_srli _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (by omega) (by omega) h2 h2' h1 h1' eN
    subst a b c; rfl
  | jalr rd rs =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' rs'
    rw [V_jalr _ _ g, V_jalr _ _ g'] at eN
    obtain ⟨h1, h2⟩ := g; obtain ⟨h1', h2'⟩ := g'
    obtain ⟨a, b, c⟩ := I_inj (x := 0) (x' := 0) (by omega) (by omega) h2 h2' (by omega) (by omega) eN
    subst b c; rfl
  | alu op rd a b =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i op' rd' a' b'
    rw [V_alu _ _ _ _ g, V_alu _ _ _ _ g'] at eN
    obtain ⟨h1, h2, h3, h4, h5⟩ := g; obtain ⟨h1', h2', h3', h4', h5'⟩ := g'
    have c1 := alu_code op h4 h5
    have c2 := alu_code op' h4' h5'
    obtain ⟨-, -, -, -, f5, f6, -⟩ := alu_facts op h4 h5
    obtain ⟨-, -, -, -, f5', f6', -⟩ := alu_facts op' h4' h5'
    generalize (aluF op).1.toNat = u at *
    generalize (aluF op).2.toNat = v at *
    generalize (aluF op').1.toNat = u' at *
    generalize (aluF op').2.toNat = v' at *
    have : u = u' ∧ v = v' ∧ rd = rd' ∧ a = a' ∧ b = b' := by omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := this
    subst q1 q2 q3 q4 q5
    rw [show op = op' by omega]
  | beq a b o =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i a' b' o'
    rw [V_beq _ _ _ g, V_beq _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨q1, q2, q3⟩ := VB_inj (by omega) h1 h1' h2 h2' (by omega) (by omega) eN
    subst q1 q2 q3; rfl
  | bne a b o =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i a' b' o'
    rw [V_bne _ _ _ g, V_bne _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨q1, q2, q3⟩ := VB_inj (by omega) h1 h1' h2 h2' (by omega) (by omega) eN
    subst q1 q2 q3; rfl
  | bltu a b o =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i a' b' o'
    rw [V_bltu _ _ _ g, V_bltu _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨q1, q2, q3⟩ := VB_inj (by omega) h1 h1' h2 h2' (by omega) (by omega) eN
    subst q1 q2 q3; rfl
  | bgeu a b o =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i a' b' o'
    rw [V_bgeu _ _ _ g, V_bgeu _ _ _ g'] at eN
    obtain ⟨h1, h2, h3⟩ := g; obtain ⟨h1', h2', h3'⟩ := g'
    obtain ⟨q1, q2, q3⟩ := VB_inj (by omega) h1 h1' h2 h2' (by omega) (by omega) eN
    subst q1 q2 q3; rfl
  | jal rd o =>
    cases j' <;> first | (simp [cj] at hc; done) | skip
    rename_i rd' o'
    rw [V_jal _ _ g, V_jal _ _ g'] at eN
    have h1 : rd < 32 := g
    have h1' : rd' < 32 := g'
    obtain ⟨b1, b2⟩ := hj rd o rfl
    obtain ⟨b1', b2'⟩ := hj' rd' o' rfl
    have := J_inj (x := ((4 * o) % 2097152).toNat) (x' := ((4 * o') % 2097152).toNat) (by omega) (by omega) (by omega)
      (by omega) h1 h1' eN
    obtain ⟨q1, q2⟩ := this
    subst q2; rw [show o = o' by omega]

/-! ## bytes back to words, words back to instructions -/

theorem le4_inj {v w : UInt64} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) (e : le4 v = le4 w) : v = w := by
  rw [← word_back v hv, ← word_back w hw, e]

theorem flat_inj : ∀ (ws ws' : List UInt64), (∀ w ∈ ws, w.toNat < 2 ^ 32) → (∀ w ∈ ws', w.toNat < 2 ^ 32) →
    ws.flatMap le4 = ws'.flatMap le4 → ws = ws'
  | [], [], _, _, _ => rfl
  | [], w :: ws', _, _, e => by simp [le4] at e
  | w :: ws, [], _, _, e => by simp [le4] at e
  | v :: ws, w :: ws', h, h', e => by
    rw [List.flatMap_cons, List.flatMap_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e rfl
    rw [le4_inj (h v (List.mem_cons_self ..)) (h' w (List.mem_cons_self ..)) e1,
      flat_inj ws ws' (fun x hx => h x (List.mem_cons_of_mem _ hx)) (fun x hx => h' x (List.mem_cons_of_mem _ hx)) e2]

theorem map_inj : ∀ (Cj Cj' : List J), (∀ j ∈ Cj, JOK j) → (∀ j ∈ Cj', JOK j) → Cj.map encG = Cj'.map encG → Cj = Cj'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, e => by simp at e
  | _ :: _, [], _, _, e => by simp at e
  | j :: Cj, j' :: Cj', h, h', e => by
    rw [List.map_cons, List.map_cons] at e
    obtain ⟨e1, e2⟩ := List.cons.inj e
    rw [encG_inj j j' (h j (List.mem_cons_self ..)) (h' j' (List.mem_cons_self ..)) e1,
      map_inj Cj Cj' (fun x hx => h x (List.mem_cons_of_mem _ hx)) (fun x hx => h' x (List.mem_cons_of_mem _ hx)) e2]

end CjU

namespace NanoMain
open CallProbe

/-- **the RISC-V bytes of a J program determine the J program** -/
theorem cjUnique : ∀ (c c' : List UInt8) (Cj Cj' : List CallProbe.J), Cj.length < 2 ^ 18 → Cj'.length < 2 ^ 18 →
    (∀ j ∈ Cj, SimW.JOK j) → (∀ j ∈ Cj', SimW.JOK j) →
    C.g40 16777216 c (Cj.map encG) 0 [] = C.g40 16777216 c' (Cj'.map encG) 0 [] → Cj = Cj' := by
  intro c c' Cj Cj' hl hl' hJ hJ' e
  have e1 : C.g40 16777216 c (Cj.map encG) 0 [] = (Cj.map encG).flatMap ArmRA.le4 := by
    have := g40_le4 c (Cj.map encG) (by simp; omega) 16777216 0 [] (by simp; omega) (by omega)
    simpa using this
  have e2 : C.g40 16777216 c' (Cj'.map encG) 0 [] = (Cj'.map encG).flatMap ArmRA.le4 := by
    have := g40_le4 c' (Cj'.map encG) (by simp; omega) 16777216 0 [] (by simp; omega) (by omega)
    simpa using this
  rw [e1, e2] at e
  refine CjU.map_inj Cj Cj' hJ hJ' (CjU.flat_inj _ _ ?_ ?_ e)
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    exact ArmRA.encG_lt j (hJ j hj).1
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    exact ArmRA.encG_lt j (hJ' j hj).1

end NanoMain

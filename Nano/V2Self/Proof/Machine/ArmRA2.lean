/- rv2arm (`RA`) on Gen's words, per J instruction `j` with `JOK j` (GoodX, jal offsets within ±2^18): `t0_ok`: on an
`armOK` instruction `RA.t0` appends the bytes of `ArmEnc.blockJ j`; `c0_ok`: rv2arm's validation `RA.c0` accepts only
`armOK` instructions (with the target inside the program). -/
import Nano.V2Self.Proof.Machine.ArmRA
set_option linter.unusedSimpArgs false
namespace ArmRA
open CallProbe ArmEnc

/-- Gen's instructions that rv2arm reads back exactly: `GoodX` with jal offsets inside ±2^18 J instructions -/
def JOK (j : J) : Prop := GoodX j ∧ ∀ rd o, j = .jal rd o → -2 ^ 18 < o ∧ o < 2 ^ 18

theorem t0_ok (x o : List UInt8) (j : J) (n i : Nat) (hj : JOK j) (hok : armOK n i j = true) :
    RA.t0 x o (encG j) = emit o (body j) := by
  obtain ⟨hg, hjal⟩ := hj
  cases j with
  | addi rd rs imm =>
    simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hg
    obtain ⟨ms, md, -⟩ := hok; exact t0_addi x o rd rs imm h1 h2 h3 h4 md ms
  | ld rd rs f =>
    simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hg
    obtain ⟨-, ms, md, -⟩ := hok; exact t0_ld x o rd rs f h1 h2 h3 h4 md ms
  | sd r2 r1 f =>
    simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hg
    obtain ⟨-, ms, md, -⟩ := hok; exact t0_sd x o r2 r1 f h1 h2 h3 h4 md ms
  | lbu rd rs f =>
    simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hg
    obtain ⟨-, ms, md, -⟩ := hok; exact t0_lbu x o rd rs f h1 h2 h3 h4 md ms
  | sb r2 r1 f =>
    simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4⟩ := hg
    obtain ⟨-, ms, md, -⟩ := hok; exact t0_sb x o r2 r1 f h1 h2 h3 h4 md ms
  | alu op rd a b =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg
    obtain ⟨-, -, ma, mb, md⟩ := hok; exact t0_alu x o op rd a b h4 h5 h1 h2 h3 md ma mb
  | slli rd rs sh =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    obtain ⟨-, ms, md⟩ := hok; exact t0_slli x o rd rs sh h1 h2 h3 md ms
  | srli rd rs sh =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    obtain ⟨-, ms, md⟩ := hok; exact t0_srli x o rd rs sh h1 h2 h3 md ms
  | beq a b off =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    obtain ⟨ma, mb, -⟩ := hok; exact t0_beq x o a b off h1 h2 (by omega) (by omega) ma mb
  | bne a b off =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    have := t0_cbr x o 1 1 (by omega) a b off h1 h2 (by omega) (by omega) hok.1 hok.2.1
    simpa [encG, body] using this
  | bltu a b off =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    have := t0_cbr x o 6 3 (by omega) a b off h1 h2 (by omega) (by omega) hok.1 hok.2.1
    simpa [encG, body] using this
  | bgeu a b off =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2, h3⟩ := hg
    have := t0_cbr x o 7 2 (by omega) a b off h1 h2 (by omega) (by omega) hok.1 hok.2.1
    simpa [encG, body] using this
  | jal rd off =>
    obtain ⟨h3, h4⟩ := hjal rd off rfl
    exact t0_jal x o rd off hg h3 h4
  | jalr rd rs =>
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨h1, h2⟩ := hg
    obtain ⟨-, -, ms⟩ := hok; exact t0_jalr x o rd rs (by omega) h2 ms

theorem u2_eq {r : Nat} (hr : r < 32) : RA.u2 r.toUInt64 = if mapped r then 1 else 0 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨
    r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨
    r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem c2_iu {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) : RA.c2 (iu z) = 1 := by
  unfold RA.c2; rw [if_pos]; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, CallProbe.iu_toNat]; simp; omega

theorem c0_addi (rd rs : Nat) (imm : Int) (i n : Nat) (hg : GoodX (.addi rd rs imm))
    (h : RA.c0 (encG (.addi rd rs imm)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.addi rd rs imm) = true := by
  obtain ⟨hd, hs, h1, h2⟩ := hg
  have hV := addi_V rd rs imm hd hs h1 h2
  generalize encG (.addi rd rs imm) = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 19) (by omega), o2_eq (r := 0) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    o5_eq h1 h2 (by omega), c2_iu h1 h2, u2_eq hd, u2_eq hs] at h
  simp only [show ((19:Nat).toUInt64 == 19) = true from rfl, show ((0:Nat).toUInt64 == 0) = true from rfl,
    show ((1 : UInt64) == 0) = false from rfl, if_true, Bool.false_eq_true, if_false] at h
  simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, by omega, by omega⟩ <;> split at h <;> (try split at h) <;> simp_all
macro "fin_ok" : tactic => `(tactic| (repeat' (first | split at h | split)) <;> simp_all <;> omega)

theorem p3 : ((3:Nat).toUInt64 == 19) = false := rfl
theorem p35 : ((35:Nat).toUInt64 == 19) = false ∧ ((35:Nat).toUInt64 == 3) = false := by decide
theorem p51 : ((51:Nat).toUInt64 == 19) = false ∧ ((51:Nat).toUInt64 == 3) = false ∧ ((51:Nat).toUInt64 == 35) = false := by decide

theorem c0_ld (rd rs : Nat) (f : Int) (i n : Nat) (hg : GoodX (.ld rd rs f))
    (h : RA.c0 (encG (.ld rd rs f)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.ld rd rs f) = true := by
  obtain ⟨hd, hs, h1, h2⟩ := hg
  have hV := I_V 3 3 rd rs f (by omega) (by omega) hd hs
  simp only [encG, C.g11, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl] at h
  generalize C.g2 _ _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 3) (by omega), o2_eq (r := 3) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    o5_eq h1 h2 (by omega), c2_iu h1 h2, u2_eq hd, u2_eq hs, beq0 (r := rs) (by omega)] at h
  simp only [p3, show ((3:Nat).toUInt64 == 3) = true from rfl, show ((1 : UInt64) == 0) = false from rfl, if_true,
    Bool.false_eq_true, if_false] at h
  simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases e0 : rs = 0 <;> by_cases e1 : mapped rs = true <;> by_cases e2 : mapped rd = true <;> simp_all

theorem c0_lbu (rd rs : Nat) (f : Int) (i n : Nat) (hg : GoodX (.lbu rd rs f))
    (h : RA.c0 (encG (.lbu rd rs f)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.lbu rd rs f) = true := by
  obtain ⟨hd, hs, h1, h2⟩ := hg
  have hV := I_V 3 4 rd rs f (by omega) (by omega) hd hs
  simp only [encG, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl] at h
  generalize C.g2 _ _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 3) (by omega), o2_eq (r := 4) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    o5_eq h1 h2 (by omega), c2_iu h1 h2, u2_eq hd, u2_eq hs, beq0 (r := rs) (by omega)] at h
  simp only [p3, show ((4:Nat).toUInt64 == 3) = false from rfl, show ((4:Nat).toUInt64 == 4) = true from rfl,
    show ((1 : UInt64) == 0) = false from rfl, if_true, Bool.false_eq_true, if_false] at h
  simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases e0 : rs = 0 <;> by_cases e1 : mapped rs = true <;> by_cases e2 : mapped rd = true <;> simp_all

theorem c0_sd (r2 r1 : Nat) (f : Int) (i n : Nat) (hg : GoodX (.sd r2 r1 f))
    (h : RA.c0 (encG (.sd r2 r1 f)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.sd r2 r1 f) = true := by
  obtain ⟨hd, hs, h1, h2⟩ := hg
  have hV := S_V 3 r2 r1 f (by omega) hd hs
  simp only [encG, C.g12, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl] at h
  generalize C.g3 _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 35) (by omega), o2_eq (r := 3) (by omega), o4_eq (r := r2) (by omega), o3_eq (r := r1) (by omega),
    o6_eq h1 h2 (by omega) (by omega), c2_iu h1 h2, u2_eq hd, u2_eq hs, beq0 (r := r1) (by omega)] at h
  simp only [p35, show ((35:Nat).toUInt64 == 35) = true from rfl, show ((3:Nat).toUInt64 == 3) = true from rfl,
    show ((1 : UInt64) == 0) = false from rfl, if_true, Bool.false_eq_true, if_false] at h
  simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases e0 : r1 = 0 <;> by_cases e1 : mapped r1 = true <;> by_cases e2 : mapped r2 = true <;> simp_all

theorem c0_sb (r2 r1 : Nat) (f : Int) (i n : Nat) (hg : GoodX (.sb r2 r1 f))
    (h : RA.c0 (encG (.sb r2 r1 f)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.sb r2 r1 f) = true := by
  obtain ⟨hd, hs, h1, h2⟩ := hg
  have hV := S_V 0 r2 r1 f (by omega) hd hs
  simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl] at h
  generalize C.g3 _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 35) (by omega), o2_eq (r := 0) (by omega), o4_eq (r := r2) (by omega), o3_eq (r := r1) (by omega),
    o6_eq h1 h2 (by omega) (by omega), c2_iu h1 h2, u2_eq hd, u2_eq hs, beq0 (r := r1) (by omega)] at h
  simp only [p35, show ((35:Nat).toUInt64 == 35) = true from rfl, show ((0:Nat).toUInt64 == 3) = false from rfl,
    show ((0:Nat).toUInt64 == 0) = true from rfl,
    show ((1 : UInt64) == 0) = false from rfl, if_true, Bool.false_eq_true, if_false] at h
  simp only [armOK, imm12, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases e0 : r1 = 0 <;> by_cases e1 : mapped r1 = true <;> by_cases e2 : mapped r2 = true <;> simp_all

theorem c0_alu (op rd a b : Nat) (i n : Nat) (hg : GoodX (.alu op rd a b))
    (h : RA.c0 (encG (.alu op rd a b)) i.toUInt64 n.toUInt64 = 1) : armOK n i (.alu op rd a b) = true := by
  obtain ⟨hd, ha, hb, ho1, ho2⟩ := hg
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := alu_facts op ho1 ho2
  have hV := g1_sum (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64 f5 f6 (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
  rw [tU (by omega), tU (by omega), tU (by omega)] at hV
  simp only [encG] at h
  generalize C.g1 _ _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 51) (by omega), o2_eq (r := (aluF op).2.toNat) (by omega), o1_eq (r := rd) (by omega),
    o3_eq (r := a) (by omega), o4_eq (r := b) (by omega),
    show (25 : UInt64) = (25 : Nat).toUInt64 from rfl, shr_eq (r := (aluF op).1.toNat) (by omega) (by omega),
    show (aluF op).2.toNat.toUInt64 = (aluF op).2 from u64 (tU (by omega)),
    show (aluF op).1.toNat.toUInt64 = (aluF op).1 from u64 (tU (by omega)), f1, u2_eq hd, u2_eq ha, u2_eq hb] at h
  simp only [p51, show ((51:Nat).toUInt64 == 51) = true from rfl, show ((1 : UInt64) == 0) = false from rfl, if_true,
    Bool.false_eq_true, if_false] at h
  simp only [armOK, Bool.and_eq_true, decide_eq_true_eq]
  by_cases e0 : mapped a = true <;> by_cases e1 : mapped b = true <;> by_cases e2 : mapped rd = true <;> simp_all

theorem c0_sh (f3 : Nat) (hf : f3 = 1 ∨ f3 = 5) (rd rs sh : Nat) (i n : Nat) (hd : rd < 32) (hs : rs < 32) (hh : sh < 64)
    (h : RA.c0 (C.g2 C.g_19 f3.toUInt64 rd.toUInt64 rs.toUInt64 sh.toUInt64) i.toUInt64 n.toUInt64 = 1) :
    mapped rs = true ∧ mapped rd = true := by
  have hV := sh_V f3 rd rs sh (by omega) hd hs hh
  generalize C.g2 _ _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 19) (by omega), o2_eq (r := f3) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    show (26 : UInt64) = (26 : Nat).toUInt64 from rfl, shr_eq (r := 0) (by omega) (by omega), u2_eq hd, u2_eq hs] at h
  rcases hf with rfl | rfl <;>
  simp only [show ((19:Nat).toUInt64 == 19) = true from rfl, show ((1:Nat).toUInt64 == 0) = false from rfl,
    show ((1:Nat).toUInt64 == 1) = true from rfl, show ((5:Nat).toUInt64 == 0) = false from rfl,
    show ((5:Nat).toUInt64 == 1) = false from rfl, show ((5:Nat).toUInt64 == 5) = true from rfl,
    show ((0:Nat).toUInt64 == 0) = true from rfl,
    show ((1 : UInt64) == 1) = true from rfl, show ((0 : UInt64) == 1) = false from rfl, if_true,
    Bool.false_eq_true, if_false] at h <;> by_cases e0 : mapped rs = true <;> by_cases e1 : mapped rd = true <;> simp_all
theorem tgt (i n : Nat) (o : Int) (hi : i < n) (hn : n ≤ 2 ^ 18) (h1 : -2 ^ 20 < o) (h2 : o < 2 ^ 20) :
    (4 * i.toUInt64 + iu (4 * o) < 4 * n.toUInt64) = (0 ≤ (i : Int) + o ∧ (i : Int) + o < n) := by
  apply propext; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, CallProbe.iu_toNat,
    tU (by omega), tU (by omega)]
  simp; omega

theorem and3_iu (o : Int) : (iu (4 * o) &&& 3 == 0) = true := by
  apply beq_iff_eq.2; apply u64; wnorm; rw [CallProbe.iu_toNat]; simp; omega

theorem p99' : ((99:Nat).toUInt64 == 19) = false ∧ ((99:Nat).toUInt64 == 3) = false ∧ ((99:Nat).toUInt64 == 35) = false ∧
    ((99:Nat).toUInt64 == 51) = false ∧ ((99:Nat).toUInt64 == 99) = true := by decide

theorem c0_br (f3 : Nat) (hf : f3 = 0 ∨ f3 = 1 ∨ f3 = 6 ∨ f3 = 7) (a b : Nat) (off : Int) (i n : Nat)
    (ha : a < 32) (hb : b < 32) (h1 : -1000 ≤ off) (h2 : off ≤ 1000) (hi : i < n) (hn : n ≤ 2 ^ 18)
    (h : RA.c0 (C.g4 f3.toUInt64 a.toUInt64 b.toUInt64 (iu (4 * off))) i.toUInt64 n.toUInt64 = 1) :
    mapped a = true ∧ mapped b = true ∧ 0 ≤ (i : Int) + off ∧ (i : Int) + off < n := by
  have hV := B_V f3 a b off (by omega) ha hb
  generalize C.g4 _ _ _ _ = v at hV h
  obtain ⟨q0, q2, q3, q4⟩ := B_fields ha hb (by omega) hV
  simp only [RA.c0] at h
  have hb3 : RA.b3 f3.toUInt64 ≠ 99 := by rcases hf with rfl | rfl | rfl | rfl <;> decide
  have hlim : (iu (4 * off) + 262140 < 524281) = True := by
    apply propext; simp only [iff_true]; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, CallProbe.iu_toNat]; simp; omega
  rw [o0_eq q0] at h
  simp only [p99', if_true, Bool.false_eq_true, if_false] at h
  rw [o2_eq q2, o3_eq q3, o4_eq q4, br_o7 h1 h2 (by omega) ha hb hV, u2_eq ha, u2_eq hb] at h
  simp only [tgt i n off hi hn (by omega) (by omega), and3_iu, hlim, beq_false_of_ne hb3, if_true,
    Bool.false_eq_true, if_false] at h
  by_cases e0 : mapped a = true <;> by_cases e1 : mapped b = true <;>
    by_cases e2 : 0 ≤ (i : Int) + off ∧ (i : Int) + off < n <;> simp_all

theorem c0_jal (rd : Nat) (off : Int) (i n : Nat) (hd : rd < 32) (h1 : -2 ^ 18 < off) (h2 : off < 2 ^ 18)
    (hi : i < n) (hn : n ≤ 2 ^ 18) (h : RA.c0 (encG (.jal rd off)) i.toUInt64 n.toUInt64 = 1) :
    rd < 2 ∧ 0 ≤ (i : Int) + off ∧ (i : Int) + off < n := by
  have hV := jal_V rd off hd
  obtain ⟨q0, q1, q2, q3⟩ := J_fields hd (by omega) (by omega) (by omega) hV
  simp only [encG] at h
  generalize C.g5 _ _ = v at hV q0 q1 q2 q3 h
  simp only [RA.c0] at h
  have hc3 : RA.c3 (iu (4 * off)) = 1 := by
    unfold RA.c3; rw [if_pos]; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, CallProbe.iu_toNat]; simp; omega
  have hlt : (rd.toUInt64 < 2) = (rd < 2) := by
    apply propext; rw [UInt64.lt_iff_toNat_lt, tU (by omega)]; simp
  rw [o0_eq q0] at h
  simp only [show ((111:Nat).toUInt64 == 19) = false from rfl, show ((111:Nat).toUInt64 == 3) = false from rfl,
    show ((111:Nat).toUInt64 == 35) = false from rfl, show ((111:Nat).toUInt64 == 51) = false from rfl,
    show ((111:Nat).toUInt64 == 99) = false from rfl, show ((111:Nat).toUInt64 == 111) = true from rfl,
    if_true, Bool.false_eq_true, if_false] at h
  rw [o1_eq q1, o8_eq (by omega) (by omega) q2 q3, hc3] at h
  simp only [tgt i n off hi hn (by omega) (by omega), and3_iu, hlt, show ((1 : UInt64) == 0) = false from rfl, if_true,
    Bool.false_eq_true, if_false] at h
  by_cases e0 : rd < 2 <;> by_cases e2 : 0 ≤ (i : Int) + off ∧ (i : Int) + off < n <;> simp_all

theorem u0_lt31 {r : Nat} (hr : r < 32) : (RA.u0 r.toUInt64 < 31) = (mapped r = true ∧ r ≠ 0) := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨
    r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨
    r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem c0_jalr (rd rs : Nat) (i n : Nat) (hd : rd = 0) (hs : rs < 32)
    (h : RA.c0 (encG (.jalr rd rs)) i.toUInt64 n.toUInt64 = 1) : mapped rs = true ∧ rs ≠ 0 := by
  subst hd
  have hV := g2_sum C.g_103 0 (0 : Nat).toUInt64 rs.toUInt64 0 (by decide) (by decide) (by decide)
    (by rw [tU (by omega)]; omega)
  rw [tU (show rs < 2 ^ 64 by omega), show C.g_103.toNat = 103 from rfl, show (0 : UInt64).toNat = 0 from rfl,
    show (Nat.toUInt64 0).toNat = 0 from rfl] at hV
  simp only [encG] at h
  generalize C.g2 _ _ _ _ _ = v at hV h
  simp only [RA.c0] at h
  rw [o0_eq (r := 103) (by omega)] at h
  simp only [show ((103:Nat).toUInt64 == 19) = false from rfl, show ((103:Nat).toUInt64 == 3) = false from rfl,
    show ((103:Nat).toUInt64 == 35) = false from rfl, show ((103:Nat).toUInt64 == 51) = false from rfl,
    show ((103:Nat).toUInt64 == 99) = false from rfl, show ((103:Nat).toUInt64 == 111) = false from rfl,
    show ((103:Nat).toUInt64 == 103) = true from rfl, if_true, Bool.false_eq_true, if_false] at h
  rw [o2_eq (r := 0) (by omega), o1_eq (r := 0) (by omega), o3_eq (r := rs) (by omega),
    show (20 : UInt64) = (20 : Nat).toUInt64 from rfl, shr_eq (r := 0) (by omega) (by omega)] at h
  simp only [u0_lt31 hs, show ((103:Nat).toUInt64 == 19) = false from rfl, show ((103:Nat).toUInt64 == 3) = false from rfl,
    show ((103:Nat).toUInt64 == 35) = false from rfl, show ((103:Nat).toUInt64 == 51) = false from rfl,
    show ((103:Nat).toUInt64 == 99) = false from rfl, show ((103:Nat).toUInt64 == 111) = false from rfl,
    show ((103:Nat).toUInt64 == 103) = true from rfl, show ((0:Nat).toUInt64 == 0) = true from rfl,
    if_true, Bool.false_eq_true, if_false] at h
  by_cases e0 : mapped rs = true ∧ rs ≠ 0 <;> simp_all
/-- **rv2arm's validation is `armOK`** on Gen's words -/
theorem c0_ok (j : J) (hj : JOK j) (i n : Nat) (hi : i < n) (hn : n ≤ 2 ^ 18)
    (h : RA.c0 (encG j) i.toUInt64 n.toUInt64 = 1) : armOK n i j = true := by
  obtain ⟨hg, hjal⟩ := hj
  cases j with
  | addi rd rs imm => exact c0_addi rd rs imm i n hg h
  | ld rd rs f => exact c0_ld rd rs f i n hg h
  | sd r2 r1 f => exact c0_sd r2 r1 f i n hg h
  | lbu rd rs f => exact c0_lbu rd rs f i n hg h
  | sb r2 r1 f => exact c0_sb r2 r1 f i n hg h
  | alu op rd a b => exact c0_alu op rd a b i n hg h
  | slli rd rs sh =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2⟩ := c0_sh 1 (by omega) rd rs sh i n h1 h2 h3 h
    simp [armOK, m1, m2, h3]
  | srli rd rs sh =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (5 : UInt64) = (5 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2⟩ := c0_sh 5 (by omega) rd rs sh i n h1 h2 h3 h
    simp [armOK, m1, m2, h3]
  | beq a b off =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2, t1, t2⟩ := c0_br 0 (by omega) a b off i n h1 h2 (by omega) (by omega) hi hn h
    simp only [armOK, m1, m2, Bool.and_eq_true, decide_eq_true_eq, Bool.true_and]; omega
  | bne a b off =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2, t1, t2⟩ := c0_br 1 (by omega) a b off i n h1 h2 (by omega) (by omega) hi hn h
    simp only [armOK, m1, m2, Bool.and_eq_true, decide_eq_true_eq, Bool.true_and]; omega
  | bltu a b off =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (6 : UInt64) = (6 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2, t1, t2⟩ := c0_br 6 (by omega) a b off i n h1 h2 (by omega) (by omega) hi hn h
    simp only [armOK, m1, m2, Bool.and_eq_true, decide_eq_true_eq, Bool.true_and]; omega
  | bgeu a b off =>
    obtain ⟨h1, h2, h3⟩ := hg
    simp only [encG, show (7 : UInt64) = (7 : Nat).toUInt64 from rfl] at h
    obtain ⟨m1, m2, t1, t2⟩ := c0_br 7 (by omega) a b off i n h1 h2 (by omega) (by omega) hi hn h
    simp only [armOK, m1, m2, Bool.and_eq_true, decide_eq_true_eq, Bool.true_and]; omega
  | jal rd off =>
    obtain ⟨h3, h4⟩ := hjal rd off rfl
    obtain ⟨r2, t1, t2⟩ := c0_jal rd off i n hg h3 h4 hi hn h
    simp only [armOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]; omega
  | jalr rd rs =>
    obtain ⟨h1, h2⟩ := hg
    obtain ⟨m, r0⟩ := c0_jalr rd rs i n h1 h2 h
    simp [armOK, h1, m, r0]
end ArmRA

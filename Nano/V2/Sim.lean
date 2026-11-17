import Nano.V2.Enc
import Nano.V2.Expr
/- nano v2 small backend, proof layer 4b: one pc-level step (`pstep`, Nano/V2/Flat.lean) of encodable code is one
retired instruction of the Sail model, keeping the relation `Rel` between the abstract state and the Sail state
(registers, the work words as 8 LE bytes, the input and output bytes, the code bytes, the pc). -/
namespace Nano.V2B
open Proven

/-- where the code sits -/
structure Lay where
  base : Nat
  C : List I

/-- the layout: code, work, input, output inside RAM; the written blocks (work, output) disjoint from the read ones -/
structure Lay.Ok (K : Lay) (c : Cfg) : Prop where
  b4 : K.base % 4 = 0
  blo : 0x80000000 ≤ K.base
  bhi : K.base + 4 * K.C.length + 4 ≤ 0x100000000
  wf : ∀ i (h : i < K.C.length), (K.C[i]).wf = true
  jc : jcert K.C = true
  wlo : 0x80000000 ≤ c.lo
  whi : c.hi ≤ 0x100000000
  ilo : 0x80000000 ≤ c.ib
  ihi : c.ib + c.inp.length ≤ 0x100000000
  olo : 0x80000000 ≤ c.ob
  ohi : c.ob + c.ol ≤ 0x100000000
  cw : K.base + 4 * K.C.length ≤ c.lo ∨ c.hi ≤ K.base
  co : K.base + 4 * K.C.length ≤ c.ob ∨ c.ob + c.ol ≤ K.base
  iw : c.ib + c.inp.length ≤ c.lo ∨ c.hi ≤ c.ib
  io : c.ib + c.inp.length ≤ c.ob ∨ c.ob + c.ol ≤ c.ib
  wo : c.hi ≤ c.ob ∨ c.ob + c.ol ≤ c.lo

/-- the abstract state at instruction `pc` is the Sail state `t` -/
structure Rel (K : Lay) (c : Cfg) (p : Nat × St) (t : Proven.St) : Prop where
  cfg : Proven.Cfg t
  pc : t.regs.get? .PC = some (BitVec.ofNat 64 (K.base + 4 * p.1))
  code : ∀ i (h : i < K.C.length), instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 (K.C[i]).enc)
  x : ∀ j : Fin 32, getX t j = (p.2.get j.val).toBitVec
  w : ∀ a, c.wok a → ∀ k < 8, t.mem[a + k]? = some ((p.2.w a).toBitVec.extractLsb' (8 * k) 8)
  inp : ∀ k < c.inp.length, t.mem[c.ib + k]? = some (c.inp.getD k 0).toBitVec
  out : ∀ k < c.ol, t.mem[c.ob + k]? = some (p.2.o (c.ob + k)).toBitVec

theorem pcOK_of {K : Lay} {c : Cfg} (hK : K.Ok c) {pc : Nat} (h : pc < K.C.length) :
    pcOK (BitVec.ofNat 64 (K.base + 4 * pc)) := by
  have := hK.bhi; have := hK.blo; have := hK.b4
  have hlt : K.base + 4 * pc < 2 ^ 64 := by omega
  simp only [pcOK, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega

theorem ofNat_pc4 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 4 = BitVec.ofNat 64 (b + 4 * (pc + 1)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- a retired instruction that writes `rd` with `v` and steps the pc -/
theorem rel_reg {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t t' : Proven.St} (hR : Rel K c (pc, s) t) (rd : Fin 32)
    (v : UInt64) (hN : Next t t' (BitVec.ofNat 64 (K.base + 4 * pc) + 4) rd v.toBitVec t.mem) :
    Rel K c (pc + 1, s.set rd.val v) t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_pc4]
  code := fun i h => by
    have := hR.code i h; unfold instrAt at this ⊢; rw [hN.mem]; exact this
  x := fun j => by
    rw [hN.x j, get_set]
    by_cases hj : j = rd
    · subst hj
      by_cases h0 : j = 0
      · subst h0; simp; rfl
      · have : j.val ≠ 0 := fun e => h0 (Fin.ext e)
        simp [h0, this]
    · have : j.val ≠ rd.val := fun e => hj (Fin.ext e)
      simp only [hj, false_and, if_false, this]; exact hR.x j
  w := fun a ha k hk => by rw [hN.mem]; simpa using hR.w a ha k hk
  inp := fun k hk => by rw [hN.mem]; exact hR.inp k hk
  out := fun k hk => by rw [hN.mem]; simpa using hR.out k hk

theorem code_at {K : Lay} {c : Cfg} {p : Nat × St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c p t) {ins : I}
    (hC : K.C[p.1]? = some ins) :
    p.1 < K.C.length ∧ ins.wf = true ∧ instrAt t (BitVec.ofNat 64 (K.base + 4 * p.1)) (BitVec.ofNat 32 ins.enc) ∧
      pcOK (BitVec.ofNat 64 (K.base + 4 * p.1)) := by
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hC
  exact ⟨h1, h2 ▸ hK.wf _ h1, h2 ▸ hR.code _ h1, pcOK_of hK h1⟩

theorem shl_bv (a b : UInt64) : (a <<< (b % 64)).toBitVec = a.toBitVec <<< (b.toBitVec.toNat % 64) := by
  rw [UInt64.toBitVec_shiftLeft]; simp [BitVec.shiftLeft_eq', UInt64.toBitVec_mod]
theorem shr_bv (a b : UInt64) : (a >>> (b % 64)).toBitVec = a.toBitVec >>> (b.toBitVec.toNat % 64) := by
  rw [UInt64.toBitVec_shiftRight]; simp [BitVec.ushiftRight_eq', UInt64.toBitVec_mod]
theorem sltu_bv (a b : UInt64) :
    (if a < b then (1 : UInt64) else 0).toBitVec = if a.toBitVec < b.toBitVec then 1 else 0 := by
  by_cases h : a < b
  · rw [if_pos h, if_pos (UInt64.lt_iff_toBitVec_lt.1 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (UInt64.lt_iff_toBitVec_lt.2 h'))]; rfl

/-- **R-type** -/
theorem sim_r {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {f : ROp} {rd a b : Nat} (hC : K.C[pc]? = some (.r f rd a b)) :
    ∃ t', Retires t t' ∧ Rel K c (pc + 1, s.set rd (f.eval (s.get a) (s.get b))) t' := by
  obtain ⟨_, hw, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨hrd, ha, hb⟩, hadd⟩ := hw
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.get a).toBitVec := hR.x A
  have xb : getX t B = (s.get b).toBitVec := hR.x B
  cases f with
  | add =>
    have hrd0 : RD ≠ 0 := fun h => by simp [RD] at h; simp [h] at hadd
    obtain ⟨t', hN⟩ := G.step_add hR.cfg hR.pc hok RD A B hrd0 hi
    rw [xa, xb, ← UInt64.toBitVec_add] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | sub =>
    obtain ⟨t', hN⟩ := G.step_sub hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_sub] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | mul =>
    obtain ⟨t', hN⟩ := G.step_mul hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_mul] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | and =>
    obtain ⟨t', hN⟩ := G.step_and hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_and] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | or =>
    obtain ⟨t', hN⟩ := G.step_or hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_or] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | xor =>
    obtain ⟨t', hN⟩ := G.step_xor hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_xor] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | sll =>
    obtain ⟨t', hN⟩ := G.step_sll hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← shl_bv] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | srl =>
    obtain ⟨t', hN⟩ := G.step_srl hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← shr_bv] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | sltu =>
    obtain ⟨t', hN⟩ := G.step_sltu hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← sltu_bv] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩

theorem ofInt_bv (x : Int) : (UInt64.ofInt x).toBitVec = BitVec.ofInt 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, UInt64.toNat_toBitVec]
  unfold UInt64.ofInt; rw [UInt64.toNat_ofNat']
  have h1 : (0 : Int) ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h2 : x % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  omega

theorem sext_bits (imm : Int) (h1 : -2048 ≤ imm) (h2 : imm < 2048) :
    (BitVec.ofNat 12 (bits imm 12)).signExtend 64 = (UInt64.ofInt imm).toBitVec := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  rw [ofInt_bv, BitVec.toInt_ofInt, BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]
  unfold bits
  have hb : (imm % 2 ^ 12).toNat < 2 ^ 12 := by omega
  rw [Nat.mod_eq_of_lt hb]
  simp only [Int.bmod]
  split <;> split <;> omega

theorem shlK_bv (a : UInt64) (n : Nat) (h : n < 64) : (a <<< UInt64.ofNat n).toBitVec = a.toBitVec <<< n := by
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq']; congr 1
  simp [UInt64.toBitVec_ofNat, BitVec.toNat_umod]; omega
theorem shrK_bv (a : UInt64) (n : Nat) (h : n < 64) : (a >>> UInt64.ofNat n).toBitVec = a.toBitVec >>> n := by
  rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq']; congr 1
  simp [UInt64.toBitVec_ofNat, BitVec.toNat_umod]; omega

theorem imm12_toNat (imm : Int) : (BitVec.ofNat 12 (bits imm 12)).toNat = bits imm 12 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bits_lt imm 12)]

/-- **I-type ALU** -/
theorem sim_i {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {f : IOp} {rd a : Nat} {imm : Int} (hC : K.C[pc]? = some (.i f rd a imm)) :
    ∃ t', Retires t t' ∧ Rel K c (pc + 1, s.set rd (f.eval (s.get a) imm)) t' := by
  obtain ⟨_, hw, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hrd, ha⟩, hori⟩, himm⟩ := hw
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have xa : getX t A = (s.get a).toBitVec := hR.x A
  cases f with
  | addi =>
    simp only [decide_eq_true_eq] at himm
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 0 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by rw [imm12_toNat]; exact hi
    obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc hok RD A _ hi'
    rw [xa, sext_bits imm himm.1 himm.2, ← UInt64.toBitVec_add] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | andi =>
    simp only [decide_eq_true_eq] at himm
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 7 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by rw [imm12_toNat]; exact hi
    obtain ⟨t', hN⟩ := G.step_andi hR.cfg hR.pc hok RD A _ hi'
    rw [xa, sext_bits imm himm.1 himm.2, ← UInt64.toBitVec_and] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | ori =>
    simp only [decide_eq_true_eq] at himm
    have hrd0 : RD ≠ 0 := fun h => by simp [RD] at h; simp [h] at hori
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 6 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by rw [imm12_toNat]; exact hi
    obtain ⟨t', hN⟩ := G.step_ori hR.cfg hR.pc hok RD A _ hrd0 hi'
    rw [xa, sext_bits imm himm.1 himm.2, ← UInt64.toBitVec_or] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | xori =>
    simp only [decide_eq_true_eq] at himm
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 4 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by rw [imm12_toNat]; exact hi
    obtain ⟨t', hN⟩ := G.step_xori hR.cfg hR.pc hok RD A _ hi'
    rw [xa, sext_bits imm himm.1 himm.2, ← UInt64.toBitVec_xor] at hN; exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩
  | slli =>
    simp only [decide_eq_true_eq] at himm
    have hn : imm.toNat < 64 := by omega
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 1 (0 <<< 6 ||| (BitVec.ofNat 6 imm.toNat).toNat) RD A) := by
      rw [show 0 <<< 6 ||| (BitVec.ofNat 6 imm.toNat).toNat = bits imm 12 by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; unfold bits; simp; omega]; exact hi
    obtain ⟨t', hN⟩ := G.step_slli hR.cfg hR.pc hok RD A _ hi'
    rw [xa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, ← shlK_bv _ _ hn] at hN
    refine ⟨t', hN.ret, ?_⟩
    have := rel_reg hR RD _ hN
    simpa [IOp.eval, Nat.mod_eq_of_lt hn] using this
  | srli =>
    simp only [decide_eq_true_eq] at himm
    have hn : imm.toNat < 64 := by omega
    have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 imm.toNat).toNat) RD A) := by
      rw [show 0 <<< 6 ||| (BitVec.ofNat 6 imm.toNat).toNat = bits imm 12 by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; unfold bits; simp; omega]; exact hi
    obtain ⟨t', hN⟩ := G.step_srli hR.cfg hR.pc hok RD A _ hi'
    rw [xa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, ← shrK_bv _ _ hn] at hN
    refine ⟨t', hN.ret, ?_⟩
    have := rel_reg hR RD _ hN
    simpa [IOp.eval, Nat.mod_eq_of_lt hn] using this

end Nano.V2B

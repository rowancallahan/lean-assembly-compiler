import Nano.Base.V2.Enc
import Nano.Base.V2.Expr
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

/-! ## memory -/

theorem storeBytes_get : ∀ (m : Mem) (a : Nat) (l : List (BitVec 8)) (x : Nat),
    (storeBytes m a l)[x]? = if a ≤ x ∧ x < a + l.length then some (l.getD (x - a) 0) else m[x]?
  | m, a, [], x => by simp [storeBytes, writeCells]; omega
  | m, a, v :: l, x => by
    show (writeCells (m.insert a v) (List.range' (a + 1) l.length) l)[x]? = _
    have := storeBytes_get (m.insert a v) (a + 1) l x
    unfold storeBytes at this; rw [this, Std.ExtHashMap.getElem?_insert]
    by_cases hx : x = a
    · subst hx; simp; omega
    · by_cases h1 : a + 1 ≤ x ∧ x < a + 1 + l.length
      · rw [if_pos h1, if_pos (by simp; omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [show x - a = (x - (a + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg h1, if_neg (by simp; omega)]
        simp; intro h3 h4; omega

theorem le8_getD (v : BitVec 64) (k : Nat) (hk : k < 8) : (le8 v).getD k 0 = v.extractLsb' (8 * k) 8 := by
  simp [le8, List.getD_eq_getElem?_getD, hk]

/-- the effective address of a load/store: the abstract `ea` -/
theorem ea_bv {K : Lay} {c : Cfg} {p : Nat × St} {t : Proven.St} (hR : Rel K c p t) (A : Fin 32) (off : Int)
    (h1 : -2048 ≤ off) (h2 : off < 2048) :
    getX t A + (BitVec.ofNat 12 (bits off 12)).signExtend 64 = BitVec.ofNat 64 (ea p.2 A.val off) := by
  rw [hR.x A, sext_bits off h1 h2, ← UInt64.toBitVec_add]; apply BitVec.eq_of_toNat_eq; simp [ea]

theorem toNat_lt64 {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem imm12S_toNat (imm : Int) : (BitVec.ofNat 12 (bits imm 12)) = BitVec.ofNat 12 (bits imm 12) := rfl

/-- **ld** -/
theorem sim_ld {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {rd a : Nat} {off : Int} (hC : K.C[pc]? = some (.ld rd a off)) (hw : c.wok (ea s a off)) :
    ∃ t', Retires t t' ∧ Rel K c (pc + 1, s.set rd (s.w (ea s a off))) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨hrd, ha, h1, h2⟩ := hwf
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hea := ea_bv hR A off h1 h2
  have hW := hK.wlo; have hH := hK.whi
  have hlt : ea s a off < 2 ^ 64 := by unfold Cfg.wok at hw; omega
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encL 3 (BitVec.ofNat 12 (bits off 12)) RD A) := by
    unfold G.encL; rw [imm12_toNat]; exact hi
  have hb := fun k (hk : k < 8) => hR.w _ hw k hk
  obtain ⟨t', hN⟩ := G.step_ld hR.cfg hR.pc hok RD A _ hi' hea (by rw [toNat_lt64 hlt]; unfold Cfg.wok at hw; omega)
    (by rw [toNat_lt64 hlt]; exact hw.2.2)
    (by rw [toNat_lt64 hlt]; exact hb 0 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 1 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 2 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 3 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 4 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 5 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 6 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 7 (by decide))
  rw [cat8_extract] at hN
  exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩

theorem store8_out (m : Mem) (A : Nat) (v : BitVec 64) (x : Nat) (h : x < A ∨ A + 8 ≤ x) :
    (storeBytes m A (le8 v))[x]? = m[x]? := by
  rw [storeBytes_get, if_neg (by simp [le8]; omega)]
theorem store8_in (m : Mem) (A : Nat) (v : BitVec 64) (k : Nat) (hk : k < 8) :
    (storeBytes m A (le8 v))[A + k]? = some (v.extractLsb' (8 * k) 8) := by
  rw [storeBytes_get, if_pos (by simp [le8]; omega), show A + k - A = k by omega, le8_getD v k hk]

theorem encSt_bits (f3 b a : Nat) (off : Int) : encSt f3 b a off = encSt f3 b a ((bits off 12 : Nat) : Int) := by
  unfold encSt; rw [bits_nat _ 12 (bits_lt off 12)]

/-- a retired store keeps everything but the stored bytes -/
theorem rel_mem {K : Lay} {c : Cfg} {pc : Nat} {s s' : St} {t t' : Proven.St} (hK : K.Ok c)
    (hR : Rel K c (pc, s) t) {m : Mem}
    (hN : Next t t' (BitVec.ofNat 64 (K.base + 4 * pc) + 4) 0 0 m) (hx : s'.x = s.x)
    (hcode : ∀ x, K.base ≤ x → x < K.base + 4 * K.C.length → m[x]? = t.mem[x]?)
    (hw : ∀ a, c.wok a → ∀ k < 8, m[a + k]? = some ((s'.w a).toBitVec.extractLsb' (8 * k) 8))
    (hi : ∀ k < c.inp.length, m[c.ib + k]? = t.mem[c.ib + k]?)
    (ho : ∀ k < c.ol, m[c.ob + k]? = some (s'.o (c.ob + k)).toBitVec) :
    Rel K c (pc + 1, s') t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_pc4]
  code := fun i h => by
    have hc := hR.code i h
    have hlt : K.base + 4 * i < 2 ^ 64 := by have := hK.bhi; omega
    unfold instrAt at hc ⊢; rw [hN.mem]; rw [toNat_lt64 hlt] at hc ⊢
    obtain ⟨h0, h1, h2, h3⟩ := hc
    exact ⟨by rw [hcode _ (by omega) (by omega)]; exact h0, by rw [hcode _ (by omega) (by omega)]; exact h1,
      by rw [hcode _ (by omega) (by omega)]; exact h2, by rw [hcode _ (by omega) (by omega)]; exact h3⟩
  x := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false, hR.x j]
    simp [St.get, hx]
  w := fun a ha k hk => by rw [hN.mem]; exact hw a ha k hk
  inp := fun k hk => by rw [hN.mem, hi k hk]; exact hR.inp k hk
  out := fun k hk => by rw [hN.mem]; exact ho k hk

/-- **sd** -/
theorem sim_sd {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {b a : Nat} {off : Int} (hC : K.C[pc]? = some (.sd b a off)) (hw : c.wok (ea s a off)) :
    ∃ t', Retires t t' ∧
      Rel K c (pc + 1, { s with w := fun j => if j = ea s a off then s.get b else s.w j }) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨hb, ha, h1, h2⟩ := hwf
  let B : Fin 32 := ⟨b, hb⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hea := ea_bv hR A off h1 h2
  have hW := hK.wlo; have hH := hK.whi
  have hlt : ea s a off < 2 ^ 64 := by unfold Cfg.wok at hw; omega
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encS 3 (BitVec.ofNat 12 (bits off 12)) B A) := by
    have e := encSt_eq 3 (by decide) B A (bits off 12) (bits_lt off 12)
    have hi2 : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc))
        (BitVec.ofNat 32 (encSt 3 B.val A.val ((bits off 12 : Nat) : Int))) := by rw [← encSt_bits]; exact hi
    rw [e] at hi2; exact hi2
  obtain ⟨t', hN⟩ := G.step_sd hR.cfg hR.pc hok B A _ hi' hea (by rw [toNat_lt64 hlt]; unfold Cfg.wok at hw; omega)
    (by rw [toNat_lt64 hlt]; exact hw.2.2)
  rw [toNat_lt64 hlt, hR.x B] at hN
  have hwk := hw
  unfold Cfg.wok at hwk
  refine ⟨t', hN.ret, rel_mem hK hR hN rfl ?_ ?_ ?_ ?_⟩
  · intro x hx1 hx2; apply store8_out; have := hK.cw; omega
  · intro a' ha' k hk
    by_cases he : a' = ea s a off
    · subst he; rw [store8_in _ _ _ k hk]; simp; rfl
    · have := ha'.2.2; rw [store8_out _ _ _ _ (by omega)]
      rw [hR.w a' ha' k hk]; simp [he]
  · intro k hk; apply store8_out; have := hK.iw; omega
  · intro k hk; rw [store8_out _ _ _ _ (by have := hK.wo; omega)]; exact hR.out k hk

/-- **lbu** (input bytes) -/
theorem sim_lbu {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {rd a : Nat} {off : Int} (hC : K.C[pc]? = some (.lbu rd a off))
    (hin : c.ib ≤ ea s a off ∧ ea s a off < c.ib + c.inp.length) :
    ∃ t', Retires t t' ∧ Rel K c (pc + 1, s.set rd (c.inp.getD (ea s a off - c.ib) 0).toUInt64) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨hrd, ha, h1, h2⟩ := hwf
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hea := ea_bv hR A off h1 h2
  have hI := hK.ilo; have hJ := hK.ihi
  have hlt : ea s a off < 2 ^ 64 := by omega
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encL 4 (BitVec.ofNat 12 (bits off 12)) RD A) := by
    unfold G.encL; rw [imm12_toNat]; exact hi
  have hb := hR.inp (ea s a off - c.ib) (by omega)
  rw [show c.ib + (ea s a off - c.ib) = ea s a off by omega] at hb
  obtain ⟨t', hN⟩ := G.step_lbu hR.cfg hR.pc hok RD A _ hi' hea (by rw [toNat_lt64 hlt]; omega)
    (by rw [toNat_lt64 hlt]; exact hb)
  rw [← UInt8.toBitVec_toUInt64] at hN
  exact ⟨t', hN.ret, rel_reg hR RD _ hN⟩

/-- **sb** (output bytes) -/
theorem sim_sb {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {b a : Nat} {off : Int} (hC : K.C[pc]? = some (.sb b a off))
    (hout : c.ob ≤ ea s a off ∧ ea s a off < c.ob + c.ol) :
    ∃ t', Retires t t' ∧
      Rel K c (pc + 1, { s with o := fun j => if j = ea s a off then (s.get b).toUInt8 else s.o j }) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨hb, ha, h1, h2⟩ := hwf
  let B : Fin 32 := ⟨b, hb⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hea := ea_bv hR A off h1 h2
  have hO := hK.olo; have hP := hK.ohi
  have hlt : ea s a off < 2 ^ 64 := by omega
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encS 0 (BitVec.ofNat 12 (bits off 12)) B A) := by
    have e := encSt_eq 0 (by decide) B A (bits off 12) (bits_lt off 12)
    have hi2 : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc))
        (BitVec.ofNat 32 (encSt 0 B.val A.val ((bits off 12 : Nat) : Int))) := by rw [← encSt_bits]; exact hi
    rw [e] at hi2; exact hi2
  obtain ⟨t', hN⟩ := G.step_sb hR.cfg hR.pc hok B A _ hi' hea (by rw [toNat_lt64 hlt]; omega)
  rw [toNat_lt64 hlt, hR.x B] at hN
  refine ⟨t', hN.ret, rel_mem hK hR hN rfl ?_ ?_ ?_ ?_⟩
  · intro x hx1 hx2; rw [Std.ExtHashMap.getElem?_insert, if_neg (by have := hK.co; simp; omega)]
  · intro a' ha' k hk
    have := ha'.1; have := ha'.2.1
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by have := hK.wo; simp; omega)]; exact hR.w a' ha' k hk
  · intro k hk; rw [Std.ExtHashMap.getElem?_insert, if_neg (by have := hK.io; simp; omega)]
  · intro k hk
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases he : ea s a off = c.ob + k
    · rw [if_pos (by simp [he])]; simp [he]; rfl
    · rw [if_neg (by simp [he])]; simp only [Ne.symm he, if_false]; exact hR.out k hk

/-! ## control transfers -/

/-- a retired instruction that only moves the pc -/
theorem rel_jump {K : Lay} {c : Cfg} {pc pc' : Nat} {s : St} {t t' : Proven.St} (hR : Rel K c (pc, s) t)
    (hN : Next t t' (BitVec.ofNat 64 (K.base + 4 * pc')) 0 0 t.mem) : Rel K c (pc', s) t' where
  cfg := hN.cfg
  pc := hN.pc
  code := fun i h => by have := hR.code i h; unfold instrAt at this ⊢; rw [hN.mem]; exact this
  x := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact hR.x j
  w := fun a ha k hk => by rw [hN.mem]; exact hR.w a ha k hk
  inp := fun k hk => by rw [hN.mem]; exact hR.inp k hk
  out := fun k hk => by rw [hN.mem]; exact hR.out k hk

theorem app0_toNat' {w} (x : BitVec w) : (x +++ (0#1 : BitVec 1)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq]; omega

theorem boff8 : boff (4#12) = 8#64 := by decide

theorem pc_plus8 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 8#64 = BitVec.ofNat 64 (b + 4 * (pc + 2)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- **branches** (`+8`, over the following `jal`) -/
theorem sim_br {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {k : BOp} {a b : Nat} {off : Int} (hC : K.C[pc]? = some (.br k a b off)) :
    ∃ t', Retires t t' ∧
      Rel K c (if k.eval (s.get a) (s.get b) then jt pc off else pc + 1, s) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨ha, hb, rfl⟩ := hwf
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.get a).toBitVec := hR.x A
  have xb : getX t B = (s.get b).toBitVec := hR.x B
  have hj : jt pc 8 = pc + 2 := by unfold jt; omega
  rw [hj]
  have tk : ∀ {t'}, Next t t' (BitVec.ofNat 64 (K.base + 4 * pc) + boff 4#12) 0 0 t.mem → Rel K c (pc + 2, s) t' :=
    fun hN => rel_jump hR (by rw [boff8, pc_plus8] at hN; exact hN)
  have nt : ∀ {t'}, Next t t' (BitVec.ofNat 64 (K.base + 4 * pc) + 4) 0 0 t.mem → Rel K c (pc + 1, s) t' :=
    fun hN => rel_jump hR (by rw [ofNat_pc4] at hN; exact hN)
  cases k with
  | beq =>
    have e := encBt8_eq 0 (by decide) A B
    have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 0 A.val B.val 8)) := hi
    rw [e] at hi2
    by_cases hc : s.get a = s.get b
    · obtain ⟨t', hN⟩ := G.beq_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
      exact ⟨t', hN.ret, by simp only [BOp.eval, hc, beq_self_eq_true, if_true]; exact tk hN⟩
    · obtain ⟨t', hN⟩ := G.beq_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
      exact ⟨t', hN.ret, by simp only [BOp.eval, beq_iff_eq, hc, if_false]; exact nt hN⟩
  | bne =>
    have e := encBt8_eq 1 (by decide) A B
    have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 1 A.val B.val 8)) := hi
    rw [e] at hi2
    by_cases hc : s.get a = s.get b
    · obtain ⟨t', hN⟩ := G.bne_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
      exact ⟨t', hN.ret, by simp only [BOp.eval, hc, bne_self_eq_false, Bool.false_eq_true, if_false]; exact nt hN⟩
    · obtain ⟨t', hN⟩ := G.bne_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
      exact ⟨t', hN.ret, by simp only [BOp.eval, bne_iff_ne, ne_eq, hc, not_false_eq_true, if_true]; exact tk hN⟩
  | bltu =>
    have e := encBt8_eq 6 (by decide) A B
    have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 6 A.val B.val 8)) := hi
    rw [e] at hi2
    by_cases hc : s.get a < s.get b
    · obtain ⟨t', hN⟩ := G.bltu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
      exact ⟨t', hN.ret, by simp only [BOp.eval, hc, decide_true, if_true]; exact tk hN⟩
    · obtain ⟨t', hN⟩ := G.bltu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
      exact ⟨t', hN.ret, by simp only [BOp.eval, hc, decide_false, Bool.false_eq_true, if_false]; exact nt hN⟩
  | bgeu =>
    have e := encBt8_eq 7 (by decide) A B
    have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 7 A.val B.val 8)) := hi
    rw [e] at hi2
    by_cases hc : s.get a < s.get b
    · obtain ⟨t', hN⟩ := G.bgeu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
      have : ¬ s.get b ≤ s.get a := fun h => absurd hc (UInt64.not_lt.2 h)
      exact ⟨t', hN.ret, by simp only [BOp.eval, this, decide_false, Bool.false_eq_true, if_false]; exact nt hN⟩
    · obtain ⟨t', hN⟩ := G.bgeu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
      have : s.get b ≤ s.get a := UInt64.not_lt.1 hc
      exact ⟨t', hN.ret, by simp only [BOp.eval, this, decide_true, if_true]; exact tk hN⟩

theorem joff_int (v : Nat) (hv : v < 2 ^ 20) (off : Int) (h1 : -2 ^ 20 ≤ off) (h2 : off < 2 ^ 20)
    (he : bits off 21 = 2 * v) : joff (BitVec.ofNat 20 v) = BitVec.ofInt 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp [joff, BitVec.toNat_signExtend, BitVec.msb_eq_decide, app0_toNat', BitVec.toNat_ofInt]
  unfold bits at he
  have hv' : v % 2 ^ 20 = v := Nat.mod_eq_of_lt hv
  rw [hv']
  split <;> omega

theorem jcert_at {C : List I} (hc : jcert C = true) {pc : Nat} {off : Int} (h : C[pc]? = some (.jal off)) :
    0 ≤ (pc : Int) + off / 4 ∧ (pc : Int) + off / 4 ≤ C.length := by
  unfold jcert at hc
  have hpc := (List.getElem?_eq_some_iff.1 h).1
  have := List.all_eq_true.1 hc pc (List.mem_range.2 hpc)
  simp only [h, decide_eq_true_eq] at this; exact this

/-- **jal x0** (to a certified label) -/
theorem sim_jal {K : Lay} {c : Cfg} {pc : Nat} {s : St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c (pc, s) t)
    {off : Int} (hC : K.C[pc]? = some (.jal off)) : ∃ t', Retires t t' ∧ Rel K c (jt pc off, s) t' := by
  obtain ⟨_, hwf, hi, hok⟩ := code_at hK hR hC
  simp only [I.wf, decide_eq_true_eq] at hwf
  obtain ⟨h4, h1, h2⟩ := hwf
  obtain ⟨j1, j2⟩ := jcert_at hK.jc hC
  have hb := bits_lt off 21
  have heven : bits off 21 % 2 = 0 := by unfold bits; omega
  let v := bits off 21 / 2
  have he : bits off 21 = 2 * v := by omega
  have hv : v < 2 ^ 20 := by omega
  have hi2 : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (BitVec.ofNat 32 (encJt ((2 * v : Nat) : Int))) := by
    have : encJt off = encJt ((2 * v : Nat) : Int) := by
      unfold encJt; rw [bits_nat (2 * v) 21 (by omega), ← he]
    rw [← this]; exact hi
  rw [encJt_eq v hv] at hi2
  obtain ⟨t', hN⟩ := G.step_jal hR.cfg hR.pc hok 0 _ hi2
  rw [joff_int v hv off (by omega) (by omega) he] at hN
  have e : BitVec.ofNat 64 (K.base + 4 * pc) + BitVec.ofInt 64 off = BitVec.ofNat 64 (K.base + 4 * jt pc off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt, jt]
    have := hK.bhi; omega
  have hN' : Next t t' (BitVec.ofNat 64 (K.base + 4 * jt pc off)) 0 0 t.mem :=
    ⟨hN.ret, hN.cfg, by rw [hN.pc, e], fun j => by
      rw [hN.x j]; simp only [show ¬ (j = (0 : Fin 32) ∧ j ≠ 0) from fun h => h.2 h.1, if_false], hN.mem⟩
  exact ⟨t', hN.ret, rel_jump hR hN'⟩

/-- **one pc-level step is one retired Sail instruction** -/
theorem sim_step {K : Lay} {c : Cfg} {p q : Nat × St} {t : Proven.St} (hK : K.Ok c) (hR : Rel K c p t)
    (h : pstep c K.C p = some q) : ∃ t', Retires t t' ∧ Rel K c q t' := by
  obtain ⟨pc, s⟩ := p
  unfold pstep at h
  cases hC : K.C[pc]? with
  | none => simp [hC] at h
  | some ins =>
    simp only [hC] at h
    cases ins with
    | br k a b off => simp only [Option.some.injEq] at h; subst h; exact sim_br hK hR hC
    | jal off => simp only [Option.some.injEq] at h; subst h; exact sim_jal hK hR hC
    | r f rd a b => simp only [I.run, Option.map_some, Option.some.injEq] at h; subst h; exact sim_r hK hR hC
    | i f rd a imm => simp only [I.run, Option.map_some, Option.some.injEq] at h; subst h; exact sim_i hK hR hC
    | ld rd a off =>
      simp only [I.run] at h; split at h
      · rename_i hw; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact sim_ld hK hR hC hw
      · simp at h
    | sd b a off =>
      simp only [I.run] at h; split at h
      · rename_i hw; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact sim_sd hK hR hC hw
      · simp at h
    | lbu rd a off =>
      simp only [I.run] at h; split at h
      · rename_i hw; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact sim_lbu hK hR hC hw
      · simp at h
    | sb b a off =>
      simp only [I.run] at h; split at h
      · rename_i hw; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact sim_sb hK hR hC hw
      · simp at h
    | ret => simp [I.run] at h

/-- **a pc-level run is a Sail run** -/
theorem sim_star {K : Lay} {c : Cfg} (hK : K.Ok c) {p q : Nat × St} (h : PStar c K.C p q) :
    ∀ {t : Proven.St}, Rel K c p t → ∃ n t', Steps n t t' ∧ Rel K c q t' := by
  induction h with
  | refl p => intro t hR; exact ⟨0, t, rfl, hR⟩
  | step e _ ih =>
    intro t hR
    obtain ⟨t1, hr, hR1⟩ := sim_step hK hR e
    obtain ⟨n, t', hs, hR'⟩ := ih hR1
    exact ⟨n + 1, t', ⟨t1, hr, hs⟩, hR'⟩

/-- the Sail model is deterministic: a state retires into at most one state -/
theorem Retires.det {t a b : Proven.St} (ha : Retires t a) (hb : Retires t b) : a = b := by
  have := ha.2.symm.trans hb.2
  cases this; rfl

end Nano.V2B

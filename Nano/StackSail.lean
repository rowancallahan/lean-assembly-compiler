/- Route (a): the record machine (`Nano.R`, `Nano/StackRec.lean`) is refined by the Sail RV64 model.  For code
`asm P` loaded at `pc0` and `P` made of family records (`Nano/StackFam.lean`), every record step is one retired Sail
instruction (`sim`), and `ret` returns to `ra` (`sim_halt`).  The relation `Rel`: same registers, pc = pc0 + 4·index,
the record machine's bytes are Sail's on the input, work and output blocks, and Sail's memory outside work and the 8
output bytes is the start state's. -/
import Nano.StackFam
import Riscv.Back.Top

set_option linter.unusedVariables false

namespace Nano.S
open Proven Proven.G Nano Nano.R Nano.F

/-- the fixed data of a run -/
structure Ctx where
  t0 : Proven.St
  pc0 : Nat
  P : List UInt8
  W : Nat
  SP : Nat
  I : Nat
  IL : Nat
  O : Nat
  RA : Nat

/-- the blocks whose bytes the record machine tracks -/
def Ctx.In (C : Ctx) (a : Nat) : Prop :=
  (C.W ≤ a ∧ a < C.SP) ∨ (C.O ≤ a ∧ a < C.O + 8) ∨ (C.I ≤ a ∧ a < C.I + C.IL)

/-- what the code and the blocks satisfy -/
structure Ctx.Ok (C : Ctx) : Prop where
  p4 : C.P.length % 4 = 0
  code : ∀ k (hk : k < (asm C.P).length), C.t0.mem[C.pc0 + k]? = some ((asm C.P)[k]).toBitVec
  pcal : C.pc0 % 4 = 0
  pclo : 0x80000000 ≤ C.pc0
  pchi : C.pc0 + C.P.length ≤ 0x100000000
  cW : C.pc0 + C.P.length ≤ C.W ∨ C.SP ≤ C.pc0
  cO : C.pc0 + C.P.length ≤ C.O ∨ C.O + 8 ≤ C.pc0
  wlo : 0x80000000 ≤ C.W
  whi : C.SP ≤ 0x100000000
  wsp : C.W ≤ C.SP
  olo : 0x80000000 ≤ C.O
  ohi : C.O + 8 ≤ 0x100000000
  ilo : 0x80000000 ≤ C.I
  ihi : C.I + C.IL ≤ 0x100000000
  fam : allFam C.P = true
  ra : C.RA % 4 = 0 ∧ C.RA < 2 ^ 64

/-- the record state `s` is the Sail state `t` -/
structure Rel (C : Ctx) (s : R.St) (t : Proven.St) : Prop where
  cfg : Cfg t
  pc : t.regs.get? .PC = some (BitVec.ofNat 64 (C.pc0 + 4 * s.pc))
  x : ∀ j : Fin 32, getX t j = s.get j.val
  r12 : s.get 12 = BitVec.ofNat 64 C.W
  r2 : s.get 2 = BitVec.ofNat 64 C.SP
  r1 : s.get 1 = BitVec.ofNat 64 C.RA
  g : s.g = ⟨C.I, C.IL, C.O⟩
  mem : ∀ a, C.In a → t.mem[a]? = some (s.m a).toBitVec
  frame : ∀ a, ¬ (C.W ≤ a ∧ a < C.SP) → ¬ (C.O ≤ a ∧ a < C.O + 8) → t.mem[a]? = C.t0.mem[a]?

theorem ofNat_add4 (a : Nat) : BitVec.ofNat 64 a + 4 = BitVec.ofNat 64 (a + 4) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem get_set_fin (s : R.St) (r : Nat) (v : BitVec 64) (j : Nat) :
    (s.set r v).get j = if j = 0 then 0 else if j = r then v else s.get j := by
  simp only [St.get, St.set]; by_cases h : j = 0 <;> simp [h]

/-- a retired instruction that writes register `rd` and steps the pc -/
theorem rel_reg {C : Ctx} {s : R.St} {t t' : Proven.St} (hR : Rel C s t) {rd : Fin 32} {v : BitVec 64}
    (hN : Next t t' (BitVec.ofNat 64 (C.pc0 + 4 * s.pc) + 4) rd v t.mem) (h12 : rd.val ≠ 12) (h2 : rd.val ≠ 2)
    (h1 : rd.val ≠ 1) :
    Rel C ((({ s with pc := s.pc + 1 } : R.St)).set rd.val v) t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_add4]; congr 2
  x := fun j => by
    rw [hN.x j, get_set_fin]
    by_cases hj : j = 0
    · subst hj; simp
    · have hj' : j.val ≠ 0 := fun e => hj (Fin.ext e)
      by_cases hjr : j = rd
      · subst hjr; simp [hj', hj]
      · have : j.val ≠ rd.val := fun e => hjr (Fin.ext e)
        simp only [hj', this, hjr, false_and, if_false]; exact hR.x j
  r12 := by rw [get_set_ne _ (Ne.symm h12)]; exact hR.r12
  r2 := by rw [get_set_ne _ (Ne.symm h2)]; exact hR.r2
  r1 := by rw [get_set_ne _ (Ne.symm h1)]; exact hR.r1
  g := hR.g
  mem := fun a ha => by rw [hN.mem]; exact hR.mem a ha
  frame := fun a h1 h2 => by rw [hN.mem]; exact hR.frame a h1 h2

/-- a retired instruction that only steps the pc by `k` records -/
theorem rel_pc {C : Ctx} {s : R.St} {t t' : Proven.St} (hR : Rel C s t) (k : Nat)
    (hN : Next t t' (BitVec.ofNat 64 (C.pc0 + 4 * s.pc) + BitVec.ofNat 64 (4 * k)) 0 0 t.mem) :
    Rel C { s with pc := s.pc + k } t' where
  cfg := hN.cfg
  pc := by rw [hN.pc]; apply congrArg some; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  x := fun j => by rw [hN.x j]; by_cases hj : j = 0 <;> simp [hj] <;> first | rfl | exact hR.x j
  r12 := hR.r12
  r2 := hR.r2
  r1 := hR.r1
  g := hR.g
  mem := fun a ha => by rw [hN.mem]; exact hR.mem a ha
  frame := fun a h1 h2 => by rw [hN.mem]; exact hR.frame a h1 h2

theorem le8_length' (v : BitVec 64) : (le8 v).length = 8 := by simp [le8]

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

theorem le8_byte' (w : BitVec 64) (j : Nat) :
    w.extractLsb' (8 * j) 8 = (UInt8.ofNat (w.toNat / 256 ^ j % 256)).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  show _ = (UInt8.ofNat (w.toNat / 256 ^ j % 256)).toNat
  rw [UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

theorem le8_leN (w : BitVec 64) : le8 w = (leN 8 w.toNat).map (·.toBitVec) := by
  simp only [le8, List.range, List.range.loop, List.map, leN, le8_byte']
  simp [Nat.div_div_eq_div_mul]

/-- a retired `sd` of `v` at `A` (in the work block) -/
theorem rel_sd {C : Ctx} {s : R.St} {t t' : Proven.St} (hR : Rel C s t) {A : Nat} (hA : C.W ≤ A ∧ A + 8 ≤ C.SP)
    {v : BitVec 64} (hN : Next t t' (BitVec.ofNat 64 (C.pc0 + 4 * s.pc) + 4) 0 0 (storeBytes t.mem A (le8 v))) :
    Rel C { s with pc := s.pc + 1, m := wr64 s.m A v } t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_add4]; congr 2
  x := fun j => by rw [hN.x j]; by_cases hj : j = 0 <;> simp [hj] <;> first | rfl | exact hR.x j
  r12 := hR.r12
  r2 := hR.r2
  r1 := hR.r1
  g := hR.g
  mem := fun a ha => by
    rw [hN.mem, storeBytes_get]
    show _ = some (wrL s.m A (leN 8 v.toNat) a).toBitVec
    unfold wrL; rw [le8_length' v, leN_length]
    by_cases h : A ≤ a ∧ a < A + 8
    · rw [if_pos h, if_pos h, le8_leN]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      have : a - A < (leN 8 v.toNat).length := by rw [leN_length]; omega
      rw [List.getElem?_eq_getElem this]; rfl
    · rw [if_neg h, if_neg h]; exact hR.mem a ha
  frame := fun a h1 h2 => by
    rw [hN.mem, storeBytes_get, le8_length', if_neg (by omega)]; exact hR.frame a h1 h2

/-- a retired `sb` of the low byte of `v` at `A` (an output byte) -/
theorem rel_sb {C : Ctx} {s : R.St} {t t' : Proven.St} (hR : Rel C s t) {A : Nat} (hA : C.O ≤ A ∧ A < C.O + 8)
    {v : BitVec 64} (hN : Next t t' (BitVec.ofNat 64 (C.pc0 + 4 * s.pc) + 4) 0 0 (t.mem.insert A (v.setWidth 8))) :
    Rel C { s with pc := s.pc + 1, m := wrL s.m A [UInt8.ofBitVec (v.setWidth 8)] } t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_add4]; congr 2
  x := fun j => by rw [hN.x j]; by_cases hj : j = 0 <;> simp [hj] <;> first | rfl | exact hR.x j
  r12 := hR.r12
  r2 := hR.r2
  r1 := hR.r1
  g := hR.g
  mem := fun a ha => by
    rw [hN.mem, Std.ExtHashMap.getElem?_insert]
    show _ = some (wrL s.m A [UInt8.ofBitVec (v.setWidth 8)] a).toBitVec
    unfold wrL
    by_cases h : a = A
    · subst h; simp
    · rw [if_neg (by simp; omega), if_neg (by simp; omega)]; exact hR.mem a ha
  frame := fun a h1 h2 => by
    rw [hN.mem, Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)]; exact hR.frame a h1 h2

/-! ## fetching the record's word -/

theorem asm_drop : ∀ (P : List UInt8) (i : Nat), (asm P).drop (4 * i) = asm (P.drop (4 * i))
  | P, 0 => by simp
  | op :: a :: b :: c :: rest, i + 1 => by
    rw [show 4 * (i + 1) = 4 * i + 4 by omega]
    show (asm rest).drop (4 * i) = _
    rw [asm_drop rest i]; simp
  | [], i + 1 => by simp [asm]
  | [x], i + 1 => by rw [List.drop_eq_nil_of_le (as := [x]) (by simp; omega)]; simp [asm]
  | [x, y], i + 1 => by rw [List.drop_eq_nil_of_le (as := [x, y]) (by simp; omega)]; simp [asm]
  | [x, y, z], i + 1 => by rw [List.drop_eq_nil_of_le (as := [x, y, z]) (by simp; omega)]; simp [asm]

theorem asm_length : ∀ (P : List UInt8), (asm P).length = P.length / 4 * 4
  | op :: a :: b :: c :: rest => by
    show (asm rest).length + 4 = _; rw [asm_length rest]; simp; omega
  | [] => rfl | [_] => by simp [asm] | [_, _] => by simp [asm] | [_, _, _] => by simp [asm]

theorem drop_len {P : List UInt8} {i : Nat} {op a b c : UInt8} {rest : List UInt8}
    (hd : P.drop (4 * i) = op :: a :: b :: c :: rest) : 4 * i + 4 ≤ P.length := by
  have := congrArg List.length hd; simp at this; omega

theorem pcok_of {C : Ctx} (hC : C.Ok) {i : Nat} {op a b c : UInt8} {rest : List UInt8}
    (hd : C.P.drop (4 * i) = op :: a :: b :: c :: rest) : pcOK (BitVec.ofNat 64 (C.pc0 + 4 * i)) := by
  have := drop_len hd; have := hC.pchi; have := hC.pclo; have := hC.pcal
  have e : (BitVec.ofNat 64 (C.pc0 + 4 * i)).toNat = C.pc0 + 4 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold pcOK; rw [e]; omega

theorem toBitVec_ofBitVec8 (x : BitVec 8) : (UInt8.ofBitVec x).toBitVec = x := rfl

/-- the record's word is in Sail's memory at the record's pc -/
theorem instr_of {C : Ctx} (hC : C.Ok) {s : R.St} {t : Proven.St} (hR : Rel C s t) {op a b c : UInt8}
    {rest : List UInt8} (hd : C.P.drop (4 * s.pc) = op :: a :: b :: c :: rest) {w : BitVec 32}
    (hw : asm [op, a, b, c] = wb w) : instrAt t (BitVec.ofNat 64 (C.pc0 + 4 * s.pc)) w := by
  have hl := drop_len hd; have := hC.pchi; have := hC.pclo; have hp4 := hC.p4
  have hal : (asm C.P).length = C.P.length := by rw [asm_length]; omega
  have hcode : ∀ j, j < 4 → t.mem[C.pc0 + 4 * s.pc + j]? = some ((wb w)[j]?.getD 0).toBitVec := by
    intro j hj
    rw [hR.frame _ (by have := hC.cW; omega) (by have := hC.cO; omega), Nat.add_assoc,
      hC.code _ (by omega)]
    apply congrArg some; apply congrArg UInt8.toBitVec
    have e1 : (asm C.P).drop (4 * s.pc) = wb w ++ asm rest := by
      rw [asm_drop, hd]; show asm [op, a, b, c] ++ asm rest = _; rw [hw]
    have e2 := congrArg (·[j]?) e1; simp only [List.getElem?_drop] at e2
    rw [List.getElem?_append_left (by simp [wb]; omega)] at e2
    have h3 := List.getElem?_eq_getElem (l := asm C.P) (i := 4 * s.pc + j) (by omega)
    rw [e2] at h3; rw [h3]; rfl
  have hpc : (BitVec.ofNat 64 (C.pc0 + 4 * s.pc)).toNat = C.pc0 + 4 * s.pc := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold instrAt; rw [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hcode 0 (by decide); simpa [wb] using this
  · have := hcode 1 (by decide); simpa [wb] using this
  · have := hcode 2 (by decide); simpa [wb] using this
  · have := hcode 3 (by decide); simpa [wb] using this

end Nano.S

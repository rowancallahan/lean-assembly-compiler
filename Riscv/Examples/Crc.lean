/- CRC-32 (ISO-HDLC / zlib: reflected, polynomial `0xEDB88320`, initial value and final xor `0xFFFFFFFF`),
a client of the WORD ARRAYS of the middle layer.

Reference: `crc32`, the readable BITWISE definition (8 shift/xor steps per byte).  Program: `crcP`, TABLE-
DRIVEN: it first builds the 256-entry table of 64-bit words in word block 0 (the first 2048 bytes of the work
block; no constant data block is needed, the table is computed at run time), then one table lookup per byte.
`crcP_exec`: the program computes `crc32` (via `byteStep_tab`, the linearity of the bit step).
`crc32_implements1`: the RV64 code implements `crc32` in `Implements1` form with `space n = 2048 + 15`. -/
import Riscv.Examples.Implements1Ex

set_option linter.unusedVariables false

namespace Proven.Crc
open Proven.Mach Proven.Mach.Riscv
open Proven (ult_ne toNat_inc toNat_ofNat_lt)

/-! ## The reference -/

def poly : BitVec 32 := 0xEDB88320#32

/-- one bit: shift right; if the bit shifted out was 1, xor the polynomial -/
def step (c : BitVec 32) : BitVec 32 := (c >>> 1) ^^^ (if c.getLsbD 0 then poly else 0)

def step8 (c : BitVec 32) : BitVec 32 := step (step (step (step (step (step (step (step c)))))))

/-- one byte: xor it into the low byte, then 8 bit steps -/
def byteStep (c : BitVec 32) (b : UInt8) : BitVec 32 := step8 (c ^^^ b.toBitVec.setWidth 32)

/-- **CRC-32** of a byte list -/
def crc32 (xs : List UInt8) : BitVec 32 := xs.foldl byteStep 0xFFFFFFFF#32 ^^^ 0xFFFFFFFF#32

/-- the result as 4 little-endian bytes -/
def enc32 (c : BitVec 32) : List UInt8 := leN 4 c.toNat

example : crc32 "123456789".toUTF8.toList = 0xCBF43926#32 := by decide +kernel
example : crc32 [] = 0#32 := by decide +kernel

/-! ## Linearity: the table identity -/

theorem step_xor (a b : BitVec 32) : step (a ^^^ b) = step a ^^^ step b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [step, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> simp <;>
    cases a.getLsbD (1 + i) <;> cases b.getLsbD (1 + i) <;> cases poly.getLsbD i <;> decide

theorem step8_xor (a b : BitVec 32) : step8 (a ^^^ b) = step8 a ^^^ step8 b := by
  simp only [step8, step_xor]

theorem step_shr {x : BitVec 32} (h : x.getLsbD 0 = false) : step x = x >>> 1 := by
  simp [step, h]

theorem shr_shr (x : BitVec 32) (m : Nat) : x >>> m >>> 1 = x >>> (m + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]; congr 1; omega

/-- a word whose low 8 bits are 0 goes through 8 steps as a plain shift -/
theorem step8_hi {h : BitVec 32} (hb : ∀ j, j < 8 → h.getLsbD j = false) : step8 h = h >>> 8 := by
  have k : ∀ m, m < 8 → step (h >>> m) = h >>> (m + 1) := fun m hm => by
    rw [step_shr (by rw [BitVec.getLsbD_ushiftRight, Nat.add_zero]; exact hb m hm), shr_shr]
  have k0 : step h = h >>> 1 := by
    have := k 0 (by omega); rwa [show h >>> 0 = h from BitVec.ushiftRight_zero h] at this
  simp only [step8, k0, k 1 (by omega), k 2 (by omega), k 3 (by omega), k 4 (by omega), k 5 (by omega),
    k 6 (by omega), k 7 (by omega)]

/-- the low byte of `y`, as a 32-bit word -/
def lo8 (y : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (y.toNat % 256)

theorem getLsbD_lo8 (y : BitVec 32) (i : Nat) : (lo8 y).getLsbD i = (decide (i < 8) && y.getLsbD i) := by
  simp only [lo8, BitVec.getLsbD_ofNat, BitVec.getLsbD, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  by_cases h : i < 8
  · simp [h, show i < 32 by omega]
  · simp [h]

/-- **The table identity**: one byte of CRC = the table entry of the low byte, xor the shifted register -/
theorem byteStep_tab (c : BitVec 32) (b : UInt8) :
    byteStep c b = step8 (lo8 (c ^^^ b.toBitVec.setWidth 32)) ^^^ (c >>> 8) := by
  unfold byteStep
  generalize hy : c ^^^ b.toBitVec.setWidth 32 = y
  have hsplit : y = lo8 y ^^^ (y ^^^ lo8 y) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_xor]; cases y.getLsbD i <;> cases (lo8 y).getLsbD i <;> rfl
  rw [hsplit, step8_xor]
  congr 1
  · congr 1; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [getLsbD_lo8, BitVec.getLsbD_xor]
    by_cases h : i < 8 <;> simp [h] <;> cases y.getLsbD i <;> rfl
  · rw [step8_hi (fun j hj => by simp [BitVec.getLsbD_xor, getLsbD_lo8, hj])]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, getLsbD_lo8, ← hy, BitVec.getLsbD_setWidth]
    simp [show ¬ (8 + i < 8) by omega]
    intro h; exact absurd (UInt8.toBitVec b |>.getLsbD_ge (8 + i) (by omega)) (by simp_all)

/-! ## 64-bit registers -/

/-- a 32-bit value in a 64-bit register -/
abbrev w64 (c : BitVec 32) : BitVec 64 := c.setWidth 64

theorem toNat_w64 (c : BitVec 32) : (w64 c).toNat = c.toNat := by
  simp only [w64, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := c.isLt; omega)

theorem w64_xor (a b : BitVec 32) : w64 a ^^^ w64 b = w64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_xor, toNat_w64]

theorem w64_shr (a : BitVec 32) (n : Nat) : w64 a >>> n = w64 (a >>> n) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ushiftRight, toNat_w64]

/-- `c := (c >> 1) ^ (if c & 1 ≠ 0 then poly else 0)` -/
def stepE : Mach.BExp :=
  .bin .xor (.bin .lshr (.var 5) (.const 1)) (.ite (.bin .and (.var 5) (.const 1)) (.const (w64 poly)) (.const 0))

theorem and1 (c : BitVec 32) : (w64 c &&& 1#64 = 0) ↔ c.getLsbD 0 = false := by
  constructor
  · intro h; have := congrArg (·.getLsbD 0) h; simpa [w64, BitVec.getLsbD_and, BitVec.getLsbD_setWidth] using this
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    by_cases hi0 : i = 0
    · subst hi0; simp [w64, BitVec.getLsbD_setWidth, h]
    · simp [BitVec.getLsbD_one, hi0]

theorem stepE_denote (env : Mach.BEnv) (c : BitVec 32) (h5 : env 5 = w64 c) : stepE.denote env = w64 (step c) := by
  simp only [stepE, Mach.BExp.denote, Op.eval, h5]
  have e1 : (1#64).toNat % 64 = 1 := rfl
  rw [e1, w64_shr]
  unfold step
  by_cases hb : c.getLsbD 0 = true
  · rw [if_neg (fun e => by rw [(and1 c).1 e] at hb; exact absurd hb (by decide)), if_pos hb, w64_xor]
  · rw [if_pos ((and1 c).2 (by simpa using hb)), if_neg hb, w64_xor]; rfl

/-! ## The program -/

def rep : Nat → Mach.BStmt → Mach.BStmt
  | 0, p => p
  | n + 1, p => .seq p (rep n p)

/-- `while v4 < 256 { v5 := v4; 8 × (v5 := step v5); T[v4] := v5; v4 := v4 + 1 }` -/
def tableLoop : Mach.BStmt :=
  .loop (.bin .ult (.var 4) (.const 256))
    (.seq (.assign 5 (.var 4)) (.seq (rep 7 (.assign 5 stepE))
      (.seq (.store64 0 (.var 4) (.var 5)) (.assign 4 (.bin .add (.var 4) (.const 1))))))

/-- `while v4 < v1 { v6 := in[v4]; v7 := T[(v5 ^ v6) & 255]; v5 := v7 ^ (v5 >> 8); v4 := v4 + 1 }` -/
def mainLoop : Mach.BStmt :=
  .loop (.bin .ult (.var 4) (.var 1))
    (.seq (.load 6 0 (.var 4)) (.seq (.load64 7 0 (.bin .and (.bin .xor (.var 5) (.var 6)) (.const 255)))
      (.seq (.assign 5 (.bin .xor (.var 7) (.bin .lshr (.var 5) (.const 8))))
        (.assign 4 (.bin .add (.var 4) (.const 1))))))

def crcP : Mach.BStmt :=
  .seq (.assign 4 (.const 0)) (.seq tableLoop (.seq (.assign 5 (.const 0xFFFFFFFF)) (.seq (.assign 4 (.const 0))
    (.seq mainLoop (.seq (.assign 4 (.bin .xor (.var 5) (.const 0xFFFFFFFF))) (store8 3))))))

/-- the table, as 64-bit words -/
def tab64 : List (BitVec 64) := (List.range 256).map fun i => w64 (step8 (BitVec.ofNat 32 i))

theorem length_tab64 : tab64.length = 256 := by simp [tab64]

theorem rep_exec (c : BitVec 32) : ∀ (n : Nat) (σ : Mach.BState), σ.env 5 = w64 c →
    ∃ e', Mach.BExec (rep n (.assign 5 stepE)) σ ⟨e', σ.heap, σ.wheap⟩ ∧ e' 5 = w64 (step^[n + 1] c) ∧
      ∀ v, v ≠ 5 → e' v = σ.env v
  | 0, σ, h5 => ⟨_, .assign, by simp [Mach.BEnv.set, stepE_denote _ c h5], fun v hv => by simp [Mach.BEnv.set, hv]⟩
  | n + 1, σ, h5 => by
    obtain ⟨e', he, h5', hk⟩ := rep_exec (step c) n ⟨σ.env.set 5 (stepE.denote σ.env), σ.heap, σ.wheap⟩
      (by simp [Mach.BEnv.set, stepE_denote _ c h5])
    refine ⟨e', .seq .assign he, ?_, fun v hv => by rw [hk v hv]; simp [Mach.BEnv.set, hv]⟩
    rw [h5', Function.iterate_succ_apply]

theorem step8_iter (c : BitVec 32) : step^[8] c = step8 c := rfl

theorem table_set {tbl : List (BitVec 64)} {k : Nat} (hk : k < 256) (hl : tbl.length = 256) :
    (tab64.take k ++ tbl.drop k).set k (w64 (step8 (BitVec.ofNat 32 k))) = tab64.take (k + 1) ++ tbl.drop (k + 1) := by
  have hl' : (tab64.take k).length = k := by simp [length_tab64]; omega
  rw [List.set_append_right _ _ (by rw [hl']; exact Nat.le_refl _), hl', Nat.sub_self,
    List.drop_eq_getElem_cons (by omega), List.set_cons_zero,
    List.take_succ_eq_append_getElem (by rw [length_tab64]; exact hk), List.append_assoc]
  simp [tab64]

theorem tableLoop_exec (σ : Mach.BState) (tbl : List (BitVec 64)) (hw : σ.wheap = [tbl]) (hl : tbl.length = 256)
    (h4 : σ.env 4 = 0) :
    ∃ σ', Mach.BExec tableLoop σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [tab64] ∧ σ'.env 1 = σ.env 1 := by
  obtain ⟨σ₁, hl', hq⟩ := BExec.loop_inv (c := .bin .ult (.var 4) (.const 256))
    (b := .seq (.assign 5 (.var 4)) (.seq (rep 7 (.assign 5 stepE))
      (.seq (.store64 0 (.var 4) (.var 5)) (.assign 4 (.bin .add (.var 4) (.const 1))))))
    (fun τ => τ.heap = σ.heap ∧ τ.wheap = [tab64.take (τ.env 4).toNat ++ tbl.drop (τ.env 4).toNat] ∧
      (τ.env 4).toNat ≤ 256 ∧ τ.env 1 = σ.env 1)
    (fun τ => τ.heap = σ.heap ∧ τ.wheap = [tab64] ∧ τ.env 1 = σ.env 1)
    (fun τ => 256 - (τ.env 4).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨hh, hw', hle, h1⟩ hc => by
      dsimp only at hh hw' hle h1
      simp only [Mach.BExp.denote, ult_ne, show (BitVec.ofNat 64 256).toNat = 256 from rfl] at hc
      set k := (env 4).toNat with hkdef
      have ek : env 4 = w64 (BitVec.ofNat 32 k) := by
        apply BitVec.eq_of_toNat_eq; rw [toNat_w64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨e', hrep, h5', hk⟩ := rep_exec (BitVec.ofNat 32 k) 7 ⟨env.set 5 (env 4), heap, wheap⟩
        (by simp [Mach.BEnv.set, ek])
      rw [step8_iter] at h5'
      have e4 : e' 4 = env 4 := by rw [hk 4 (by decide)]; simp [Mach.BEnv.set]
      have hlen : (tab64.take k ++ tbl.drop k).length = 256 := by simp [length_tab64, hl]; omega
      refine ⟨_, .seq .assign (.seq hrep (.seq (.store64 (by simp [hw']) (by simp [hw', Mach.BExp.denote, e4, hlen]; omega))
        .assign)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [Mach.BEnv.set, Mach.BExp.denote, Op.eval, if_pos, if_true]
      · exact hh
      · have e5 := toNat_inc (show (e' 4).toNat < 256 by rw [e4]; omega) (by omega)
        simp only [e5, e4, hw', List.getElem_cons_zero, List.set_cons_zero, h5']
        rw [← hkdef, table_set (by omega) hl]
      · rw [toNat_inc (show (e' 4).toNat < 256 by rw [e4]; omega) (by omega), e4]; omega
      · rw [hk 1 (by decide)]; simp [Mach.BEnv.set, h1]
      · rw [toNat_inc (show (e' 4).toNat < 256 by rw [e4]; omega) (by omega), e4]; omega)
    (fun ⟨env, heap, wheap⟩ ⟨hh, hw', hle, h1⟩ hc => by
      dsimp only at hh hw' hle h1 ⊢
      have : ¬ (env 4).toNat < 256 := fun hlt => (ult_ne (a := env 4) (b := BitVec.ofNat 64 256)).2 hlt hc
      refine ⟨hh, ?_, h1⟩
      rw [hw', show (env 4).toNat = 256 by omega, List.take_of_length_le (by rw [length_tab64]),
        List.drop_of_length_le (by rw [hl]), List.append_nil])
    σ ⟨rfl, by rw [hw, h4]; simp, by rw [h4]; simp, rfl⟩
  exact ⟨σ₁, hl', hq⟩

theorem getElem_tab64 {k : Nat} (hk : k < 256) : tab64[k]'(by rw [length_tab64]; exact hk) =
    w64 (step8 (BitVec.ofNat 32 k)) := by simp [tab64]

theorem foldl_take_succ (xs : List UInt8) (c : BitVec 32) {j : Nat} (h : j < xs.length) :
    (xs.take (j + 1)).foldl byteStep c = byteStep ((xs.take j).foldl byteStep c) xs[j] := by
  rw [List.take_succ_eq_append_getElem h, List.foldl_append]; rfl

theorem mainLoop_exec (σ : Mach.BState) (xs : List UInt8) (out : List (BitVec 8))
    (hh : σ.heap = [xs.map (·.toBitVec), out]) (hw : σ.wheap = [tab64])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (h4 : σ.env 4 = 0)
    (h5 : σ.env 5 = w64 0xFFFFFFFF#32) :
    ∃ σ', Mach.BExec mainLoop σ σ' ∧ σ'.heap = σ.heap ∧ σ'.env 5 = w64 (xs.foldl byteStep 0xFFFFFFFF#32) := by
  obtain ⟨σ₁, hl', hq⟩ := BExec.loop_inv (c := .bin .ult (.var 4) (.var 1))
    (b := .seq (.load 6 0 (.var 4)) (.seq (.load64 7 0 (.bin .and (.bin .xor (.var 5) (.var 6)) (.const 255)))
      (.seq (.assign 5 (.bin .xor (.var 7) (.bin .lshr (.var 5) (.const 8))))
        (.assign 4 (.bin .add (.var 4) (.const 1))))))
    (fun τ => τ.heap = σ.heap ∧ τ.wheap = [tab64] ∧ τ.env 1 = σ.env 1 ∧ (τ.env 4).toNat ≤ xs.length ∧
      τ.env 5 = w64 ((xs.take (τ.env 4).toNat).foldl byteStep 0xFFFFFFFF#32))
    (fun τ => τ.heap = σ.heap ∧ τ.env 5 = w64 (xs.foldl byteStep 0xFFFFFFFF#32))
    (fun τ => xs.length - (τ.env 4).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨hh', hw', h1', hle, h5'⟩ hc => by
      dsimp only at hh' hw' h1' hle h5'
      simp only [Mach.BExp.denote, ult_ne, h1', h1, toNat_ofNat_lt (show xs.length < 2 ^ 64 by omega)] at hc
      set j := (env 4).toNat with hj
      set c := (xs.take j).foldl byteStep 0xFFFFFFFF#32
      have hb : j < (xs.map (·.toBitVec)).length := by simp; omega
      have e6 : (xs.map (·.toBitVec))[j].setWidth 64 = w64 (xs[j].toBitVec.setWidth 32) := by
        apply BitVec.eq_of_toNat_eq; simp [toNat_w64]
      let env6 := env.set 6 ((xs.map (·.toBitVec))[j].setWidth 64)
      have hidx : ((Mach.BExp.bin .and (.bin .xor (.var 5) (.var 6)) (.const 255)).denote env6).toNat =
          (c ^^^ xs[j].toBitVec.setWidth 32).toNat % 256 := by
        simp only [Mach.BExp.denote, Op.eval, env6, Mach.BEnv.set, show (5 : Nat) ≠ 6 by decide, if_false, if_true,
          h5', e6, w64_xor, BitVec.toNat_and, toNat_w64]
        rw [show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      have hidx' : ((Mach.BExp.bin .and (.bin .xor (.var 5) (.var 6)) (.const 255)).denote env6).toNat < 256 := by
        rw [hidx]; omega
      refine ⟨_, .seq (.load (by rw [hh', hh]; simp) (by rw [hh, hh'] at *; simpa using hb)) (.seq (.load64 (by simp [hw'])
        (by simp only [hw']; simpa [length_tab64] using hidx')) (.seq .assign .assign)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [Mach.BEnv.set, Mach.BExp.denote, Op.eval]
      all_goals simp only [show (4 : Nat) ≠ 5 by decide, show (4 : Nat) ≠ 6 by decide, show (4 : Nat) ≠ 7 by decide,
        show (1 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 5 by decide, show (1 : Nat) ≠ 6 by decide,
        show (1 : Nat) ≠ 7 by decide, show (5 : Nat) ≠ 6 by decide, show (5 : Nat) ≠ 7 by decide,
        show (5 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 7 by decide, if_false, if_true]
      · exact hh'
      · exact hw'
      · exact h1'
      · rw [toNat_inc (show (env 4).toNat < xs.length by omega) (by omega)]; omega
      · sorry
      · rw [toNat_inc (show (env 4).toNat < xs.length by omega) (by omega)]; omega)
    (fun ⟨env, heap, wheap⟩ ⟨hh', hw', h1', hle, h5'⟩ hc => by
      dsimp only at hh' hw' h1' hle h5' ⊢
      have : ¬ (env 4).toNat < xs.length := fun hlt =>
        (ult_ne (a := env 4) (b := env 1)).2 (by rw [h1', h1, toNat_ofNat_lt (by omega)]; exact hlt) hc
      refine ⟨hh', ?_⟩
      rw [h5', List.take_of_length_le (by omega)])
    σ ⟨rfl, hw, rfl, by rw [h4]; simp, by rw [h4, h5]; simp⟩
  exact ⟨σ₁, hl', hq⟩

theorem enc32_bytes (c : BitVec 32) :
    (enc32 c).map (·.toBitVec) = (List.range 4).map fun j => BitVec.ofNat 8 (c.toNat / 256 ^ j) := by
  show (leN 4 c.toNat).map _ = _
  simp only [leN, List.range, List.range.loop, Nat.div_div_eq_div_mul, List.map, u8]
  simp

theorem crcP_exec (σ : Mach.BState) (xs : List UInt8) (out : List (BitVec 8)) (tbl : List (BitVec 64))
    (hh : σ.heap = [xs.map (·.toBitVec), out]) (hw : σ.wheap = [tbl]) (htl : tbl.length = 256)
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (hl : 4 ≤ out.length) :
    ∃ σ' out', Mach.BExec crcP σ σ' ∧ σ'.heap = [xs.map (·.toBitVec), out'] ∧
      out'.take 4 = (enc32 (crc32 xs)).map (·.toBitVec) ∧ out'.drop 4 = out.drop 4 := by
  let σa : Mach.BState := ⟨σ.env.set 4 0, σ.heap, σ.wheap⟩
  obtain ⟨σb, hb, hbh, hbw, hb1⟩ := tableLoop_exec σa tbl hw htl (by simp [σa, Mach.BEnv.set])
  let σc : Mach.BState := ⟨(σb.env.set 5 0xFFFFFFFF).set 4 0, σb.heap, σb.wheap⟩
  obtain ⟨σe, he, heh, he5⟩ := mainLoop_exec σc xs out (by simp [σc, hbh, σa, hh]) (by simp [σc, hbw])
    (by simp [σc, Mach.BEnv.set, hb1, σa, h1]) hn (by simp [σc, Mach.BEnv.set])
    (by simp [σc, Mach.BEnv.set]; rfl)
  have hw4 : (Mach.BExp.bin .xor (.var 5) (.const 0xFFFFFFFF)).denote σe.env = w64 (crc32 xs) := by
    simp only [Mach.BExp.denote, Op.eval, he5, crc32]
    rw [show (0xFFFFFFFF#64 : BitVec 64) = w64 0xFFFFFFFF#32 from rfl, w64_xor]
  obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (w64 (crc32 xs)) 3 (by omega)
    ⟨σe.env.set 4 ((Mach.BExp.bin .xor (.var 5) (.const 0xFFFFFFFF)).denote σe.env), σe.heap, σe.wheap⟩ _ out
    (by simp [heh, σc, hbh, σa, hh]) (by simp [Mach.BEnv.set, hw4]) (by omega) rfl
  refine ⟨_, out', .seq (BExec.assign' rfl) (.seq hb (.seq (BExec.assign' rfl) (.seq (BExec.assign' rfl)
    (.seq he (.seq (BExec.assign' rfl) hst))))), rfl, ?_, ?_⟩
  · apply List.ext_getElem?; intro i
    rw [enc32_bytes]
    by_cases hi : i < 4
    · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi, toNat_w64]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)

/-! ## The machine theorem -/

def crcCode : List (BitVec 32) := rvF.codeF (rvF.compBF 0 [0, 3] [2] crcP)

theorem crc_wf : rvF.wfB 0 [0, 3] [2] crcP := by
  simp [crcP, tableLoop, mainLoop, rep, stepE, store8, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, bzOK_iff,
    jmpOK_iff]
  decide +kernel

/-- **CRC-32 on RV64**, `Implements1` form: input = the raw bytes, output = the 4 little-endian bytes of
`crc32`, work space `2048 + 15` bytes (the table, the frame cell saving `gp`, alignment). -/
theorem crc32_implements1 : Implements1With encRaw enc32 crcCode crc32 (fun _ => 2063) := by
  refine implements1_of_exec encRaw enc32 crc32 0 (by omega) crcP crc_wf (fun _ => 256) (fun _ => 2063)
    (fun n => by dsimp only; omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hl4 : (enc32 (crc32 a)).length = 4 := leN_length 4 _
  simp only [encRaw, hl4] at h1 hlt hout htl ⊢
  obtain ⟨σ', out', hex, hh, ht, hd⟩ := crcP_exec ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ a out tbl rfl rfl htl
    h1 hlt hout
  exact ⟨σ', out', hex, hh, ht, hd, fun h => nomatch h⟩

end Proven.Crc

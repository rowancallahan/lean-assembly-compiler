/- Bare metal: a boot stub run from the model's reset state (`Riscv/Back/BootReset.lean`) establishes
`StartCorrect` (`Spec/Top.lean`), and with `compile_correct` the compiled program's result lands in the
output block (`boot_correct`).  No OS: the only assumptions are on the loaded memory image and sizes.

Layout (RAM from `0x80000000`): stub at `0x80000000` (halt loop, the return address, at `0x80000050`),
compiled code at `0x80001000` (< `0xFF000` bytes), input length (8 bytes LE) at `0x80100000`, input at
`0x80200000` (≤ 2^20 bytes), output block `[0x80300000, +0x100000)`, work block `[0x80400000, +0xC00000)`,
`sp` = its top `0x81000000`.  The stub clears `misa.V`, sets `a0..a3`, `sp`, zeroes output and work (one
loop), then `jal ra` to the code. -/
import Legacy.Riscv.Back.BootV
import Legacy.Riscv.Examples.VacuityBase
import Nano.Base.Riscv.Steps.GenUse
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace Proven.Boot
open Proven.Top Proven.Vacuity

/-! ## The stub -/

/-- the boot stub, at `0x80000000` -/
def stub : List (BitVec 32) :=
  [ luiW,                                    -- 0x00 lui t2, 0x200
    csrW,                                    -- 0x04 csrrc x0, misa, t2   (clear misa.V)
    encI 0 1 5 0,                            -- 0x08 addi t0, x0, 1
    encI 1 (0 <<< 6 ||| 31) 5 5,             -- 0x0c slli t0, t0, 31      (t0 = RAM base)
    G.encU 0x37 6 0x200, encR 0 0 10 5 6,    -- 0x10 a0 = input
    G.encU 0x37 6 0x100, encR 0 0 6 5 6,     -- 0x18 t1 = length address
    G.encL 3 0 11 6,                         -- 0x20 ld a1, 0(t1)
    G.encU 0x37 6 0x300, encR 0 0 13 5 6,    -- 0x24 a3 = output
    G.encU 0x37 6 0x400, encR 0 0 12 5 6,    -- 0x2c a2 = work
    G.encU 0x37 6 0x1000, encR 0 0 2 5 6,    -- 0x34 sp = work top
    encI 0 0 6 13,                           -- 0x3c t1 = a3
    G.encS 3 0 0 6,                          -- 0x40 loop: sd x0, 0(t1)
    encI 0 8 6 6,                            -- 0x44 addi t1, t1, 8
    wB 6 (.ofFin 6) (.ofFin 2) 0xffc,        -- 0x48 bltu t1, sp, loop
    wJ (.ofFin 1) 0x7da,                     -- 0x4c jal ra, 0x80001000
    wJ (.ofFin 0) 0 ]                        -- 0x50 halt: j .

/-- address of stub word `i` -/
def P (i : Nat) : BitVec 64 := BitVec.ofNat 64 (0x80000000 + 4 * i)

def codeBase : Nat := 0x80001000
def lenAddr : Nat := 0x80100000
def inputBase : Nat := 0x80200000
def outBase : Nat := 0x80300000
def workBase : Nat := 0x80400000
def workTop : Nat := 0x81000000

/-- the call the stub makes -/
def bootCall (n : Nat) : Call where
  returnAddress := 0x80000050
  inputAddress := 0x80200000
  inputLength := n
  workAddress := 0x80400000
  workLength := 0xC00000
  outputAddress := 0x80300000
  outputLength := 0x100000

/-- `bytes` at `base` in `m` -/
def Holds (m : Mem) (base : Nat) (bytes : List UInt8) : Prop :=
  (List.range bytes.length).map (m[base + ·]?) = bytes.map (some ·.toBitVec)

/-- the length word: 8 little-endian bytes -/
def encLen (n : Nat) : List UInt8 := (le8 (BitVec.ofNat 64 n)).map UInt8.ofBitVec

/-- **the loaded memory image**: stub, compiled code, input length, input -/
structure Image (m : Mem) (code input : List UInt8) : Prop where
  stub : ∀ i < 4 * stub.length, m[0x80000000 + i]? = (codeBytes8 stub)[i]?
  code : Holds m codeBase code
  length : Holds m lenAddr (encLen input.length)
  input : Holds m inputBase input

/-! ## Helpers -/

theorem P_succ (i : Nat) : P i + 4 = P (i + 1) := by
  simp only [P]; rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1

theorem P_toNat {i : Nat} (hi : i < 2 ^ 32) : (P i).toNat = 0x80000000 + 4 * i := by
  simp only [P, BitVec.toNat_ofNat]; omega

theorem pcOK_P {i : Nat} (hi : i < 21) : pcOK (P i) := by
  simp only [pcOK, P_toNat (by omega : i < 2 ^ 32)]; omega

/-- the stub's words, while memory below the output block is the image -/
theorem instr_of {s : St} {image : Mem} {code input : List UInt8} (himg : Image image code input)
    (hs : ∀ a < outBase, s.mem[a]? = image[a]?) {i : Nat} (hi : i < 21) : instrAt s (P i) stub[i] := by
  have hc : codeAt s (BitVec.ofNat 64 0x80000000) stub :=
    codeAt_of_mem (by simp [codeOK, stub]) fun j hj => by
      rw [hs _ (by simp [stub, outBase] at hj ⊢; omega)]
      exact himg.stub j hj
  have := hc i (by simp [stub]; omega)
  rwa [← BitVec.ofNat_add] at this

theorem runs_trans : ∀ {s t u : riscv.State}, Runs riscv s t → Runs riscv t u → Runs riscv s u
  | _, _, _, .stop, h2 => h2
  | _, _, _, .step hs r, h2 => .step hs (runs_trans r h2)

theorem runs_next {s s' u : St} {pc rd v m} (n : Next s s' pc rd v m) (r : Runs riscv s' u) : Runs riscv s u :=
  .step (step_of_retires n.ret) r


theorem getX_zero (s : St) : getX s 0 = 0 := rfl

theorem getX_next {s s' : St} {pc rd v m} (n : Next s s' pc rd v m) (j : Fin 32) :
    getX s' j = if j = rd ∧ j ≠ 0 then v else getX s j := n.x j

/-- an 8-byte zero store at `A ≥ outBase` keeps memory below `outBase` -/
theorem store_low {m : Mem} {A : Nat} (hA : outBase ≤ A) (a : Nat) (ha : a < outBase) :
    (storeBytes m A (le8 0))[a]? = m[a]? := by
  rw [storeBytes_le8]; simp only [Std.ExtHashMap.getElem?_insert]
  repeat rw [if_neg (by simp; omega)]

theorem store_get (m : Mem) (A a : Nat) :
    (storeBytes m A (le8 0))[a]? = if A ≤ a ∧ a < A + 8 then some 0 else m[a]? := by
  rw [storeBytes_le8]; simp only [Std.ExtHashMap.getElem?_insert]
  by_cases h : A ≤ a ∧ a < A + 8
  · rw [if_pos h]
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ a = A + k := ⟨a - A, by omega, by omega⟩
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all <;> first | rfl | omega
  · rw [if_neg h]; repeat rw [if_neg (by simp; omega)]

theorem ite_merge {α} {x m : Option α} {lo mid hi a : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    (if mid ≤ a ∧ a < hi then x else if lo ≤ a ∧ a < mid then x else m) = if lo ≤ a ∧ a < hi then x else m := by
  by_cases ha : mid ≤ a ∧ a < hi
  · rw [if_pos ha, if_pos (by omega)]
  · rw [if_neg ha]; by_cases hb : lo ≤ a ∧ a < mid
    · rw [if_pos hb, if_pos (by omega)]
    · rw [if_neg hb, if_neg (by omega)]

/-- **the zeroing loop**, `n` iterations left: `[0x81000000 - 8n, 0x81000000)` becomes zero -/
theorem zero_loop {image : Mem} {code input : List UInt8} (himg : Image image code input) :
    ∀ n : Nat, ∀ s : St, Cfg s → s.regs.get? .PC = some (P 16) → (∀ a < outBase, s.mem[a]? = image[a]?) →
    0 < n → 8 * n ≤ 0xD00000 → getX s 6 = BitVec.ofNat 64 (0x81000000 - 8 * n) →
    getX s 2 = BitVec.ofNat 64 0x81000000 →
    ∃ s', Runs riscv s s' ∧ Cfg s' ∧ s'.regs.get? .PC = some (P 19) ∧ (∀ j, j ≠ 6 → getX s' j = getX s j) ∧
      getX s' 6 = BitVec.ofNat 64 0x81000000 ∧
      ∀ a, s'.mem[a]? = if 0x81000000 - 8 * n ≤ a ∧ a < 0x81000000 then some 0 else s.mem[a]?
  | 0, _, _, _, _, h0, _, _, _ => absurd h0 (by omega)
  | k + 1, s, h, hpc, hs, _, hn, h6, h2 => by
    have hA6 : (getX s 6).toNat = 0x81000000 - 8 * (k + 1) := by
      rw [h6, BitVec.toNat_ofNat]; omega
    obtain ⟨s1, n1⟩ := G.step_sd h hpc (pcOK_P (by omega)) 0 6 0 (instr_of himg hs (i := 16) (by omega))
      (A := getX s 6) (by simp) (by rw [hA6]; omega)
      (by rw [hA6]; omega)
    have hs1 : ∀ a < outBase, s1.mem[a]? = image[a]? := fun a ha => by
      rw [n1.mem, getX_zero, store_low (by rw [hA6]; simp only [outBase]; omega) a ha]; exact hs a ha
    obtain ⟨s2, n2⟩ := G.step_addi n1.cfg (by rw [n1.pc, P_succ]) (pcOK_P (by omega)) 6 6 8
      (instr_of himg hs1 (i := 17) (by omega))
    have hs2 : ∀ a < outBase, s2.mem[a]? = image[a]? := fun a ha => by rw [n2.mem]; exact hs1 a ha
    have e26 : getX s2 6 = BitVec.ofNat 64 (0x81000000 - 8 * k) := by
      rw [getX_next n2, if_pos (by decide), getX_next n1, if_neg (by decide), h6]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e22 : getX s2 2 = BitVec.ofNat 64 0x81000000 := by
      rw [getX_next n2, if_neg (by decide), getX_next n1, if_neg (by decide), h2]
    have hm2 : ∀ a, s2.mem[a]? = if 0x81000000 - 8 * (k + 1) ≤ a ∧ a < 0x81000000 - 8 * k then some 0 else s.mem[a]? := by
      intro a; rw [n2.mem, n1.mem, getX_zero, store_get, hA6]
      congr 1; apply propext; omega
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨s3, n3⟩ := G.bltu_n n2.cfg (by rw [n2.pc, P_succ]) (pcOK_P (by omega)) 6 2 0xffc
        (instr_of himg hs2 (i := 18) (by omega)) (by rw [e26, e22]; simp)
      refine ⟨s3, runs_next n1 (runs_next n2 (runs_next n3 .stop)), n3.cfg, by rw [n3.pc, P_succ], ?_, ?_, ?_⟩
      · intro j hj
        rw [getX_next n3, if_neg (by simp), getX_next n2, if_neg (by simp [hj]), getX_next n1, if_neg (by simp)]
      · rw [getX_next n3, if_neg (by simp), e26]
      · intro a; rw [n3.mem, hm2]
    · obtain ⟨s3, n3⟩ := G.bltu_t n2.cfg (by rw [n2.pc, P_succ]) (pcOK_P (by omega)) 6 2 0xffc
        (instr_of himg hs2 (i := 18) (by omega))
        (by rw [e26, e22]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      have hs3 : ∀ a < outBase, s3.mem[a]? = image[a]? := fun a ha => by rw [n3.mem]; exact hs2 a ha
      obtain ⟨s4, r4, c4, p4, x4, e4, m4⟩ := zero_loop himg k s3 n3.cfg (by rw [n3.pc]; decide) hs3 hk
        (by omega) (by rw [getX_next n3, if_neg (by simp), e26])
        (by rw [getX_next n3, if_neg (by simp), e22])
      refine ⟨s4, runs_next n1 (runs_next n2 (runs_next n3 r4)), c4, p4, ?_, e4, ?_⟩
      · intro j hj
        rw [x4 j hj, getX_next n3, if_neg (by simp), getX_next n2, if_neg (by simp [hj]), getX_next n1,
          if_neg (by simp)]
      · intro a; rw [m4, n3.mem, hm2]
        exact ite_merge (by omega) (by omega)


theorem P0 : P 0 = 0x80000000#64 := rfl

theorem len_bytes {m : Mem} {n : Nat} (h : Holds m lenAddr (encLen n)) :
    (List.range 8).map (m[lenAddr + ·]?) = (le8 (BitVec.ofNat 64 n)).map some := by
  have h' := h; simp only [Holds, encLen, List.length_map] at h'
  rw [show (le8 (BitVec.ofNat 64 n)).length = 8 by simp [le8]] at h'
  rw [h', List.map_map]; rfl

/-- **the stub run**: from the start state to the first instruction of the compiled code -/
theorem stub_run {image : Mem} {code input : List UInt8} (himg : Image image code input)
    (hlen : input.length < 2 ^ 64) :
    ∃ s, Runs riscv (bootStart (pure ()) image) s ∧ Cfg s ∧ s.regs.get? .PC = some 0x80001000#64 ∧
      getX s 1 = 0x80000050#64 ∧ getX s 10 = 0x80200000#64 ∧ getX s 11 = BitVec.ofNat 64 input.length ∧
      getX s 12 = 0x80400000#64 ∧ getX s 13 = 0x80300000#64 ∧ getX s 2 = 0x81000000#64 ∧
      ∀ a, s.mem[a]? = if 0x80300000 ≤ a ∧ a < 0x81000000 then some 0 else image[a]? := by
  obtain ⟨h0, hpc0, hm0⟩ := bootStart_ok image
  generalize bootStart (pure ()) image = S0 at h0 hpc0 hm0 ⊢
  have hs0 : ∀ a < outBase, S0.mem[a]? = image[a]? := fun a _ => by rw [hm0]
  obtain ⟨S1, r1, h1, hpc1, h71, hm1⟩ := step_luiV h0 (by rw [hpc0]; rfl) (pcOK_P (i := 0) (by omega))
    (instr_of himg hs0 (i := 0) (by omega))
  have hs1 : ∀ a < outBase, S1.mem[a]? = image[a]? := fun a ha => by rw [hm1]; exact hs0 a ha
  obtain ⟨S2, r2, h2, hpc2, hm2⟩ := step_csrV h1 (by rw [hpc1, P_succ]) (pcOK_P (i := 1) (by omega))
    (instr_of himg hs1 (i := 1) (by omega)) h71
  have hs2 : ∀ a < outBase, S2.mem[a]? = image[a]? := fun a ha => by rw [hm2]; exact hs1 a ha
  obtain ⟨s3, n3⟩ := G.step_addi h2 (by rw [hpc2, P_succ]) (pcOK_P (i := 2) (by omega)) 5 0 1
    (instr_of himg hs2 (i := 2) (by omega))
  have hs3 : ∀ a < outBase, s3.mem[a]? = image[a]? := fun a ha => by rw [n3.mem]; exact hs2 a ha
  obtain ⟨s4, n4⟩ := G.step_slli n3.cfg (by rw [n3.pc, P_succ]) (pcOK_P (i := 3) (by omega)) 5 5 31
    (instr_of himg hs3 (i := 3) (by omega))
  have hs4 : ∀ a < outBase, s4.mem[a]? = image[a]? := fun a ha => by rw [n4.mem]; exact hs3 a ha
  obtain ⟨s5, n5⟩ := G.step_lui n4.cfg (by rw [n4.pc, P_succ]) (pcOK_P (i := 4) (by omega)) 6 0x200
    (instr_of himg hs4 (i := 4) (by omega))
  have hs5 : ∀ a < outBase, s5.mem[a]? = image[a]? := fun a ha => by rw [n5.mem]; exact hs4 a ha
  obtain ⟨s6, n6⟩ := G.step_add n5.cfg (by rw [n5.pc, P_succ]) (pcOK_P (i := 5) (by omega)) 10 5 6 (by decide)
    (instr_of himg hs5 (i := 5) (by omega))
  have hs6 : ∀ a < outBase, s6.mem[a]? = image[a]? := fun a ha => by rw [n6.mem]; exact hs5 a ha
  obtain ⟨s7, n7⟩ := G.step_lui n6.cfg (by rw [n6.pc, P_succ]) (pcOK_P (i := 6) (by omega)) 6 0x100
    (instr_of himg hs6 (i := 6) (by omega))
  have hs7 : ∀ a < outBase, s7.mem[a]? = image[a]? := fun a ha => by rw [n7.mem]; exact hs6 a ha
  obtain ⟨s8, n8⟩ := G.step_add n7.cfg (by rw [n7.pc, P_succ]) (pcOK_P (i := 7) (by omega)) 6 5 6 (by decide)
    (instr_of himg hs7 (i := 7) (by omega))
  have hs8 : ∀ a < outBase, s8.mem[a]? = image[a]? := fun a ha => by rw [n8.mem]; exact hs7 a ha
  have x5 : getX s8 5 = 0x80000000#64 := by
    simp (config := { decide := true }) only [getX_next n8, getX_next n7, getX_next n6, getX_next n5,
      getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have x6 : getX s8 6 = 0x80100000#64 := by
    simp (config := { decide := true }) only [getX_next n8, getX_next n7, getX_next n6, getX_next n5,
      getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have hl := bytesAt_le8 (s := s8) (a := lenAddr) (by rw [bytesAt, ← len_bytes himg.length]; exact List.map_congr_left (fun i hi => hs8 _ (by simp at hi; simp only [lenAddr, outBase]; omega)))
  obtain ⟨s9, n9⟩ := G.step_ld n8.cfg (by rw [n8.pc, P_succ]) (pcOK_P (i := 8) (by omega)) 11 6 0
    (instr_of himg hs8 (i := 8) (by omega)) (A := 0x80100000#64) (by rw [x6]; rfl) (by decide) (by decide)
    hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1 hl.2.2.2.2.2.1 hl.2.2.2.2.2.2.1 hl.2.2.2.2.2.2.2
  rw [le8_cat] at n9
  have hs9 : ∀ a < outBase, s9.mem[a]? = image[a]? := fun a ha => by rw [n9.mem]; exact hs8 a ha
  obtain ⟨s10, n10⟩ := G.step_lui n9.cfg (by rw [n9.pc, P_succ]) (pcOK_P (i := 9) (by omega)) 6 0x300
    (instr_of himg hs9 (i := 9) (by omega))
  have hs10 : ∀ a < outBase, s10.mem[a]? = image[a]? := fun a ha => by rw [n10.mem]; exact hs9 a ha
  obtain ⟨s11, n11⟩ := G.step_add n10.cfg (by rw [n10.pc, P_succ]) (pcOK_P (i := 10) (by omega)) 13 5 6 (by decide)
    (instr_of himg hs10 (i := 10) (by omega))
  have hs11 : ∀ a < outBase, s11.mem[a]? = image[a]? := fun a ha => by rw [n11.mem]; exact hs10 a ha
  obtain ⟨s12, n12⟩ := G.step_lui n11.cfg (by rw [n11.pc, P_succ]) (pcOK_P (i := 11) (by omega)) 6 0x400
    (instr_of himg hs11 (i := 11) (by omega))
  have hs12 : ∀ a < outBase, s12.mem[a]? = image[a]? := fun a ha => by rw [n12.mem]; exact hs11 a ha
  obtain ⟨s13, n13⟩ := G.step_add n12.cfg (by rw [n12.pc, P_succ]) (pcOK_P (i := 12) (by omega)) 12 5 6 (by decide)
    (instr_of himg hs12 (i := 12) (by omega))
  have hs13 : ∀ a < outBase, s13.mem[a]? = image[a]? := fun a ha => by rw [n13.mem]; exact hs12 a ha
  obtain ⟨s14, n14⟩ := G.step_lui n13.cfg (by rw [n13.pc, P_succ]) (pcOK_P (i := 13) (by omega)) 6 0x1000
    (instr_of himg hs13 (i := 13) (by omega))
  have hs14 : ∀ a < outBase, s14.mem[a]? = image[a]? := fun a ha => by rw [n14.mem]; exact hs13 a ha
  obtain ⟨s15, n15⟩ := G.step_add n14.cfg (by rw [n14.pc, P_succ]) (pcOK_P (i := 14) (by omega)) 2 5 6 (by decide)
    (instr_of himg hs14 (i := 14) (by omega))
  have hs15 : ∀ a < outBase, s15.mem[a]? = image[a]? := fun a ha => by rw [n15.mem]; exact hs14 a ha
  obtain ⟨s16, n16⟩ := G.step_addi n15.cfg (by rw [n15.pc, P_succ]) (pcOK_P (i := 15) (by omega)) 6 13 0
    (instr_of himg hs15 (i := 15) (by omega))
  have hs16 : ∀ a < outBase, s16.mem[a]? = image[a]? := fun a ha => by rw [n16.mem]; exact hs15 a ha
  have hm16 : s16.mem = image := by
    rw [n16.mem, n15.mem, n14.mem, n13.mem, n12.mem, n11.mem, n10.mem, n9.mem, n8.mem, n7.mem, n6.mem, n5.mem,
      n4.mem, n3.mem, hm2, hm1, hm0]
  have y2 : getX s16 2 = 0x81000000#64 := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have y6 : getX s16 6 = 0x80300000#64 := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have y10 : getX s16 10 = 0x80200000#64 := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have y11 : getX s16 11 = BitVec.ofNat 64 input.length := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have y12 : getX s16 12 = 0x80400000#64 := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  have y13 : getX s16 13 = 0x80300000#64 := by
    simp (config := { decide := true }) only [getX_next n16, getX_next n15, getX_next n14, getX_next n13,
      getX_next n12, getX_next n11, getX_next n10, getX_next n9, getX_next n8, getX_next n7, getX_next n6,
      getX_next n5, getX_next n4, getX_next n3, getX_zero, if_true, if_false]
  obtain ⟨s17, r17, c17, p17, x17, e17, m17⟩ := zero_loop himg 0x1A0000 s16 n16.cfg (by rw [n16.pc, P_succ])
    hs16 (by decide) (by decide) (by rw [y6]) (by rw [y2])
  have hs17 : ∀ a < outBase, s17.mem[a]? = image[a]? := fun a ha => by
    rw [m17, if_neg (by simp only [outBase] at ha; omega)]; exact hs16 a ha
  obtain ⟨s18, n18⟩ := G.step_jal c17 p17 (pcOK_P (i := 19) (by omega)) 1 0x7da
    (instr_of himg hs17 (i := 19) (by omega))
  have k : ∀ j : Fin 32, j ≠ 1 → j ≠ 6 → getX s18 j = getX s16 j := fun j h1 h6 => by
    rw [getX_next n18, if_neg (by simp [h1]), x17 j h6]
  refine ⟨s18, .step (step_of_retires r1) (.step (step_of_retires r2) (runs_next n3 (runs_next n4 (runs_next n5
    (runs_next n6 (runs_next n7 (runs_next n8 (runs_next n9 (runs_next n10 (runs_next n11 (runs_next n12
    (runs_next n13 (runs_next n14 (runs_next n15 (runs_next n16 (runs_trans r17 (runs_next n18 .stop))))))))))))))))),
    n18.cfg, by rw [n18.pc]; rfl, by rw [getX_next n18, if_pos (by decide)]; rfl,
    by rw [k 10 (by decide) (by decide), y10], by rw [k 11 (by decide) (by decide), y11],
    by rw [k 12 (by decide) (by decide), y12], by rw [k 13 (by decide) (by decide), y13],
    by rw [k 2 (by decide) (by decide), y2], fun a => ?_⟩
  rw [n18.mem, m17, hm16]


theorem obs_reg {s : St} {n : Nat} {v : BitVec 64} (hx : riscvRegister s n = some v) :
    (riscvObserve s).register n = UInt64.ofBitVec v := by
  simp only [riscvObserve, hx]; rfl

theorem holds_read {s : St} {image : Mem} {base : Nat} {bytes : List UInt8} (h : Holds image base bytes)
    (hb : base + bytes.length ≤ 0x80300000)
    (hm : ∀ a, s.mem[a]? = if 0x80300000 ≤ a ∧ a < 0x81000000 then some 0 else image[a]?)
    {addr : UInt64} (ha : addr.toNat = base) : readMemory (riscvObserve s) addr bytes.length = some bytes := by
  rw [readMemory_riscv _ _ (by rw [ha]; omega), bytesAt, ha, ← h]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [hm, if_neg (by omega)]

/-- **the stub establishes `StartCorrect`** from the bare-metal start, for code and input that fit -/
theorem boot_start {image : Mem} {code input : List UInt8} (himg : Image image code input)
    (hcode : code.length ≤ 0xFF000) (hin : input.length ≤ 2 ^ 20) :
    ∃ s, Runs riscv (bootStart (pure ()) image) s ∧ StartCorrect riscv s (bootCall input.length) code input := by
  obtain ⟨s, hr, h, hpc, x1, x10, x11, x12, x13, x2, hm⟩ := stub_run himg (by omega)
  have epc : (riscvObserve s).programCounter = 0x80001000 := by simp only [riscvObserve, hpc]; rfl
  refine ⟨s, hr, ⟨h, ?_, ?_, rfl, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by show (0x80000050 : UInt64).toNat % 4 = 0; decide, by show (0x80400000 : UInt64).toNat % 8 = 0; decide, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show readMemory (riscvObserve s) (riscvObserve s).programCounter code.length = some code
    rw [epc]; exact holds_read himg.code (by simp only [codeBase]; omega) hm rfl
  · show readMemory (riscvObserve s) 0x80200000 input.length = some input
    exact holds_read himg.input (by simp only [inputBase]; omega) hm rfl
  · show (riscvObserve s).register 1 = 0x80000050
    rw [obs_reg (n := 1) h.x1, x1]; rfl
  · show (riscvObserve s).register 10 = 0x80200000
    rw [obs_reg (n := 10) h.x10, x10]; rfl
  · show (riscvObserve s).register 11 = input.length.toUInt64
    rw [obs_reg (n := 11) h.x11, x11]; rfl
  · show (riscvObserve s).register 12 = 0x80400000
    rw [obs_reg (n := 12) h.x12, x12]; rfl
  · show (riscvObserve s).register 2 = 0x80400000 + (0xC00000 : Nat).toUInt64
    rw [obs_reg (n := 2) h.x2, x2]; rfl
  · show (riscvObserve s).register 13 = 0x80300000
    rw [obs_reg (n := 13) h.x13, x13]; rfl
  · show (riscvObserve s).programCounter.toNat % 4 = 0
    rw [epc]; decide
  · show Apart (0x80000050, 4) ((riscvObserve s).programCounter, code.length)
    rw [epc]; exact Or.inl (by decide : (0x80000050 : UInt64).toNat + 4 ≤ (0x80001000 : UInt64).toNat)
  · show ∀ block ∈ (bootCall input.length).blocks (riscvObserve s).programCounter code.length,
      0x80000000 ≤ block.1.toNat ∧ block.1.toNat + block.2 ≤ 0x100000000
    rw [epc]
    simp only [Call.blocks, bootCall, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      UInt64.reduceToNat]
    omega
  · show ((bootCall input.length).blocks (riscvObserve s).programCounter code.length).Pairwise Apart
    rw [epc]
    simp only [Call.blocks, bootCall, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, Apart, UInt64.reduceToNat, false_implies,
      implies_true]
    omega
  · intro offset ho; replace ho : offset < 0x100000 := ho
    show ((riscvObserve s).memory (0x80300000 + offset.toUInt64)).isSome
    simp only [riscvObserve, Option.isSome_map]
    rw [toNat_add_offset (bound := 0x100000) (by decide) ho, hm, if_pos (by simp only [UInt64.reduceToNat]; omega)]
    rfl
  · intro offset ho; replace ho : offset < 0xC00000 := ho
    show ((riscvObserve s).memory (0x80400000 + offset.toUInt64)).isSome
    simp only [riscvObserve, Option.isSome_map]
    rw [toNat_add_offset (bound := 0xC00000) (by decide) ho, hm, if_pos (by simp only [UInt64.reduceToNat]; omega)]
    rfl


/-- the compiler's work space bound always fits the work block -/
theorem space_fits {program : XPipe} {compiled : Top.Compiled} (compiles : Top.compile program = some compiled)
    {n : Nat} (hn : n ≤ 2 ^ 20) : compiled.space n ≤ 0xC00000 := by
  obtain ⟨code, hcode, rfl⟩ := compile_inv compiles
  have := (compileX1_inv hcode).2.2.1
  show 2 * (n + XPipe.extra program) + 79 ≤ 0xC00000
  omega

/-- **bare metal, end to end**, for a reservation hook `cancel` that leaves the state alone: from the
bare-metal start, the machine runs to the stub's halt address with `encodeOutput (f argument)` in the
output block -/
theorem boot_correct_with {cancel : SailM Unit} (hcancel : ∀ s : St, cancel s = .ok () s)
    {program : XPipe} {compiled : Top.Compiled} {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} {argument : α} {image : Mem}
    (compiles : Top.compile program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (loaded : Image image compiled.code (encodeInput argument))
    (codeFits : compiled.code.length ≤ 0xFF000)
    (inputFits : (encodeInput argument).length ≤ 2 ^ 20)
    (outputFits : (encodeOutput (f argument)).length ≤ 0x100000) :
    ∃ finishState, Runs riscv (bootStart cancel image) finishState ∧
      (riscv.observe finishState).programCounter = 0x80000050 ∧
      readMemory (riscv.observe finishState) 0x80300000 (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) := by
  have : cancel = (pure () : SailM Unit) := funext hcancel
  subst this
  obtain ⟨s, hr, hs⟩ := boot_start loaded codeFits inputFits
  obtain ⟨t, ht, hpc, hout⟩ := compile_correct compiles computes hs outputFits (space_fits compiles inputFits)
  exact ⟨t, runs_trans hr ht, hpc, hout⟩

/-- **`boot_correct`**: from the model's own reset (`reset_eq`: `bootStart (cancel_reservation ())` runs
`sail_model_init`, the board config and `reset`), assuming only that the declared axiom
`cancel_reservation` leaves the Sail state alone -/
theorem boot_correct (hcancel : ∀ s : St, cancel_reservation () s = .ok () s)
    {program : XPipe} {compiled : Top.Compiled} {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} {argument : α} {image : Mem}
    (compiles : Top.compile program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (loaded : Image image compiled.code (encodeInput argument))
    (codeFits : compiled.code.length ≤ 0xFF000)
    (inputFits : (encodeInput argument).length ≤ 2 ^ 20)
    (outputFits : (encodeOutput (f argument)).length ≤ 0x100000) :
    ∃ finishState, Runs riscv (bootStart (cancel_reservation ()) image) finishState ∧
      (riscv.observe finishState).programCounter = 0x80000050 ∧
      readMemory (riscv.observe finishState) 0x80300000 (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) :=
  boot_correct_with hcancel compiles computes loaded codeFits inputFits outputFits


/-- the same for any `Implements1With` code (`implements1_top`), loaded as `wordBytes code` -/
theorem boot_implements1_with {cancel : SailM Unit} (hcancel : ∀ s : St, cancel s = .ok () s)
    {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {code : List (BitVec 32)} {f : α → β}
    {space : Nat → Nat} {retLen : Bool} (implements : Implements1With encA encB code f space (retLen := retLen))
    {argument : α} {image : Mem}
    (loaded : Image image (wordBytes code) (encA argument))
    (codeFits : (wordBytes code).length ≤ 0xFF000)
    (inputFits : (encA argument).length ≤ 2 ^ 20)
    (outputFits : (encB (f argument)).length ≤ 0x100000)
    (spaceFits : space (encA argument).length ≤ 0xC00000) :
    ∃ finishState, Runs riscv (bootStart cancel image) finishState ∧
      (riscv.observe finishState).programCounter = 0x80000050 ∧
      readMemory (riscv.observe finishState) 0x80300000 (encB (f argument)).length
        = some (encB (f argument)) := by
  have : cancel = (pure () : SailM Unit) := funext hcancel
  subst this
  obtain ⟨s, hr, hs⟩ := boot_start loaded codeFits inputFits
  obtain ⟨t, ht, hpc, hout, -⟩ := implements1_top implements hs outputFits spaceFits
  exact ⟨t, runs_trans hr ht, hpc, hout⟩

end Proven.Boot

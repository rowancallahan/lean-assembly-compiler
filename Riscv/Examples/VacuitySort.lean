/- Non-vacuity, part 3: the hypotheses of `sortCode_implements` (`ImplementsMapped`) and `msortCode_implements`
(`ImplementsMapped2`, stack frame 71) are jointly satisfiable on one explicit state, with input `[3, 1, 2]`, and
the theorems then say the output block holds `[1, 2, 3]`.

Layout (all in RAM, pairwise disjoint): code at `pc0 = 0x80000000` (any code of at most 1000 words), `park`
(`jal x0, 0`) at `ra0 = 0x80001000`, input at `0x80002000`, scratch at `0x80003000` (3 bytes), output at
`0x80004000` (3 bytes), stack `[0x80005000, 0x80005100)`. -/
import Riscv.Examples.MutationBase
import Riscv.Direct.SortMergeMachine
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Proven.Vacuity

def x3 : List UInt8 := [3, 1, 2]
def inR : Region := ⟨0x80002000, 3⟩
def scR : Region := ⟨0x80003000, 3⟩
def outR : Region := ⟨0x80004000, 3⟩
def stR : Region := ⟨0x80005000, 0x100⟩

/-- memory: `code` at `pc0`, `park` at `ra0`, the input bytes, zeroed scratch and output -/
def memS (code : List (BitVec 32)) : Mem :=
  loadBytes (loadBytes (loadBytes (loadBytes (loadBytes ∅ ra0.toNat (codeBytes8 [park])) inR.base (x3.map (·.toBitVec)))
    scR.base [0, 0, 0]) outR.base [0, 0, 0]) pc0.toNat (codeBytes8 code)

/-- **the witness state** for the sorts: `a0 = input`, `a1 = 3`, `a2 = scratch`, `a3 = output`,
`sp = stack top`, `ra = ra0`, `PC = pc0` -/
def sS (code : List (BitVec 32)) : St :=
  witness pc0 ra0 (BitVec.ofNat 64 (stR.base + stR.len)) (BitVec.ofNat 64 inR.base) (BitVec.ofNat 64 3)
    (BitVec.ofNat 64 scR.base) (BitVec.ofNat 64 outR.base) (memS code)

theorem pc0_toNat : pc0.toNat = 0x80000000 := rfl
theorem ra0_toNat : ra0.toNat = 0x80001000 := rfl

theorem memS_code_other {code : List (BitVec 32)} (hlen : code.length ≤ 1000) {k : Nat} (hk : 0x80001000 ≤ k) :
    (memS code)[k]? = (loadBytes (loadBytes (loadBytes (loadBytes ∅ ra0.toNat (codeBytes8 [park]))
      inR.base (x3.map (·.toBitVec))) scR.base [0, 0, 0]) outR.base [0, 0, 0])[k]? := by
  rw [memS, load_get_other]; rw [codeBytes8_length, pc0_toNat]; omega

theorem sS_input {code : List (BitVec 32)} (hlen : code.length ≤ 1000) :
    bytesAt (sS code) inR.base x3.length = x3.map (some ·.toBitVec) := by
  rw [bytesAt_eq]; show memAt (memS code) _ _ = _
  rw [memS, memAt_load_other _ _ _ _ _ (by rw [codeBytes8_length, pc0_toNat]; simp [inR, x3]; omega),
    memAt_load_other _ _ _ _ _ (by simp [inR, outR, x3]), memAt_load_other _ _ _ _ _ (by simp [inR, scR, x3]),
    show x3.length = (x3.map (·.toBitVec)).length by simp, memAt_load_self]
  simp

theorem sS_out_mapped {code : List (BitVec 32)} (hlen : code.length ≤ 1000) :
    ∀ i < 3, ((sS code).mem[outR.base + i]?).isSome := by
  intro i hi
  show ((memS code)[_]?).isSome
  rw [memS_code_other hlen (by simp [outR]; omega), load_get_in _ _ _ _ (by simpa using hi)]; rfl

theorem sS_scr_mapped {code : List (BitVec 32)} (hlen : code.length ≤ 1000) :
    ∀ i < 3, ((sS code).mem[scR.base + i]?).isSome := by
  intro i hi
  show ((memS code)[_]?).isSome
  rw [memS_code_other hlen (by simp [scR]; omega), load_get_other _ _ _ _ (by simp [scR, outR]; omega),
    load_get_in _ _ _ _ (by simpa using hi)]; rfl

theorem sS_park {code : List (BitVec 32)} (hlen : code.length ≤ 1000) : instrAt (sS code) ra0 park := by
  have hp : instrAt { sS code with mem := loadBytes ∅ ra0.toNat (codeBytes8 [park]) } ra0 park :=
    codeAt_one (codeAt_load ∅ [park] (by refine ⟨by decide, by decide, by decide⟩) rfl)
  refine instrAt_of_mem (fun i hi => ?_) hp
  show (memS code)[_]? = _
  rw [ra0_toNat] at *
  rw [memS_code_other hlen (by omega), load_get_other _ _ _ _ (by simp [outR]; omega),
    load_get_other _ _ _ _ (by simp [scR]; omega), load_get_other _ _ _ _ (by simp [inR]; omega)]
  rfl

theorem sS_code {code : List (BitVec 32)} (hlen : code.length ≤ 1000) :
    bytesAt (sS code) pc0.toNat (4 * code.length) = codeBytes code := by
  rw [bytesAt_eq, codeBytes_eq, ← codeBytes8_length]; exact memAt_load_self ..

theorem sS_cfg (code) : Cfg (sS code) := witness_cfg ..

/-- the `inRAM` and disjointness side conditions of the layout -/
theorem layout_ok {n : Nat} (hlen : n ≤ 1000) :
    (∀ r ∈ [inR, scR, outR, stR, (⟨pc0.toNat, 4 * n⟩ : Region)], r.inRAM) ∧
    [inR, scR, outR, stR, (⟨pc0.toNat, 4 * n⟩ : Region)].Pairwise disjoint ∧
    disjoint ⟨ra0.toNat, 4⟩ ⟨pc0.toNat, 4 * n⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.pairwise_cons,
    List.Pairwise.nil, and_true, Region.inRAM, disjoint, inR, scR, outR, stR, pc0_toNat, ra0_toNat]
  refine ⟨by omega, ⟨by omega, by omega, by omega, ⟨by omega, fun _ h => h.elim⟩⟩, by omega⟩

/-- **`ImplementsMapped` applied at the witness** (for any code of at most 1000 words and any `f` with
`|f [3,1,2]| = 3`): every hypothesis is discharged. -/
theorem IM_apply {code : List (BitVec 32)} {f : List UInt8 → List UInt8} (hlen : code.length ≤ 1000)
    (hf : (f x3).length = 3) (H : ImplementsMapped code f) :
    runsTo (sS code) fun s' => s'.regs.get? .PC = some ra0 ∧
      bytesAt s' outR.base 3 = (f x3).map (some ·.toBitVec) ∧
      unchangedOutside (sS code) s' [inR, scR, outR, stR] ∧ calleeSavedKept (sS code) s' ∧ Cfg s' := by
  obtain ⟨hram, hdis, hrad⟩ := layout_ok hlen
  have := H x3 (sS code) pc0 ra0 inR scR outR stR (by decide) (sS_cfg code) (witness_pc ..) (by decide)
    (sS_code hlen) (witness_x10 ..) (witness_x11 ..) (witness_x12 ..) (witness_x13 ..) (witness_x2 ..)
    (witness_x1 ..) (by decide) hrad (sS_input hlen) rfl (by decide) (by rw [hf]; decide) (by decide) hram hdis
    (by rw [hf]; exact sS_out_mapped hlen)
  rw [hf] at this; exact this

/-- **`ImplementsMapped2` applied at the witness**, stack frame 71. -/
theorem IM2_apply {code : List (BitVec 32)} {f : List UInt8 → List UInt8} (hlen : code.length ≤ 1000)
    (hf : (f x3).length = 3) (H : ImplementsMapped2 code f (stackLen := 71)) :
    runsTo (sS code) fun s' => s'.regs.get? .PC = some ra0 ∧
      bytesAt s' outR.base 3 = (f x3).map (some ·.toBitVec) ∧
      unchangedOutside (sS code) s' [inR, scR, outR, stR] ∧ calleeSavedKept (sS code) s' ∧ Cfg s' := by
  obtain ⟨hram, hdis, hrad⟩ := layout_ok hlen
  have := H x3 (sS code) pc0 ra0 inR scR outR stR (by decide) (sS_cfg code) (witness_pc ..) (by decide)
    (sS_code hlen) (witness_x10 ..) (witness_x11 ..) (witness_x12 ..) (witness_x13 ..) (witness_x2 ..)
    (witness_x1 ..) (by decide) hrad (sS_input hlen) rfl (by decide) (by rw [hf]; decide) (by decide) hram hdis
    (by rw [hf]; exact sS_out_mapped hlen) (sS_scr_mapped hlen)
  rw [hf] at this; exact this

theorem mergeSort_x3 : x3.mergeSort leU = [1, 2, 3] := by simp [x3, List.mergeSort, leU]

theorem sortCode_len : sortCode.length ≤ 1000 := by decide +kernel
theorem msortCode_len : msortCode.length ≤ 1000 := by decide +kernel

/-- **`sortCode_implements` is not vacuous**: on the explicit state `sS sortCode` (input `[3,1,2]`) all its
hypotheses hold, and it yields a run that returns to `ra0` with the output block `[1, 2, 3]`. -/
theorem sortCode_concrete : runsTo (sS sortCode) fun s' => s'.regs.get? .PC = some ra0 ∧
    bytesAt s' outR.base 3 = [some 1#8, some 2#8, some 3#8] := by
  refine runsTo_mono (IM_apply sortCode_len (by rw [mergeSort_x3]; rfl) sortCode_implements) ?_
  rintro s' ⟨p1, p2, -⟩; exact ⟨p1, by rw [p2, mergeSort_x3]; rfl⟩

/-- **`msortCode_implements` is not vacuous** (same state shape, stack frame 71 ≤ 256). -/
theorem msortCode_concrete : runsTo (sS msortCode) fun s' => s'.regs.get? .PC = some ra0 ∧
    bytesAt s' outR.base 3 = [some 1#8, some 2#8, some 3#8] := by
  refine runsTo_mono (IM2_apply msortCode_len (by rw [mergeSort_x3]; rfl) msortCode_implements) ?_
  rintro s' ⟨p1, p2, -⟩; exact ⟨p1, by rw [p2, mergeSort_x3]; rfl⟩

end Proven.Vacuity

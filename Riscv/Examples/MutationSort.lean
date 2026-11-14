/- Mutation testing of the sort specification: `ImplementsMapped code (fun x => x.mergeSort leU)` REJECTS
four one-word mutants of `sortCode`.

Method (`kill_sort`): each mutant is the image `compileAF [0, 3] p'` of a mutated source program `p'`, differing
from `sortCode` in exactly one instruction word (`*_diff`, by `decide +kernel`).  On the witness state `sS` of
`VacuitySort.lean` (input `[3, 1, 2]`, a `jal x0, 0` parked at the return address):
* if the mutant satisfied the spec, `IM_apply` gives a run ending with output `[1, 2, 3]`;
* `compileAF_ok` for `p'` (with an `AExec` derivation from the fuel interpreter `AStmt.run`, evaluated by
  `decide +kernel`) gives a run ending with output = block 1 of the source result;
* `runsTo_unique` (determinism of `Retires` + parking) says both final states have the same memory.
The source result differs from `[1, 2, 3]`, contradiction. -/
import Riscv.Examples.VacuitySort
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Proven.Vacuity

/-- the source variables of the witness (`a0..a7`) -/
def env0 : AEnv := fun i =>
  if i = 0 then BitVec.ofNat 64 inR.base else if i = 1 then BitVec.ofNat 64 3 else
  if i = 2 then BitVec.ofNat 64 scR.base else if i = 3 then BitVec.ofNat 64 outR.base else 0

/-- the source state of the witness: block 0 = input `[3,1,2]`, block 1 = output (zeroed) -/
def σ0 : AState := ⟨env0, [x3.map (·.toBitVec), [0, 0, 0]]⟩

theorem sS_ra (code : List (BitVec 32)) : getX (sS code) 1 = ra0 := by rw [sS, witness_getX]; rfl

theorem sS_output {code : List (BitVec 32)} (hlen : code.length ≤ 1000) :
    bytesAt (sS code) outR.base 3 = [some 0, some 0, some 0] := by
  rw [bytesAt_eq]; show memAt (memS code) _ _ = _
  rw [memS, memAt_load_other _ _ _ _ _ (by rw [codeBytes8_length, pc0_toNat]; simp [outR]; omega),
    show (3 : Nat) = ([0, 0, 0] : List (BitVec 8)).length from rfl, memAt_load_self]; rfl

theorem rel0 {code : List (BitVec 32)} (hlen : code.length ≤ 1000) : Rel [0, 3] [inR, outR] σ0 (sS code) where
  env := by intro i; rw [sS, witness_getX]; revert i; decide
  hlen := rfl
  bvlen := rfl
  base := by decide
  blen := by decide
  bytes := by
    intro b hb
    rcases b with _ | _ | b
    · show bytesAt (sS code) inR.base x3.length = _
      rw [sS_input hlen]; rfl
    · exact sS_output hlen
    · simp at hb; omega

theorem park_of_unchanged {code : List (BitVec 32)} (hlen : code.length ≤ 1000) {t : St} {rs : List Region}
    (hrs : ∀ r ∈ rs, ra0.toNat + 4 ≤ r.base) (hu : unchangedOutside (sS code) t rs) : instrAt t ra0 park :=
  instrAt_of_mem (fun i hi => hu _ fun r hr => Or.inl (by have := hrs r hr; omega)) (sS_park hlen)

/-- **The kill lemma**: a source-image mutant whose source result on `[3,1,2]` is not `[1,2,3]` does not
satisfy the sort specification. -/
theorem kill_sort {p : AStmt} (hwf : p.wf [0, 3]) (hlen : (compileAF [0, 3] p).length ≤ 1000) {H : Heap}
    (hrun : (AStmt.run 100000 p σ0).map AState.heap = some H)
    (hne : (H[1]?.getD []).map some ≠ [some 1#8, some 2#8, some 3#8]) :
    ¬ ImplementsMapped (compileAF [0, 3] p) (fun x => x.mergeSort leU) := by
  intro HI
  obtain ⟨σ', hex, hH⟩ := AStmt.exec_of_run hrun
  have r1 := IM_apply hlen (by rw [mergeSort_x3]; rfl) HI
  have hR : RegOK [inR, outR] := by
    refine ⟨?_, ?_⟩ <;> simp [Region.inRAM, disjoint, inR, outR]
  have hcd : ∀ r ∈ [inR, outR], disjoint ⟨pc0.toNat, 4 * (compileAF [0, 3] p).length⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, disjoint, inR, outR,
      pc0_toNat]; omega
  have r2 := compileAF_ok [0, 3] hwf hR hex (sS_cfg _) (witness_pc ..) (codeAt_load _ _ (codeOK_pc0 hlen) rfl)
    (codeOK_pc0 hlen) hcd (rel0 hlen) (by rw [sS_ra]; decide)
  have hb : ∀ r ∈ [inR, scR, outR, stR], ra0.toNat + 4 ≤ r.base := by
    simp [inR, scR, outR, stR, ra0_toNat]
  obtain ⟨t₁, t₂, p₁, p₂, hm, -⟩ := runsTo_unique pcOK_ra0 r1 r2
    (fun t ⟨q1, _, q3, _, q5⟩ => ⟨q5, q1, park_of_unchanged hlen hb q3⟩)
    (fun t ⟨q1, _, q3, q4, _⟩ => ⟨q4, by rw [q1, sS_ra], park_of_unchanged hlen (fun r hr => hb r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) q3⟩)
  have b1 := p₁.2.1
  have b2 := p₂.2.1.bytes 1 (by decide)
  rw [hH] at b2
  apply hne; rw [← b2]
  show bytesAt t₂ outR.base 3 = _
  rw [bytesAt_eq, ← hm, ← bytesAt_eq, b1, mergeSort_x3]; rfl

/-- the indices where two code lists differ -/
def wordDiff (a b : List (BitVec 32)) : List Nat :=
  (List.range (max a.length b.length)).filter fun i => a[i]? != b[i]?

/-! ## Mutated source pieces -/

def mkSort (map ins : AStmt) : AStmt := .seq (.assign 2 (.var 1)) (.seq map ins)
def insWith (outer : AStmt) : AStmt := .seq (.assign 2 (.const 0)) (.loop (.bin .ult (.var 2) (.var 1)) outer)
def outerWith (inner : AStmt) (inc : AExp) : AStmt :=
  .seq (.load 5 1 (.var 2)) (.seq (.assign 4 (.var 2)) (.seq (.assign 7 (.const 1))
    (.seq (.loop (.var 7) inner) (.assign 2 inc))))
def innerWith (c v : AExp) : AStmt :=
  .seq (.load 6 1 idxE) (.seq (.assign 7 c) (.seq (.store 1 (.var 4) v) (.assign 4 (.bin .sub (.var 4) (.var 7)))))
def incA : AExp := .bin .add (.var 2) (.const 1)
/-- `mapProg (var 6)` with the copy-loop increment `a5 + 1` replaced by `a5 - 1` -/
def mapSub : AStmt :=
  .seq (.assign 4 (.ite (.bin .ult (.var 2) (.var 1)) (.var 2) (.var 1)))
  (.seq (.assign 5 (.const 0))
   (.loop (.bin .ult (.var 5) (.var 4))
     (.seq (.load 6 0 (.var 5)) (.seq (.store 1 (.var 5) (.var 6)) (.assign 5 (.bin .sub (.var 5) (.const 1)))))))

theorem mkSort_eq : mkSort (mapProg (.var 6)) (insWith (outerWith (innerWith cE valE) incA)) = sortProg := rfl

/-- M1: outer increment `add t0, t0, t1` → `sub t0, t0, t1` (`i := i - 1`): output `[3, 1, 2]` -/
def mut1 : AStmt := mkSort (mapProg (.var 6)) (insWith (outerWith (innerWith cE valE) (.bin .sub (.var 2) (.const 1))))
/-- M2: stored value `a7 ? a6 : a5` → `a7 ? a6 : a6` (one register field): output `[3, 3, 3]` -/
def mut2 : AStmt := mkSort (mapProg (.var 6)) (insWith (outerWith (innerWith cE (.ite (.var 7) (.var 6) (.var 6))) incA))
/-- M3: copy-loop increment `add` → `sub`: output `[0, 0, 3]` -/
def mut3 : AStmt := mkSort mapSub insProg
/-- M4: shift test `a5 <u a6` → `a5 <u a5` (one register field): never shifts, output `[3, 1, 2]` -/
def mut4 : AStmt := mkSort (mapProg (.var 6))
  (insWith (outerWith (innerWith (.bin .and (.bin .ult (.const 0) (.var 4)) (.bin .ult (.var 5) (.var 5))) valE) incA))

theorem mut1_diff : wordDiff (compileAF [0, 3] mut1) sortCode = [100] ∧
    (compileAF [0, 3] mut1).length = sortCode.length := by decide +kernel
theorem mut2_diff : wordDiff (compileAF [0, 3] mut2) sortCode = [84] ∧
    (compileAF [0, 3] mut2).length = sortCode.length := by decide +kernel
theorem mut3_diff : wordDiff (compileAF [0, 3] mut3) sortCode = [33] ∧
    (compileAF [0, 3] mut3).length = sortCode.length := by decide +kernel
theorem mut4_diff : wordDiff (compileAF [0, 3] mut4) sortCode = [75] ∧
    (compileAF [0, 3] mut4).length = sortCode.length := by decide +kernel

theorem mut1_wf : mut1.wf [0, 3] := by
  simp [mut1, mkSort, insWith, outerWith, innerWith, mapProg, idxE, cE, valE, AStmt.wf, AExp.depth, compileA, gen8,
    addrE, opCode, selCode, genConst]
theorem mut2_wf : mut2.wf [0, 3] := by
  simp [mut2, mkSort, insWith, outerWith, innerWith, incA, mapProg, idxE, cE, AStmt.wf, AExp.depth, compileA, gen8,
    addrE, opCode, selCode, genConst]
theorem mut3_wf : mut3.wf [0, 3] := by
  simp [mut3, mkSort, mapSub, insProg, outerBody, innerBody, idxE, cE, valE, AStmt.wf, AExp.depth, compileA, gen8,
    addrE, opCode, selCode, genConst]
theorem mut4_wf : mut4.wf [0, 3] := by
  simp [mut4, mkSort, insWith, outerWith, innerWith, incA, mapProg, idxE, valE, AStmt.wf, AExp.depth, compileA, gen8,
    addrE, opCode, selCode, genConst]

/-- **Mutant M1 is rejected** by the sort specification. -/
theorem mut1_killed : ¬ ImplementsMapped (compileAF [0, 3] mut1) (fun x => x.mergeSort leU) :=
  kill_sort mut1_wf (by decide +kernel) (H := [[3, 1, 2], [3, 1, 2]]) (by decide +kernel) (by decide)
/-- **Mutant M2 is rejected.** -/
theorem mut2_killed : ¬ ImplementsMapped (compileAF [0, 3] mut2) (fun x => x.mergeSort leU) :=
  kill_sort mut2_wf (by decide +kernel) (H := [[3, 1, 2], [3, 3, 3]]) (by decide +kernel) (by decide)
/-- **Mutant M3 is rejected.** -/
theorem mut3_killed : ¬ ImplementsMapped (compileAF [0, 3] mut3) (fun x => x.mergeSort leU) :=
  kill_sort mut3_wf (by decide +kernel) (H := [[3, 1, 2], [0, 0, 3]]) (by decide +kernel) (by decide)
/-- **Mutant M4 is rejected.** -/
theorem mut4_killed : ¬ ImplementsMapped (compileAF [0, 3] mut4) (fun x => x.mergeSort leU) :=
  kill_sort mut4_wf (by decide +kernel) (H := [[3, 1, 2], [3, 1, 2]]) (by decide +kernel) (by decide)

/-- the four killed mutants, each one word away from `sortCode` -/
theorem sort_mutants_killed :
    (¬ ImplementsMapped (compileAF [0, 3] mut1) (fun x => x.mergeSort leU)) ∧
    (¬ ImplementsMapped (compileAF [0, 3] mut2) (fun x => x.mergeSort leU)) ∧
    (¬ ImplementsMapped (compileAF [0, 3] mut3) (fun x => x.mergeSort leU)) ∧
    (¬ ImplementsMapped (compileAF [0, 3] mut4) (fun x => x.mergeSort leU)) :=
  ⟨mut1_killed, mut2_killed, mut3_killed, mut4_killed⟩

end Proven.Vacuity

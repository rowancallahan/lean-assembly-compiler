/- Paged arrays (NOTES section 30), part 16: lean-zip code (VERBATIM, `Riscv/Frontx/WaLeanZip.lean`) on the paged back
end: `Zip.Native.countLengthsFast` (Inflate.lean:536; `Array.replicate (maxBits + 1) 0`, `set!` in a loop; ARR rows
`countLengthsFast` and `countLengthsFast.go`), through the word-array front end's `wa_compile` and the bridge
`Pg.goodE_of_good` (`WpBridge.lean`). -/
import Riscv.Frontx.WpBridge
import Riscv.Frontx.WpMem
import Riscv.Frontx.WaMul

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven.WA.LeanZip
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv

theorem countLengthsE_plain : countLengthsE.wa.PlainP [inLocP] 9 := by
  simp [countLengthsE.wa, Pg.PlainP, Inis.PlainP, F.PlainP, T.PushFree, Args.PushFree, A.PushFree, Mem.locP,
    inLocP, E.natVal]
  exact ⟨by decide, by decide⟩

theorem countLengthsE_N : pgNA countLengthsE.wa ≤ NS := by decide +kernel
theorem countLengthsE_ob : (countLengthsE.wa.compP [inLocP] 9).2.v < outBaseP countLengthsE.wa ∧
    (countLengthsE.wa.compP [inLocP] 9).2.pt < outBaseP countLengthsE.wa := by decide +kernel
theorem countLengthsE_wfP : countLengthsE.wa.wfP [inLocP] 9 = true := by decide +kernel
theorem countLengthsE_wfB : rvF.wfB (pgNA countLengthsE.wa) [0, 3] [2] (pgProgA countLengthsE.wa) := by
  decide +kernel
theorem countLengthsE_pk : pk 0 (countLengthsE.wa.evsC [inLocP] 9) = 2 := by decide +kernel

theorem countLengths7E_plain : countLengths7E.wa.PlainP [inLocP] 9 := by
  simp [countLengths7E.wa, Pg.PlainP, Inis.PlainP, F.PlainP, T.PushFree, Args.PushFree, A.PushFree, Mem.locP,
    inLocP, E.natVal]
  exact ⟨by decide, by decide⟩
theorem countLengths7E_N : pgNA countLengths7E.wa ≤ NS := by decide +kernel
theorem countLengths7E_ob : (countLengths7E.wa.compP [inLocP] 9).2.v < outBaseP countLengths7E.wa ∧
    (countLengths7E.wa.compP [inLocP] 9).2.pt < outBaseP countLengths7E.wa := by decide +kernel
theorem countLengths7E_wfP : countLengths7E.wa.wfP [inLocP] 9 = true := by decide +kernel
theorem countLengths7E_wfB : rvF.wfB (pgNA countLengths7E.wa) [0, 3] [2] (pgProgA countLengths7E.wa) := by
  decide +kernel
theorem countLengths7E_pk : pk 0 (countLengths7E.wa.evsC [inLocP] 9) = 2 := by decide +kernel

/-- the pages `countLengthsFast` needs: a page table, one page of counters, one for the frame -/
def clFits (_ : ByteArray) (L : Nat) : Prop := 3 ≤ L / 8192

/-- **`countLengthsFast xs.data 15` (lean-zip, verbatim) on the paged back end ⇒ `Implements1Pg`** -/
theorem countLengthsE_implements : Implements1Pg (fun xs : ByteArray => xs.data.toList) (encArr (.arr .nat))
    (pgCodeA countLengthsE.wa) countLengthsE 8192 clFits (2 ^ 20) (retLen := true) :=
  implements1_pgA (k := .arr .nat) countLengthsE countLengthsE.wa countLengthsE_N countLengthsE_ob
    countLengthsE_wfP countLengthsE_wfB clFits (2 ^ 20) fun xs hx =>
    ⟨_, Pg.goodE_of_good _ _ _ _ _ countLengthsE_plain (countLengthsE.good xs (by omega)),
      fun L _ => by rw [countLengthsE_pk]; unfold clFits; omega⟩

/-- **`countLengthsFast xs.data 7` on the paged back end ⇒ `Implements1Pg`** -/
theorem countLengths7E_implements : Implements1Pg (fun xs : ByteArray => xs.data.toList) (encArr (.arr .nat))
    (pgCodeA countLengths7E.wa) countLengths7E 8192 clFits (2 ^ 20) (retLen := true) :=
  implements1_pgA (k := .arr .nat) countLengths7E countLengths7E.wa countLengths7E_N countLengths7E_ob
    countLengths7E_wfP countLengths7E_wfB clFits (2 ^ 20) fun xs hx =>
    ⟨_, Pg.goodE_of_good _ _ _ _ _ countLengths7E_plain (countLengths7E.good xs (by omega)),
      fun L _ => by rw [countLengths7E_pk]; unfold clFits; omega⟩

/-- the events of the run (newest first, the frame page first) and the memory in the `AllocSpec` form -/
def clEvents (_ : List UInt8) : List MemEvent := (countLengthsE.wa.evsC [inLocP] 9).reverse ++ [.alloc 1]
def cl7Events (_ : List UInt8) : List MemEvent := (countLengths7E.wa.evsC [inLocP] 9).reverse ++ [.alloc 1]

def isAlloc : MemEvent → Bool | .alloc _ => true | .free _ => false

theorem allocs_of_all {E : List MemEvent} (h : E.all isAlloc = true) : ∀ e ∈ E, ∃ n, e = .alloc n := by
  intro e he
  have := List.all_eq_true.1 h e he
  cases e with
  | alloc n => exact ⟨n, rfl⟩
  | free n => exact absurd this (by simp [isAlloc])

theorem countLengthsE_memoryNeeded (code : List (BitVec 32)) (input : List UInt8) :
    memoryNeeded (pgCompiled code clEvents) input = 8192 * 3 := by
  show 8192 * peak ((countLengthsE.wa.evsC [inLocP] 9).reverse ++ [.alloc 1]) = _
  rw [peak_pages _ (allocs_of_all (by decide +kernel)), countLengthsE_pk]

theorem countLengths7E_memoryNeeded (code : List (BitVec 32)) (input : List UInt8) :
    memoryNeeded (pgCompiled code cl7Events) input = 8192 * 3 := by
  show 8192 * peak ((countLengths7E.wa.evsC [inLocP] 9).reverse ++ [.alloc 1]) = _
  rw [peak_pages _ (allocs_of_all (by decide +kernel)), countLengths7E_pk]

end Proven.WA.LeanZip

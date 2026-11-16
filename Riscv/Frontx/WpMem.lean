/- Paged arrays (NOTES section 30), part 14: `memoryNeeded` in pages.

A paged program's abstract run has the page events `E` (oldest first, allocations only) from the empty pool; the work
block also holds the frame (one page of `8 P = 8192` bytes).  In the `AllocSpec` form (`Compiler/AllocSpec.lean`: events
newest first, cells = pages, cell size `8 P`): `events = E.reverse ++ [.alloc 1]` (the frame comes first), so
`memoryNeeded = 8192 * peak = 8192 * (pk 0 E + 1)`; the code returns the result exactly when the work block has this
many whole pages (`fits_iff_memoryNeeded`). -/
import Riscv.Frontx.WpEx2
import Spec.Top
import Riscv.Back.Top

namespace Proven.WA
open Proven Proven.WP Proven.Top Proven.Top.Alloc Proven.Mach.Riscv

theorem finE_shift : ∀ (E : List MemEvent) (u : Nat), (∀ e ∈ E, ∃ n, e = .alloc n) → finE (u + 1) E = finE u E + 1
  | [], u, _ => rfl
  | e :: es, u, h => by
    obtain ⟨n, rfl⟩ := h e (by simp)
    simp only [finE, stepE]
    rw [show u + 1 + n = (u + n) + 1 by omega]
    exact finE_shift es (u + n) (fun e he => h e (by simp [he]))

/-- the peak of the paged run, frame included -/
theorem peak_pages (E : List MemEvent) (hE : ∀ e ∈ E, ∃ n, e = .alloc n) :
    peak (E.reverse ++ [.alloc 1]) = pk 0 E + 1 := by
  rw [peak_eq, (PgEx.pk_allocs E 1 hE).1, (PgEx.pk_allocs E 0 hE).1, finE_shift E 0 hE]

/-- **fits ⟺ `memoryNeeded ≤ work length`**: `pk 0 E + 1 ≤ L / 8192` ⟺ `8192 * peak ≤ L` -/
theorem fits_iff_memoryNeeded (E : List MemEvent) (hE : ∀ e ∈ E, ∃ n, e = .alloc n) (L : Nat) :
    pk 0 E + 1 ≤ L / 8192 ↔ 8192 * peak (E.reverse ++ [.alloc 1]) ≤ L := by
  rw [peak_pages E hE]; omega

/-- a compiled paged program in the `AllocSpec` form: cells are pages of `8 P = 8192` bytes -/
def pgCompiled (code : List (BitVec 32)) (events : List UInt8 → List MemEvent) : CompiledA :=
  ⟨wordBytes code, 8192, events⟩

theorem pgCompiled_memoryNeeded (code : List (BitVec 32)) (events : List UInt8 → List MemEvent) (input : List UInt8) :
    memoryNeeded (pgCompiled code events) input = 8192 * peak (events input) := rfl

namespace PgEx

theorem copyEv_allocs (xs : ByteArray) : ∀ e ∈ copyEv xs, ∃ n, e = .alloc n := by
  intro e he
  simp only [copyEv, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | he
  · exact ⟨1, rfl⟩
  · exact pushFrom_allocs _ _ e he

theorem lzEv_allocs (xs : ByteArray) : ∀ e ∈ lzEv xs, ∃ n, e = .alloc n := by
  intro e he
  simp only [lzEv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, pushEvs] at he
  rcases he with (rfl | he) | he
  · exact ⟨1, rfl⟩
  · exact pushFrom_allocs 0 _ e he
  · exact pushFrom_allocs _ _ e he

/-- `copyE` in the `AllocSpec` form (the events of the run on the input's bytes) -/
def copyCompiled : CompiledA :=
  pgCompiled (pgCodeA copyPg) fun input => (copyEv ⟨input.toArray⟩).reverse ++ [.alloc 1]

def lzCompiled : CompiledA :=
  pgCompiled (pgCodeA lzPg) fun input => (lzEv ⟨input.toArray⟩).reverse ++ [.alloc 1]

/-- the memory `copyE` needs: a page table, `⌈n / P⌉` pages, a page for the frame -/
theorem copy_memoryNeeded (xs : ByteArray) (h : xs.size ≤ P * P) :
    memoryNeeded copyCompiled xs.data.toList = 8192 * (2 + npages xs.size) := by
  show 8192 * peak ((copyEv ⟨xs.data.toList.toArray⟩).reverse ++ [.alloc 1]) = _
  rw [show (ByteArray.mk xs.data.toList.toArray) = xs by simp, peak_pages _ (copyEv_allocs xs), (copyPg_good xs h).2]
  omega

theorem copy_fits_iff_memoryNeeded (xs : ByteArray) (h : xs.size ≤ P * P) (L : Nat) :
    copyFits xs L ↔ memoryNeeded copyCompiled xs.data.toList ≤ L := by
  rw [copy_memoryNeeded xs h]; unfold copyFits; omega

theorem lz_memoryNeeded (xs : ByteArray) (h : xs.size ≤ P * P - 16) :
    memoryNeeded lzCompiled xs.data.toList = 8192 * (2 + npages (min 16 xs.size + xs.size)) := by
  show 8192 * peak ((lzEv ⟨xs.data.toList.toArray⟩).reverse ++ [.alloc 1]) = _
  rw [show (ByteArray.mk xs.data.toList.toArray) = xs by simp, peak_pages _ (lzEv_allocs xs), (lzPg_good xs h).2]
  omega

theorem lz_fits_iff_memoryNeeded (xs : ByteArray) (h : xs.size ≤ P * P - 16) (L : Nat) :
    lzFits xs L ↔ memoryNeeded lzCompiled xs.data.toList ≤ L := by
  rw [lz_memoryNeeded xs h]; unfold lzFits; omega

end PgEx
end Proven.WA

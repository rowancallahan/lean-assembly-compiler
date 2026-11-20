/- Paged dynamic arrays (NOTES section 30), part 4: page events and peaks.

The abstract run of a program reports its page events (`MemEvent` of `Compiler/AllocSpec.lean`, cells = pages),
oldest first here: `pk u E` is the most pages in use while the events `E` happen from `u` pages in use,
`finE u E` the pages in use afterwards.  `peak_eq` connects them to `AllocSpec.peak` (newest first). -/
import Legacy.Riscv.Frontx.WpExp

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc

def stepE : Nat → MemEvent → Nat
  | u, .alloc n => u + n
  | u, .free n => u - n

/-- pages in use after the events (oldest first) -/
def finE : Nat → List MemEvent → Nat
  | u, [] => u
  | u, e :: es => finE (stepE u e) es

/-- the most pages in use while the events happen -/
def pk : Nat → List MemEvent → Nat
  | u, [] => u
  | u, e :: es => max u (pk (stepE u e) es)

theorem finE_append (u : Nat) : ∀ (E F : List MemEvent), finE u (E ++ F) = finE (finE u E) F
  | [], _ => rfl
  | e :: es, F => finE_append (stepE u e) es F

theorem pk_append : ∀ (u : Nat) (E F : List MemEvent), pk u (E ++ F) = max (pk u E) (pk (finE u E) F)
  | u, [], F => by
    simp only [List.nil_append, pk, finE]
    cases F with
    | nil => simp [pk]
    | cons f fs => simp only [pk]; omega
  | u, e :: es, F => by
    simp only [List.cons_append, pk, finE]
    rw [pk_append (stepE u e) es F]; omega

theorem le_pk : ∀ (u : Nat) (E : List MemEvent), u ≤ pk u E
  | _, [] => Nat.le_refl _
  | _, _ :: _ => Nat.le_max_left _ _

theorem finE_le_pk : ∀ (u : Nat) (E : List MemEvent), finE u E ≤ pk u E
  | _, [] => Nat.le_refl _
  | u, e :: es => Nat.le_trans (finE_le_pk (stepE u e) es) (Nat.le_max_right _ _)

theorem pk_mono_left (u : Nat) (E F : List MemEvent) : pk u E ≤ pk u (E ++ F) := by
  rw [pk_append]; exact Nat.le_max_left _ _

theorem pk_alloc1 (u : Nat) (E : List MemEvent) : pk u (E ++ [.alloc 1]) = max (pk u E) (finE u E + 1) := by
  rw [pk_append]; simp [pk, stepE]

theorem peak_eq_rev (u : Nat) : ∀ (R : List MemEvent), peak (R ++ [.alloc u]) = pk u R.reverse ∧
    inUse (R ++ [.alloc u]) = finE u R.reverse
  | [] => by simp [peak, inUse, pk, finE]
  | e :: rest => by
    obtain ⟨h1, h2⟩ := peak_eq_rev u rest
    have hin : inUse (e :: (rest ++ [.alloc u])) = finE u (rest.reverse ++ [e]) := by
      rw [finE_append]; cases e <;> simp [inUse, finE, stepE, h2]
    rw [List.cons_append, List.reverse_cons]
    refine ⟨?_, hin⟩
    show max (inUse (e :: (rest ++ [.alloc u]))) (peak (rest ++ [.alloc u])) = _
    have hf := finE_le_pk u rest.reverse
    rw [hin, h1, pk_append, finE_append]
    cases e <;> simp [pk, stepE, finE] <;> omega

/-- the AllocSpec peak (events newest first) of the events after a start with `u` cells -/
theorem peak_eq (E : List MemEvent) (u : Nat) : peak (E.reverse ++ [.alloc u]) = pk u E := by
  have := (peak_eq_rev u E.reverse).1; rwa [List.reverse_reverse] at this

end Proven.WA

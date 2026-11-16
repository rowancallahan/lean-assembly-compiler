/- Facts about IR runs: events are only added (newest first), the output never shrinks; peaks of event lists. -/
import Compiler.Ir.Sem

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem setOut_length (out : List (Option UInt8)) (i : Nat) (v : UInt8) :
    out.length ≤ (setOut out i v).length := by
  unfold setOut; split <;> simp

section
variable {ρ : Type} [DecidableEq ρ]

theorem exec_out {m : Mem} {g : ρ → Val} {i : Inst ρ} {g' : ρ → Val} {m' : Mem} {e : List MemEvent}
    (h : i.exec m g = some (g', m', e)) : m.out.length ≤ m'.out.length := by
  cases i with
  | let_ d r => simp only [Inst.exec] at h; split at h <;> simp_all
  | ldb d p x => simp only [Inst.exec] at h; (repeat' split at h) <;> simp_all
  | stb v p x =>
    simp only [Inst.exec] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact setOut_length _ _ _
    · exact nomatch h
  | ld d p k => simp only [Inst.exec] at h; (repeat' split at h) <;> simp_all
  | st v p k =>
    simp only [Inst.exec] at h; (repeat' split at h) <;> simp_all
    all_goals (obtain ⟨-, rfl, -⟩ := h; exact Nat.le_refl _)
  | alloc d n =>
    simp only [Inst.exec] at h; split at h <;> simp_all
    obtain ⟨-, rfl, -⟩ := h; exact Nat.le_refl _
  | free p =>
    simp only [Inst.exec] at h; (repeat' split at h) <;> simp_all
    obtain ⟨-, rfl, -⟩ := h; exact Nat.le_refl _
  | call ds f as => exact nomatch h

theorem termStep_next {F : Func ρ} {fr : Frame ρ} {rest : List (Frame ρ)} {m : Mem} {ev : List MemEvent}
    {t : Term ρ} {s' : State ρ} (h : termStep F fr rest m ev t = .next s') :
    s'.mem = m ∧ ∃ E, s'.ev = E ++ ev := by
  cases t <;> simp only [termStep] at h <;> (repeat' split at h) <;> (try cases h)
  all_goals first | exact ⟨rfl, [], rfl⟩ | exact ⟨rfl, [_], rfl⟩

/-- a step only adds events and never shrinks the output -/
theorem step_mono {P : Prog ρ} {s s' : State ρ} (h : step P s = .next s') :
    (∃ E, s'.ev = E ++ s.ev) ∧ s.mem.out.length ≤ s'.mem.out.length := by
  unfold step at h
  (repeat' split at h) <;> (try cases h)
  all_goals first
    | exact ⟨⟨[_], rfl⟩, Nat.le_refl _⟩
    | (next e => exact ⟨⟨_, rfl⟩, exec_out e⟩)
    | (obtain ⟨hm, hE⟩ := termStep_next h; exact ⟨hE, by rw [hm]; exact Nat.le_refl _⟩)

theorem run_mono_ev {P : Prog ρ} : ∀ {n : Nat} {s : State ρ} {r : Result}, run P n s = some r →
    ∃ E, r.ev = E ++ s.ev
  | 0, _, _, h => nomatch h
  | n + 1, s, r, h => by
    rw [run_succ] at h
    split at h
    · next s' e =>
      obtain ⟨⟨E₁, h₁⟩, -⟩ := step_mono e
      obtain ⟨E₂, h₂⟩ := run_mono_ev h
      exact ⟨E₂ ++ E₁, by rw [h₂, h₁, List.append_assoc]⟩
    · next r' e =>
      cases h
      unfold step at e
      (repeat' split at e) <;> (try cases e)
      all_goals unfold termStep at e
      all_goals (repeat' split at e) <;> (try cases e)
      all_goals exact ⟨[], by simp⟩
    · exact nomatch h

theorem run_mono_out {P : Prog ρ} : ∀ {n : Nat} {s : State ρ} {r : Result}, run P n s = some r →
    s.mem.out.length ≤ r.mem.out.length
  | 0, _, _, h => nomatch h
  | n + 1, s, r, h => by
    rw [run_succ] at h
    split at h
    · next s' e => exact Nat.le_trans (step_mono e).2 (run_mono_out h)
    · next r' e =>
      cases h
      unfold step at e
      (repeat' split at e) <;> (try cases e)
      all_goals unfold termStep at e
      all_goals (repeat' split at e) <;> (try cases e)
      all_goals exact Nat.le_refl _
    · exact nomatch h

end

/-! ## Peaks -/

theorem peak_append_ge : ∀ (E L : List MemEvent), peak L ≤ peak (E ++ L)
  | [], _ => Nat.le_refl _
  | e :: E, L => by
    show peak L ≤ max (inUse (e :: (E ++ L))) (peak (E ++ L))
    exact Nat.le_trans (peak_append_ge E L) (Nat.le_max_right _ _)

theorem inUse_le_peak' : ∀ (L : List MemEvent), inUse L ≤ peak L
  | [] => Nat.le_refl _
  | _ :: _ => Nat.le_max_left _ _

/-- only allocations -/
def Allocs (L : List MemEvent) : Prop := ∀ e ∈ L, ∃ n, e = .alloc n

theorem inUse_append_alloc : ∀ (E : List MemEvent) (a : Nat), Allocs E → inUse (E ++ [.alloc a]) = inUse E + a
  | [], a, _ => by simp [inUse]
  | .alloc n :: E, a, h => by
    show inUse (E ++ [.alloc a]) + n = inUse E + n + a
    rw [inUse_append_alloc E a fun e he => h e (List.mem_cons_of_mem _ he)]; omega
  | .free n :: E, a, h => by obtain ⟨_, e⟩ := h _ (List.mem_cons_self ..); exact nomatch e

theorem peak_allocs : ∀ (E : List MemEvent), Allocs E → peak E = inUse E
  | [], _ => rfl
  | .alloc n :: E, h => by
    show max (inUse E + n) (peak E) = inUse E + n
    rw [peak_allocs E fun e he => h e (List.mem_cons_of_mem _ he)]; omega
  | .free n :: E, h => by obtain ⟨_, e⟩ := h _ (List.mem_cons_self ..); exact nomatch e

theorem Allocs.append {E L : List MemEvent} (h₁ : Allocs E) (h₂ : Allocs L) : Allocs (E ++ L) :=
  fun e he => (List.mem_append.1 he).elim (h₁ e) (h₂ e)

end Proven.Ir

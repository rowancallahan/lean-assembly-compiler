/- Machine bridge (Opus box E): multi-word value semantics.  `SemW` = a fragment's semantics (environment, stack
pointer, heap ↦ result words and heap); combinators `one`/`hd1`, `nilS`, `pairS`, `ifS`, `letS` (+ `setW`), the IF head
`ifHeadG`/`cmpJ` with `step_cmp`, and `hrel_sp`.  The fragment contract and its run theorems are the safe ones:
`EVHwS` (EVSDefs.lean), `nilXS`/`pairXS`/`ifXS`/`letXS` (EVSComp.lean). -/
import Nano.V2Self.Proof.Machine.HeapEV
namespace Templates
open CallProbe

abbrev Env := Nat → UInt64
abbrev SemW := Env → Nat → Hp → Option (List UInt64 × Hp)

/-- one word as a list -/
def one (S : Env → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (S env sp H).map fun r => ([r.1], r.2)

/-- the head word of a result (for one-word operands) -/
def hd1 (S : SemW) : Env → Nat → Hp → Option (UInt64 × Hp) :=
  fun env sp H => (S env sp H).bind fun r => match r.1 with | [v] => some (v, r.2) | _ => none

/-! ## the empty fragment and sequencing -/

def nilS : SemW := fun _ _ H => some ([], H)

def pairS (wa : Nat) (SA SB : SemW) : SemW :=
  fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8 * wa) r1.2).bind fun r2 => some (r1.1 ++ r2.1, r2.2)

theorem hrel_sp {hb : Nat} {s : St} {H : Hp} (h : HRel hb s H) : 16 ≤ (s.x 31).toNat := by
  obtain ⟨a, b, c, _⟩ := h; omega

/-! ## IF with multi-word arms -/

/-- the compare instruction of the IF head (Gen: cmp 1 = `beq`, otherwise `bltu`) -/
def cmpJ (cmp : Nat) : J := if cmp = 1 then .beq 5 6 2 else .bltu 5 6 2
def cmpF (cmp : Nat) (a b : UInt64) : Prop := if cmp = 1 then a = b else a.toNat < b.toNat
instance (cmp : Nat) (a b : UInt64) : Decidable (cmpF cmp a b) := by unfold cmpF; split <;> infer_instance

def ifHeadG (cmp lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, cmpJ cmp, .jal 0 ((lt : Int) + 2)]

def ifS (cmp : Nat) (SP ST SE : SemW) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => if cmpF cmp a b then ST env sp r.2 else SE env sp r.2
    | _ => none

theorem step_cmp {C : List J} {q cmp : Nat} {s : St} (hc : C[q]? = some (cmpJ cmp)) :
    step C (q, s) = some (if cmpF cmp (s.x 5) (s.x 6) then q + 2 else q + 1, s) := by
  by_cases h : cmp = 1
  · simp only [cmpJ, h, if_true] at hc; simp only [cmpF, h, if_true, step, hc]
    by_cases e : s.x 5 = s.x 6 <;> simp [e]; omega
  · simp only [cmpJ, h, if_false] at hc; simp only [cmpF, h, if_false, step, hc]
    by_cases e : (s.x 5).toNat < (s.x 6).toNat <;> simp [e]; omega

/-! ## LET of width w -/

/-- slots k0 … k0+w−1 get the words of `vs` -/
def setW (env : Env) (k0 w : Nat) (vs : List UInt64) : Env :=
  fun k => if k0 ≤ k ∧ k < k0 + w then vs.getD (k - k0) 0 else env k

def letS (k0 w : Nat) (SV SB : SemW) : SemW :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2

end Templates

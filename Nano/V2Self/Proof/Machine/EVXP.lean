/- Machine bridge (Opus box E): leaves and prim closings as `EVHw` fragments.
`leafX` (one checked push: CONST, LOCAL 1, LEN/ISIZE), `localX` (LOCAL of width w = w single pushes),
`fin1X` / `fin2X` / `fin3X` (an operand block of 1/2/3 words, then a closing fragment `Fin1/2/3`: BIN, RD, BSIZE,
BGET, BPUSH/PUT, BSET), `bnewX` (BNEW). -/
import Nano.V2Self.Proof.Machine.EVXC
import Nano.V2Self.Proof.Machine.ExprEV
namespace Templates
open CallProbe

/-- one checked push of `V env` (exact room condition: t5 + 8 ≤ t6) -/
def leafS (V : Env → UInt64) : SemW := fun env sp H => if H.top + 8 ≤ sp then some ([V env], H) else none

/-- LOCAL k w: w single pushes -/
def localS (k : Nat) : Nat → SemW
  | 0 => nilS
  | w + 1 => pairS 1 (leafS (fun env => env k)) (localS (k + 1) w)

theorem localT_succ (tgt p k q w : Nat) : localT tgt p k q (w + 1) = localT tgt p k q 1 ++ localT tgt p (k + 1) (q + 5) w := by
  simp [localT]

/-! ## operand block + closing fragment -/

def fin1S (SP : SemW) (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a] => (F a (sp - 8) r.2).map fun x => ([x.1], x.2)
    | _ => none
def fin2S (SP : SemW) (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => (F a b (sp - 16) r.2).map fun x => ([x.1], x.2)
    | _ => none
def fin3S (SP : SemW) (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b, c] => (F a b c (sp - 24) r.2).map fun x => ([x.1], x.2)
    | _ => none

end Templates

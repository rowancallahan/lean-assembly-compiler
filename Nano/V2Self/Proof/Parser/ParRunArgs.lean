/- Nano/V2Self/Proof/Parser/ParRunArgs: Layer 2 → ParSpec for ARGUMENT LISTS (box G).
`AtomSpec cx st st'`: an atom segment pushed one node `v` and is `ParSpec.pAtom` (non-tail) at all large fuels, with node `v.toNd`.
`atomSeg_spec`: every run of `[argAtom]` is an `AtomSpec`, given the same for parenthesised atoms (`ParenH`: the open-recursion
hypothesis that the expression induction supplies).  `args_spec`: `Atoms k` = `ParSpec.pArgs` for every parameter list the
argument types match. -/
import Nano.V2Self.Proof.Parser.ParRunAtom
namespace ParRun
open ParSpec

theorem StarN.nil_inv {n : Nat} {st : St} {c : List Frame × St} (h : StarN n ([], st) c) : n = 0 ∧ c = ([], st) := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => simp [stepS] at hs

theorem pArgs_nil (f : Nat) (cx : Cx) (ts : List Tok) (nx : Nat) : pArgs (f + 1) cx [] ts nx = some ([], ts, nx) := by
  rw [pArgs]

theorem pArgs_cons (f : Nat) (cx : Cx) (p : Ps) (ps : List Ps) (ts : List Tok) (nx : Nat) :
    pArgs (f + 1) cx (p :: ps) ts nx = (pAtom f cx false ts nx).bind fun (a, ta, r1, nx1) =>
      if tyMatch p ta then (pArgs f cx ps r1 nx1).map fun (as, r2, nx2) => ((a, ta) :: as, r2, nx2) else none := by
  rw [pArgs]

/-- parameter kinds matched by the argument types, position by position -/
inductive ArgsMatch : List Ps → List (RN × Ty) → Prop
  | nil : ArgsMatch [] []
  | cons {p ps v vs} : tyMatch p v.2 = true → ArgsMatch ps vs → ArgsMatch (p :: ps) (v :: vs)

end ParRun

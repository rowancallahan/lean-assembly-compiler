/- Nano/V2Self/Proof/Tests/OwnNV: non-vacuity of `o41_sound`.  `pOk`: `def f (b : Buf) := let c := bpush b 7; c` (the param is
consumed once) — accepted, kernel-checked, hence linear.  `pAlias` (= alias_d's shape: `b` read after `bpush b 7`
consumed it) is rejected. -/
import Nano.V2Self.Proof.Own.OwnStage
namespace OwnP
open C OwnSpec ParSpec

def pOk : List DefA := [⟨0, 1, 2, 0, 1, .letE 1 1 (.prim 9 [.loc 0 1, .const 7]) (.loc 1 1)⟩]
def pAlias : List DefA := [⟨0, 1, 2, 0, 1, .letE 1 1 (.prim 9 [.loc 0 1, .const 7]) (.loc 0 1)⟩]

theorem pOk_acc : o41 (serialize pOk) ≠ [] := by decide +kernel

theorem pOk_linear : ∃ Ks, progOk [] [] Ks pOk = true ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2 :=
  o41_sound pOk (by
    intro d hd; simp [pOk] at hd; subst hd
    refine ⟨by decide, by decide, by decide, ?_⟩
    simp only [WFB, WFN, WFL, primAr, dsP]; decide) (by decide) pOk_acc

#guard o41 (serialize pAlias) == []

end OwnP

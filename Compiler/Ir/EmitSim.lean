/- The whole run: from the relation, a terminating Lin run's machine run ends in `Fin`. -/
import Compiler.Ir.EmitStepOk

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- **the run** -/
theorem sim {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) : ∀ (n : Nat) {st : State Nat} {s : T.S}
    {r : Result}, C.Rel Q L qs st s → run Q n st = some r → r.mem.out.length ≤ C.outL → T.runsTo s (C.Fin Q r)
  | 0, _, _, _, _, h, _ => nomatch h
  | n + 1, st, s, r, hrel, h, hO => by
    rw [run_succ] at h
    split at h
    · next st' e =>
      have hO' := Nat.le_trans (run_mono_out h) hO
      refine T.toCore.runsTo_trans (C.step_ok hK hrel e hO') fun s' h' => ?_
      rcases h' with hrel' | ⟨hlt, hE⟩
      · exact sim hK n hrel' h hO
      · obtain ⟨E, hE'⟩ := run_mono_ev h
        refine T.runsTo_of ⟨hE.1, hE.2.1, hE.2.2.1, .inr ⟨?_, hE.2.2.2⟩⟩
        have h1 := peak_append_ge E (st'.ev ++ [Ctx.base Q])
        have h2 := inUse_le_peak' (st'.ev ++ [Ctx.base Q])
        rw [hE', List.append_assoc]
        omega
    · next r' e => cases h; exact C.done_ok hK hrel e
    · exact nomatch h

end Ctx
end Proven.Ir

/- **The C compiler (C → RISC-V words → rv2arm) is correct on the official Sail ARM v9.4-A model**, stated against
`Proven.Top.armSail` (Spec/ARM/Sail.lean) as `Spec`'s `CompileCorrect` / `CompileRuns` (no loader premise: Sail's
permission predicates are `True`, so `ArmLoader TT TT` always holds). Proved on the proof-side machine
`ArmSail.armSail` (ArmSail/Machine.lean) from `C_correct_rv2arm` / `C_runs_rv2arm` (Nano/V2Self/Proof/Main/ArmTop.lean)
and `a64Sail`, then moved to the Spec machine by `spec_eq` (the two definitions are equal). -/
import Nano.V2Self.Proof.Main.ArmTop
import ArmSail.A64
import Spec.ARM.Sail
namespace ArmSail
open Proven.Top Proven.Top.Alloc NanoMain ArmProof

theorem loader_ok (s : armSail.State) (call : Call) (code x : List UInt8) : JT.ArmLoader (M := armSail) TT TT s call code x :=
  ⟨fun _ _ _ => trivial, fun _ _ => trivial⟩

theorem map_cast {α : Type} (h : α = α) (x : Option α) : x.map (cast h) = x := by cases x <;> rfl

theorem xget_spec (m : Regs) (r : Nat) (h : r < 31) : xget m r = armSailRegister m r := by
  unfold xget; rw [if_pos h]
  match r, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _
  | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _
  | 29, _ | 30, _ => exact map_cast _ _
  | _ + 31, h => omega

theorem reg_hi (m : Regs) (r : Nat) (h : ¬ r < 31) : armSailRegister m r = none := by
  unfold armSailRegister; split <;> first | rfl | omega

theorem obs_spec (s : St) : obsS s = armSailObserve s := by
  simp only [obsS, armSailObserve, pcOf]
  congr 1
  · cases s.regs.get? ._PC <;> rfl
  · funext r; by_cases h : r < 31
    · rw [if_pos h, xget_spec _ _ h]; cases armSailRegister s.regs r <;> rfl
    · rw [if_neg h, reg_hi _ _ h]; rfl

theorem pins_spec (m : Regs) : ArmSailPins m ↔ Pins m :=
  ⟨fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
      a24, a25, a26, a27, a28, a29, a30⟩ => ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30⟩,
   fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
      a24, a25, a26, a27, a28, a29, a30⟩ => ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30⟩⟩

theorem conf_spec (s : St) : ArmSailConfigured s ↔ (∃ n, ArmFullB s n) ∧ (s.regs.get? ._PC).isSome := by
  constructor
  · intro ⟨hp, hb, ⟨n, hn⟩, hc, hx, hpc⟩
    exact ⟨⟨n, (pins_spec _).mp hp, hb, hn, hc, fun i hi => by rw [xget_spec _ _ hi]; exact hx i hi⟩, hpc⟩
  · intro ⟨⟨n, hf⟩, hpc⟩
    exact ⟨(pins_spec _).mpr hf.pins, hf.bt, ⟨n, hf.btn⟩, hf.cc, fun i hi => by rw [← xget_spec _ _ hi]; exact hf.x i hi, hpc⟩

/-- the Spec machine is the proof-side machine -/
theorem spec_eq : Proven.Top.armSail = ArmSail.armSail := by
  unfold Proven.Top.armSail ArmSail.armSail
  congr 1
  · funext s; exact (obs_spec s).symm
  · funext s; exact propext (conf_spec s)

theorem C_correct_armSail : CompileCorrect Proven.Top.armSail (compileOn ArmRA.rv2arm) :=
  spec_eq ▸ show CompileCorrect ArmSail.armSail (compileOn ArmRA.rv2arm) from fun program compiled f eI eO a s call h1 h2 h3 h4 h5 =>
    C_correct_rv2arm a64Sail (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4 h5

theorem C_runs_armSail : CompileRuns Proven.Top.armSail (compileOn ArmRA.rv2arm) :=
  spec_eq ▸ show CompileRuns ArmSail.armSail (compileOn ArmRA.rv2arm) from fun program compiled f eI eO a s call h1 h2 h3 h4 =>
    C_runs_rv2arm a64Sail (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4

end ArmSail

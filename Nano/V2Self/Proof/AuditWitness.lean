/- Nano/V2Self/Proof/AuditWitness: the final theorem `C_correctLO` instantiated for one real program (ParSpec's `ex1`),
for the audit `Testing/notes/NANO_V2_AUDIT.md`.  What is proved here and what is NOT:
* `ex1_computes`: the premise `Computes` holds (the text's meaning is the Lean function `Ex1.m`), unconditionally;
* `ex1_compiles`: the premise `compileC _ = some _` holds GIVEN the parser run `C.y16 (C.s10 x) = a` — that single run is
  checked natively only (Par1's fixed heap layout is out of the kernel's reach, see MainWitness);
* `ex1_applies`: the theorem's conclusion for this program.  Its premise `memoryNeeded … ≤ workLength` is left as a
  hypothesis: `memoryNeeded` is `spaceC`, a `Classical.choose`, for which no upper bound is provable (audit finding 1). -/
import Nano.V2Self.Proof.ParCapBnd
import Nano.V2Self.Proof.MainCert
import Nano.V2Self.Proof.MainWitness

namespace NanoMain.Audit
open Proven Proven.Top Proven.Top.Alloc ParSpec

def src : SrcC := ⟨Witness.x2⟩

theorem ex1_computes : Computes src Ex1.m id id := fun inp => Ex1.cert inp

theorem ex1_compiles (hy : C.y16 (C.s10 Witness.x2) = Witness.a2) :
    compileC src = some ⟨mC Witness.x2, 1, fun inp => [.alloc (spaceC Witness.x2 inp)]⟩ := by
  have hne : mC Witness.x2 ≠ [] := Witness.w2.2.2 hy
  have hlen : Witness.x2.length ≤ 2 ^ 20 := by decide +kernel
  unfold compileC src
  rw [if_pos ⟨hne, hlen⟩]

/-- `C_correctLO` for `ex1`: C's code for this text computes `Ex1.m` on the Sail machine -/
theorem ex1_applies (hy : C.y16 (C.s10 Witness.x2) = Witness.a2) (inp : List UInt8) (startState : riscv.State) (call : Call)
    (hs : StartCorrect riscv startState call (mC Witness.x2) inp) (ho : (Ex1.m inp).length ≤ call.outputLength)
    (hm : spaceC Witness.x2 inp ≤ call.workLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress (Ex1.m inp).length = some (Ex1.m inp) := by
  obtain ⟨fin, h1, h2, h3, h4, -⟩ := C_correctLO src _ Ex1.m id id inp startState call (ex1_compiles hy) ex1_computes hs ho
    (by simpa [memoryNeeded, peak, inUse] using hm)
  exact ⟨fin, h1, h2, h3, h4⟩

end NanoMain.Audit

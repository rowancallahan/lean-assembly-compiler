/- lean-4.34 (Lean 4.34.1): the axioms of the machine-independent and ARM top theorems (the RISC-V instances need the
RISC-V Sail model, which is not built on this branch; see Testing/notes/BRANCHES.md).
usage: lake build Chain434 && lake env lean Testing/scripts/axioms434.lean -/
import Nano.V2Self.Proof.Main.TopOn
import Nano.V2Self.Proof.Main.ArmTop
import Nano.V2Self.Proof.Cert.All
import Nano.V2Self.Proof.SrcLink.Top
#print axioms NanoMain.C_correct_on
#print axioms NanoMain.C_runs_on
#print axioms NanoMain.C_correct_arm
#print axioms NanoMain.C_runs_arm
#print axioms Cert.sem_C
#print axioms SrcGen.link_pc
#print axioms NanoMain.C_correct_rv2arm
#print axioms NanoMain.C_runs_rv2arm

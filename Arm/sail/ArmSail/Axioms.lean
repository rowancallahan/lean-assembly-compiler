/- Axioms of the Sail-model top theorems. Expected: `propext, Classical.choice, Quot.sound` (no `sorryAx`).
`Reduce__1` is generated as an opaque `partial def` (`--lean-partial-function Reduce__1`, Arm/gen/regen.sh): its
`implemented_by` body is not part of the logic, so it adds no axiom. -/
import ArmSail.Top
#print axioms ArmSail.a64Sail
#print axioms ArmSail.C_correct_armSail
#print axioms ArmSail.C_runs_armSail
#print axioms Armv9.Functions.Reduce__1
#print Armv9.Functions.Reduce__1

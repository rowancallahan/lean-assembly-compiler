/- Axioms of the DeepMind milestone theorems (expected: propext, Classical.choice, Quot.sound).
`cd Arm/apc && lake build Blocks.AxiomsDM` (Lean 4.34.1, DeepMind arm64 at /home/user/deps/code-verification b0f729a). -/
import Blocks.ArmDMTop
#print axioms Proven.Apc.Blocks.C_correct_armDM
#print axioms Proven.Apc.Blocks.C_runs_armDM

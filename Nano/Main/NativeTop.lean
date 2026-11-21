/- **The top theorems for the native AArch64 compile** (`compileNative`: C's front end, then `C.a31`, GenArm), GENERIC
over any machine `M` with the A64 steps `A64SemN M X W` (DeepMind: Arm/apc `Blocks/ArmDMNTop.lean`; Sail: only
`a64SailN` is missing), given the bundle `NativeTemplatesOK M X W` of what is not proved yet:
* `V`: the image relation (GenArm's image of a J program);
* `laws : NatLawsOK M X W V` (Run/NatTarget.lean): the image facts and the machine facts (segment law, from the
  per-template runs of Run/ArmNatTm.lean);
* `gen : GenOKG (natTarget M X W V) genNative`: GenArm emits such an image for the J program of the source (lockstep
  with Gen).
`C_correct_native` / `C_runs_native` are `C_correct_g` / `C_runs_g` (Main/TopOn.lean) at `natTarget` with `natLaws`. -/
import Nano.Main.TopOn
import Nano.Run.NatTarget
import Nano.Codegen.GenArm
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

/-- the native code generator from source text: C's front end, then GenArm (`mC` with `a31` for `g41`) -/
def genNative (x : List UInt8) : List UInt8 := C.a31 x (C.o41 (C.y16 (C.s10 x)))

/-- **the native AArch64 compiler** -/
noncomputable def compileNative : SrcC → Option CompiledA := compileGen genNative

/-- **what remains to prove for the native compile** (supplied by M3; until then a hypothesis) -/
structure NativeTemplatesOK (M : Machine) (X W : M.State → Nat → Prop) where
  /-- `V Cj I`: `I` is GenArm's image (code bytes, layout, anchors, dead temporaries) of the J program `Cj` -/
  V : List CallProbe.J → Img → Prop
  laws : NatLawsOK M X W V
  gen : GenOKG (natTarget M X W V) genNative

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- **the native compile is correct on AArch64** (any machine with the A64 steps; loader contract `ArmLoader X W`) -/
theorem C_correct_native (S : A64SemN M X W) (H : NativeTemplatesOK M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileCorrectP M (ArmLoader X W) compileNative :=
  C_correct_g (natLaws S H.laws) genNative H.gen hwin

/-- **the native compile runs correctly on AArch64, with any work block** -/
theorem C_runs_native (S : A64SemN M X W) (H : NativeTemplatesOK M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileRunsP M (ArmLoader X W) compileNative :=
  C_runs_g (natLaws S H.laws) genNative H.gen hwin

end NanoMain

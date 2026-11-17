/- **Stage 2 (the parser) compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`): `stage2S` (= `stage2` on every
input, `Nano.PS.stage2S_eq`) compiled by the S3 front end (`s3_compileB`: program, kernel-checked certificates,
`computes`), then the ONE S3 compiler theorem through the adapter (`Nano.S3Stage.stage`,
`Proven.S3.implements1_spaceOf`): the machine theorem in the linker's form, `stage2S3_implements`. -/
import Compiler.S3.Front
import Nano.ParseS3
import Nano.S3Stage

s3_enc Nano.Tok
s3_enc Nano.PB.Fr
s3_enc Nano.PB.Ctl
s3_enc Nano.PB.St
s3_enc Nano.PB.Res

namespace Nano.PS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileB Stage2S3 := stage2S

set_option maxRecDepth 100000 in
theorem stage2S3_small : smallB Stage2S3.P.S = true := by decide

theorem stage2S3_main : (Stage2S3.P.S.fn Stage2S3.P.main).1.length = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- the IR compiler accepts the program (kernel evaluation of the compiler) -/
theorem stage2S3_compiles : (Ir.compileW (lowerP Stage2S3.P)).isSome = true := by decide +kernel

/-- **the machine theorem of stage 2, route S3** (Sail axioms only) -/
theorem stage2S3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words Stage2S3.P)
      (fun xs => stage2S xs.data.toList) (spaceP Stage2S3.P) (2 ^ 20) true :=
  stage Stage2S3.computes stage2S3_small stage2S3_main stage2S3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2S3_code_len : (S3.words Stage2S3.P).length < 2 ^ 17 := by decide +kernel

/-- the compiled stage computes `stage2` on every input -/
theorem stage2S3_f (x : List UInt8) : (fun xs : ByteArray => stage2S xs.data.toList) (Nano.Link.ofL x) = PB.stage2 x :=
  stage2S_eq x

end Nano.PS

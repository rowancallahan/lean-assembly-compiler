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

end Nano.PS

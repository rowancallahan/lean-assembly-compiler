/- **Stage 2b (the parser machine on the tag format) compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`):
`stage2b` (Nano/ParseS3B.lean; `stage2b (stage2a bs) = stage2 bs` on every input) compiled by `s3_compileF`
(program, kernel-checked certificates, `computes`). The stage theorem: Nano/ParseS3BStage.lean. -/
import Compiler.S3.Front
import Nano.ParseS3B
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
s3_compileF Stage2B := stage2b

end Nano.PS

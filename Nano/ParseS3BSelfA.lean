/- **Stage 2b (the parser machine on the tag format) compiled through S3**, part 1 of 4
(`Testing/notes/NANO_PARSE_S3.md`): `stage2b` (Nano/ParseS3B.lean; `stage2b (stage2a bs) = stage2 bs` on every
input) compiled by `s3_compileF`, split with `s3_part` (Compiler/S3/FrontPart.lean: the same generated commands,
elaborated in index ranges) to keep each build ≤ 5 min: here the program `Stage2B.P`, the oracle and the
certificates of commands [0, 84). -/
import Compiler.S3.FrontPart
import Nano.ParseS3B
import Nano.S3Stage
import Nano.TokS3Enc


s3_enc Nano.PB.Fr
s3_enc Nano.PB.Ctl
s3_enc Nano.PB.St
s3_enc Nano.PB.Res

namespace Nano.PS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Stage2B := stage2b s3_part 0 84

end Nano.PS

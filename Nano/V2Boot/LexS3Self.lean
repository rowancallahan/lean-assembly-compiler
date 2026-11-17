/- B₁: the S3 twin `lexVS` of the v2 stage `Nano.V2S.lexV` (Nano/V2Boot/LexS3.lean) compiled by the S3 front end
(program, kernel-checked certificates, `computes`). Stage theorem: Nano/V2Boot/LexS3Stage.lean. -/
import Compiler.S3.Front
import Nano.V2Boot.LexS3
import Nano.S3Stage

namespace Nano.V2B
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF LexB := Nano.V2B.lexVS

end Nano.V2B

/- B₁: the S3 twin `inlVS` of the v2 stage `Nano.V2S.inlV` (Nano/V2Boot/InlS3.lean) compiled by the S3 front end
(program, kernel-checked certificates, `computes`). Stage theorem: Nano/V2Boot/InlS3Stage.lean. -/
import Compiler.S3.Front
import Nano.V2Boot.InlS3
import Nano.S3Stage

namespace Nano.V2B
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF InlB := Nano.V2B.inlVS

end Nano.V2B

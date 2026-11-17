/- B₁: the S3 twin `p2bVS` of the v2 stage `Nano.V2S.p2bV` (Nano/V2Boot/ParseS3.lean) compiled by the S3 front end
(program, kernel-checked certificates, `computes`). Stage theorem: Nano/V2Boot/ParseS3Stage.lean. -/
import Compiler.S3.Front
import Nano.V2Boot.ParseS3Br
import Nano.S3Stage

namespace Nano.V2B
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 24 in
s3_compileF ParseB := Nano.V2B.p2bVS

end Nano.V2B

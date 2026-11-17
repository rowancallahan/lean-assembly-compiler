/- Stage 2b through S3, part 3 of 4 (Nano/ParseS3BSelfA.lean): commands [88, 172). -/
import Nano.ParseS3BSelfB

namespace Nano.PS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Stage2B := stage2b s3_part 88 172

end Nano.PS

/- Stage 2b through S3, part 2 of 4 (Nano/ParseS3BSelfA.lean): commands [84, 88),
the certificate of function 18 (the largest). -/
import Nano.ParseS3BSelfA

namespace Nano.PS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Stage2B := stage2b s3_part 84 88

end Nano.PS

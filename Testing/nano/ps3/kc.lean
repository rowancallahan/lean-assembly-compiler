import Riscv.Frontx.S3Examples
import Nano.S3Stage
open Proven Proven.S3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem mirror_stage : _ := Nano.S3Stage.stage Proven.S3.Ex.S3Mirror.computes (by decide) (by decide) (by decide +kernel)
#check @mirror_stage
#print axioms mirror_stage

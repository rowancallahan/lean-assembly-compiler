import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseS3
s3_enc Nano.Tok
s3_enc Nano.PB.Fr
s3_enc Nano.PB.Ctl
s3_enc Nano.PB.St
s3_enc Nano.PB.Res
namespace Nano.PS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileB Stage2S3 := stage2S
end Nano.PS

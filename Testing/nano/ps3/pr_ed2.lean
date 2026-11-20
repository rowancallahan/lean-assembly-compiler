import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
open Nano Nano.PB
def ed2 (bs : List UInt8) : List UInt8 := match retF (st0 []) .letB [] with | .go _ s => s.out | _ => bs
set_option maxRecDepth 20000 in
s3_compile Q := ed2
end P

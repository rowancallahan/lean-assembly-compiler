import Compiler.S3.Front
import Nano.S3Stage
namespace Nano.LT
def uniC : UInt64 → List UInt64 → UInt64
  | t, [] => t
  | t, c :: r => if c == 0 then uniC t r else if t == 0 then uniC c r else if t == c then uniC c r else 3
def toW : List UInt8 → List UInt64
  | [] => []
  | x :: r => x.toUInt64 :: toW r
def tst (xs : List UInt8) : List UInt8 := if uniC 0 (toW xs) == 3 then [1] else [0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF TU := tst
end Nano.LT

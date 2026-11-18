/- debug driver: runs the Par1 task machine on the lexed input and prints the heap state (status, cursor, task depth, #tokens, operands, nodes, def, def-name position, ...) and 8 tokens around the cursor as 8-byte words. -/
import Nano.V2Self.C.Par1
namespace C

def z0 (v : UInt64) (o : List UInt8) : List UInt8 :=
  put (put (put (put (put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48)) (v >>> 56)

def z2 : Nat → Buf → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, h, i, e, o => o
  | n + 1, h, i, e, o => if e < i then o else z2 n h (i + 1) e (z0 (bget h (d11 + i)) o)

def z3 (x : Buf) : List UInt8 :=
  let c := bsize x;
  let h := y14 16777216 x 0 (y15 bnew);
  let h := bset h 7 c;
  let h := bset h 0 1;
  let h := bpush h 0;
  let h := bpush h 2;
  let h := v97 16777216 (v1 h 60 0 0);
  let s := bget h 0;
  let p := bget h 3;
  let a := bget h 5;
  let b := bget h 8;
  let d := bget h 9;
  let f := bget h 12;
  let g := bget h 22;
  z2 16 h (p - 8) (p + 8) (z0 g (z0 f (z0 d (z0 b (z0 a (z0 p (z0 c (z0 s []))))))))

def m (x : List UInt8) : List UInt8 := z3 (s10 x)

end C

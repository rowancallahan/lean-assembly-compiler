def g (b : Buf) (i : UInt64) : UInt64 := bget b i
def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew (len x);
  let c := bset b 0 7;
  put [] (g b 0 + bget c 0)

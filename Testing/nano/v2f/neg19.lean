def g (b : Buf) : Buf := bset b 0 1
def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew (len x);
  let c := g b;
  put [] (bget b 0 + bget c 0)

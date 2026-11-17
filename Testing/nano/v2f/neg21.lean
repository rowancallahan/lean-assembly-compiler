def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew 3;
  put [] (bget b (bget (bset b 0 0) 0))

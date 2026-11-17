def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew 1;
  put [] (bget b 0)

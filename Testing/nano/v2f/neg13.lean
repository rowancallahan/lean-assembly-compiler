def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew 1;
  put (put [] (bget (bpush b 2) 1)) (bsize b)

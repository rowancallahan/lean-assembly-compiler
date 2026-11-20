def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew 1;
  let p := (b, len x);
  put (put [] (bget p.1 0)) (bsize b)

def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew 1;
  let c := bset b 0 (len x);
  put [] (bget b 0 + bget c 0)

def m (x : List UInt8) : List UInt8 :=
  let p := (1 - 2, len x);
  put [] p.1

def m (x : List UInt8) : List UInt8 :=
  let o := put [] 1;
  let p := (o, len x);
  put (put p.1 2) (len x + rd x p.2 + len p.1)

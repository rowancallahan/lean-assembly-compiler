def m (x : List UInt8) : List UInt8 :=
  let o := put [] 1;
  put (put o 2) (len x + rd x (len (put o 3)))

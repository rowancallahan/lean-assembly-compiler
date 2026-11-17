def m (x : List UInt8) : List UInt8 :=
  let o := put [] 1;
  if len x < 3 then put o 2 else put (put o 3) (len o)

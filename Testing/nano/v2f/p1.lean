def z : UInt64 := 0
def s (p : UInt64 × UInt64) (a : UInt64) : UInt64 × UInt64 := (p.2 + a, p.1 * 3 - a)
def w (x : List UInt8) (o : List UInt8) (i : UInt64) : List UInt8 := put o (rd x i <<< 1)
def m (x : List UInt8) : List UInt8 :=
  let q := s (rd x 0, rd x 1) (len x);
  let (a, b) := s q (rd x 2);
  let r := (a, (b, a ^^^ b));
  if r.2.1 < a then put (put (w x [] 1) (r.2.2 >>> 3)) b else put (put [] a) (r.1 + r.2.1)

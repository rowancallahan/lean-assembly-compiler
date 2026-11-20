def f (a : UInt64 × UInt64) : UInt64 := a.1
def m (x : List UInt8) : List UInt8 :=
  put [] (f (len x))

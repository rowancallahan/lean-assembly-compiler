def g (a : UInt64) : UInt64 := bsize (bpush bnew a)
def f : Nat → UInt64 → UInt64
  | 0, a => a
  | n + 1, a => f n (a + g a)
def m (x : List UInt8) : List UInt8 := put [] (f (len' x) 0)

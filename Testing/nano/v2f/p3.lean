def z : UInt64 := 0
def r : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => []
  | n + 1, x, i, o =>
    if i == z then o else
    let j := i - 1;
    r n x j (put o (rd x j))
def m (x : List UInt8) : List UInt8 :=
  r (len' x) x (len x) (put [] (len x))

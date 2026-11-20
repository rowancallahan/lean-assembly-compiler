def c : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o => if i < len x then c n x (i + 1) (put o (rd x i + 1)) else o
def s : Nat → List UInt8 → UInt64 × UInt64 → UInt64 × UInt64
  | 0, x, p => p
  | n + 1, x, p =>
    let (i, a) := p;
    if len x <= i then (i, a) else s n x (i + 1, a * 31 + rd x i)
def m (x : List UInt8) : List UInt8 :=
  let q := s (len' x + 1) x (len x - len x, len x);
  put (c (len' x * 2 + 1) x (len x - len x) []) (q.2 >>> 3)

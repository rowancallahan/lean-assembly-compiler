def k : UInt64 := 3
def a (p : UInt64) (b : UInt64) : UInt64 :=
  if p == 3 || p == 4 && b ≤ 7 then ((b &&& 1) <<< 7) ||| k
  else if (p ≠ 5 || b < 2) && (p ≤ 9 || b == 1) then b + p else p
def l : Nat → List UInt8 → UInt64 → List UInt64 → List UInt64
  | 0, x, i, w => w
  | n + 1, x, i, w => if i < len x && bsize w < 100 then l n x (i + 1) (bpush w (a (rd x i) i)) else w
def q : Nat → List UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, w, i, o => o
  | n + 1, w, i, o =>
    if bsize w ≤ i || i == 50 then o else
    let v := bget w i;
    q n w (i + 1) (put o v)
def m (x : List UInt8) : List UInt8 :=
  q (len' x) (l (len' x) x (len x - len x) bnew) (len x - len x) (put [] (len x))

def h : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, x, i, b => b
  | n + 1, x, i, b =>
    if len x <= i then b else
    let c := rd x i &&& 15;
    h n x (i + 1) (bset b c (bget b c + 1))
def z : Nat → UInt64 → Buf → Buf
  | 0, i, b => b
  | n + 1, i, b => z n (i + 1) (bpush b (i - i))
def e : Nat → UInt64 × Buf → List UInt8 → List UInt8
  | 0, s, o => o
  | n + 1, s, o =>
    let (i, b) := s;
    if bsize b <= i then o else
    let v := bget b i + i * bsize b;
    e n (i + 1, b) (put o v)
def m (x : List UInt8) : List UInt8 :=
  let b := h (len' x + 1) x (len x - len x) (z 16 (len x - len x) bnew);
  let o := put [] (bsize b);
  e 17 (len x - len x, bset b 99 7) o

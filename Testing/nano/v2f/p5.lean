def l : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, x, i, b => b
  | n + 1, x, i, b => if len x <= i then b else l n x (i + 1) (bpush b (rd x i))
def s : Nat → Buf → UInt64 → Buf
  | 0, b, i => b
  | n + 1, b, i =>
    if bsize b <= i + 1 then b else
    let p := bget b i;
    let q := bget b (i + 1);
    if q < p then s n (bset (bset b i q) (i + 1) p) (i + 1) else s n b (i + 1)
def r : Nat → List UInt8 → Buf → Buf
  | 0, x, b => b
  | n + 1, x, b => r n x (s (len' x) b (len x - len x))
def w : Nat → List UInt8 → Buf → UInt64 → List UInt8 → List UInt8
  | 0, x, b, i, o => o
  | n + 1, x, b, i, o =>
    if len x <= i then o else
    let v := bget b i;
    w n x b (i + 1) (put o v)
def m (x : List UInt8) : List UInt8 :=
  w (len' x) x (r (len' x) x (l (len' x) x (len x - len x) bnew)) (len x - len x) (put [] (len x))

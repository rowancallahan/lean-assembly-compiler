def g (b : Buf) (i : UInt64) : UInt64 := bget b i + bsize b
def h (b : Buf) (i : UInt64) : UInt64 := g b i * g b (i + 1)
def l : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, x, i, b => b
  | n + 1, x, i, b => if len x <= i then b else l n x (i + 1) (bpush b (rd x i))
def s : Nat → Buf → UInt64 → List UInt8 → List UInt8
  | 0, b, i, o => o
  | n + 1, b, i, o =>
    if bsize b <= i then o else
    let v := h b i;
    s n b (i + 1) (put o v)
def m (x : List UInt8) : List UInt8 :=
  let b := l (len' x) x (len x - len x) bnew;
  let k := h b 0 + g b 1;
  s (len' x) b (len x - len x) (put [] k)

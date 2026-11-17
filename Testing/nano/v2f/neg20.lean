def r : Nat → Buf → UInt64 → UInt64
  | 0, b, i => i
  | n + 1, b, i => r n b (i + bget b 0)
def m (x : List UInt8) : List UInt8 :=
  let b := bpush bnew (len x);
  let c := bset b 0 9;
  put [] (r 3 b 1 + bget c 0)

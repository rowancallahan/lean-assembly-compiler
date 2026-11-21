/- Nano/V2Self: the inliner stage = the TAIL-ONLY inliner `inlTV` (Nano/V2S/InlT.lean) in the nano subset: a word-buffer
table `u` (code of every def read so far, then the current one) and the offsets `w`; a call copies `u[w[t], w[t+1])`.
Output-carrying helpers take the input `x` first (a def's first `List UInt8` parameter is its input). -/
import Nano.V2Self.Prelude

def k100 : UInt64 := 16777216

def j0 (m q : UInt64) (o : List UInt8) : List UInt8 := put (put o m) q

def j1 (x : List UInt8) (o : List UInt8) : List UInt8 :=
  j0 4 0 (j0 3 0 (j0 2 0 (j0 2 1 (j0 2 2 (j0 2 3 (j0 2 4 (j0 2 5 (j0 2 6 (j0 1 0 o)))))))))

def j2 (x : List UInt8) (o : List UInt8) : List UInt8 :=
  j0 11 7 (j0 10 56 (j0 11 6 (j0 10 48 (j0 11 5 (j0 10 40 (j0 11 4 (j0 10 32 (j0 11 3 (j0 10 24 (j0 11 2 (j0 10 16 (j0 11 1 (j0 10 8 (j0 11 0 (j0 10 0 o)))))))))))))))

def j3 : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, k, o => o
  | n + 1, x, k, o => if k == 0 then o else j3 n x (k - 1) (j1 x o)

def j4 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, u, i, e => u
  | n + 1, u, i, e => if i < e then
      let v := bget u i;
      j4 n (bpush u v) (i + 1) e
    else u

def j5 : Nat → List UInt8 → Buf → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, x, u, i, e, o => o
  | n + 1, x, u, i, e, o =>
    if i < e then
      let v := bget u i;
      j5 n x u (i + 1) e (put o v)
    else o

def j6 (x : List UInt8) (k : UInt64) (u w : Buf) : List UInt8 :=
  let o := j3 256 x k (j0 0 0 []);
  let o1 := if 2 ≤ bsize w then j5 16777216 x u (bget w (bsize w - 2)) (bget w (bsize w - 1)) o else o;
  j0 12 0 (j2 x (j0 7 0 o1))

def j7 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → Buf → Buf → List UInt8
  | 0, x, p, h, k, u, w => []
  | n + 1, x, p, h, k, u, w =>
    if p + 2 ≤ len x then
      let q := rd x p;
      let s := rd x (p + 1);
      let z := bsize u;
      if q == 13 then j7 n x (p + 2) h s u (bpush w z)
      else if q == 14 then j7 n x (p + 2) s k u w
      else if q == 15 then
        if h * 256 + s + 1 < bsize w then
          if z + (bget w (h * 256 + s + 1) - bget w (h * 256 + s)) ≤ k100 then
            j7 n x (p + 2) h k (j4 16777216 u (bget w (h * 256 + s)) (bget w (h * 256 + s + 1))) w
          else []
        else j7 n x (p + 2) h k u w
      else if z + 2 ≤ k100 then j7 n x (p + 2) h k (bpush (bpush u q) s) w
      else []
    else j6 x k u w

def j8 (x : List UInt8) : List UInt8 := j7 (len' x + 1) x 0 0 0 bnew (bpush bnew 0)

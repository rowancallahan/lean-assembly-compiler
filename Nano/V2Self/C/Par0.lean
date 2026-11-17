/- Nano/V2Self/C: parser increment A (Testing/notes/NANO_V2_IR.md): `def f (a b : UInt64) : UInt64 := EXPR` with literals, parameters, parentheses and the
binary operators `|||` `&&&` `+ -` `*` `<<<` `>>>` (Lean precedences 55 60 65 70 75, left associative; shifts take a numeral).  Input: the token Buf of Lex2.
Output Buf (words): [2 (IRV), 20 (DEF), id 0, npw, nslots, kind 0, nres 1, pre-order AST, 21 (ENDDEF)]; nodes: CONST 1 v | LOCAL 2 slot w | BIN 3 op a b
(op: add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7).  Empty Buf = rejected.  One heap Buf h: [0] ok flag, [1] root, [3] position, [4] nparams, params at 9000.., task
stack at 1000.. (code, arg), operand stack at 5000.., nodes at 10000 + 4 i (tag a b c). -/
import Nano.V2Self.C.Base
namespace C

def y0 : Nat → Buf → UInt64 → UInt64
  | 0, h, q => 0
  | n + 1, h, q =>
    if q < bget h 7 then
      if bget h (40000 + q) == 0 then q + 1 else y0 n h (q + 2)
    else 0

def y1 (h : Buf) (p : UInt64) : UInt64 :=
  if bget h (40000 + p) == 5 then p + 9 else if bget h (40000 + p) == 14 then y0 16777216 h (p + 1) else p + 1

def y2 : Nat → Buf → UInt64 → UInt64 → UInt64
  | 0, h, a, b => 0
  | n + 1, h, a, b =>
    if bget h (40000 + a) == bget h (40000 + b) then
      if bget h (40000 + a) == 0 then 1 else if bget h (40000 + (a + 1)) == bget h (40000 + (b + 1)) then y2 n h (a + 2) (b + 2) else 0
    else 0

def y3 : Nat → Buf → UInt64 → UInt64 → UInt64
  | 0, h, i, p => 0
  | n + 1, h, i, p =>
    if i < bget h 4 then
      if y2 16777216 h (bget h (9000 + i) + 1) (p + 1) == 1 then i + 1 else y3 n h (i + 1) p
    else 0

def y7 (h : Buf) (p : UInt64) : UInt64 :=
  bget h (40000 + (p + 1)) ||| ((bget h (40000 + (p + 2))) <<< 8) ||| ((bget h (40000 + (p + 3))) <<< 16) ||| ((bget h (40000 + (p + 4))) <<< 24)
  ||| ((bget h (40000 + (p + 5))) <<< 32) ||| ((bget h (40000 + (p + 6))) <<< 40) ||| ((bget h (40000 + (p + 7))) <<< 48) ||| ((bget h (40000 + (p + 8))) <<< 56)

def y8 (t : UInt64) : UInt64 :=
  if t == 26 then 4 else if t == 27 then 5 else if t == 10 then 1 else if t == 11 then 2 else if t == 12 then 3
  else if t == 28 then 6 else if t == 29 then 7 else 0

def y10 (t : UInt64) : UInt64 :=
  if t == 27 then 55 else if t == 26 then 60 else if t == 10 then 65 else if t == 11 then 65 else if t == 12 then 70
  else if t == 28 then 75 else if t == 29 then 75 else 0

def y5 : Nat → Buf → Buf
  | 0, h => h
  | n + 1, h => y5 n (bpush h 0)

-- the task machine; tasks: 1 EXPR prec, 2 OPS prec, 3 ATOM, 4 RPAREN, 5 REDUCE op.  Reads of h are let-bound before h is consumed.
def y9 : Nat → UInt64 → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, p, g, k, m, h => h
  | n + 1, p, g, k, m, h =>
    let u := g - 1;
    let c := bget h (1000 + 2 * u);
    let a := bget h (1001 + 2 * u);
    let t := bget h (40000 + p);
    let b := 10000 + 4 * m;
    let q1 := bget h (5000 + k - 1);
    let q2 := bget h (5000 + k - 2);
    let s := y3 16777216 h 0 p;
    let v1 := y7 h p;
    let v2 := y7 h (p + 1);
    let o := y8 t;
    let r := y10 t;
    let t1 := bget h (40000 + (p + 1));
    let e1 := y0 16777216 h (p + 1);
    if g == 0 then bset (bset (bset h 0 1) 1 q1) 3 p
    else if c == 1 then y9 n p (u + 2) k m (bset (bset (bset (bset h (1000 + 2 * u) 2) (1001 + 2 * u) a) (1002 + 2 * u) 3) (1003 + 2 * u) 0)
    else if c == 3 then
      if t == 5 then y9 n (p + 9) u (k + 1) (m + 1) (bset (bset (bset h (5000 + k) m) b 1) (b + 1) v1)
      else if t == 14 then
        if s == 0 then h
        else y9 n e1 u (k + 1) (m + 1) (bset (bset (bset h (5000 + k) m) b 2) (b + 1) (s - 1))
      else if t == 6 then y9 n (p + 1) (u + 2) k m (bset (bset (bset (bset h (1000 + 2 * u) 4) (1001 + 2 * u) 0) (1002 + 2 * u) 1) (1003 + 2 * u) 0)
      else h
    else if c == 4 then if t == 7 then y9 n (p + 1) u k m h else h
    else if c == 2 then
      if o == 0 then y9 n p u k m h
      else if r < a then y9 n p u k m h
      else if o == 6 then
        if t1 == 5 then y9 n (p + 10) (u + 1) k (m + 2) (bset (bset (bset (bset (bset (bset (bset (bset (bset h b 1) (b + 1) v2) (b + 4) 3) (b + 5) o) (b + 6) q1) (b + 7) m) (5000 + k - 1) (m + 1)) (1000 + 2 * u) 2) (1001 + 2 * u) a)
        else h
      else if o == 7 then
        if t1 == 5 then y9 n (p + 10) (u + 1) k (m + 2) (bset (bset (bset (bset (bset (bset (bset (bset (bset h b 1) (b + 1) v2) (b + 4) 3) (b + 5) o) (b + 6) q1) (b + 7) m) (5000 + k - 1) (m + 1)) (1000 + 2 * u) 2) (1001 + 2 * u) a)
        else h
      else y9 n (p + 1) (u + 3) k m (bset (bset (bset (bset (bset (bset h (1000 + 2 * u) 2) (1001 + 2 * u) a) (1002 + 2 * u) 5) (1003 + 2 * u) o) (1004 + 2 * u) 1) (1005 + 2 * u) (r + 1))
    else if c == 5 then
      y9 n p u (k - 1) (m + 1) (bset (bset (bset (bset (bset h b 3) (b + 1) a) (b + 2) q2) (b + 3) q1) (5000 + k - 2) m)
    else h

def y11 : Nat → UInt64 → UInt64 → Buf → Buf
  | 0, p, m, h => h
  | n + 1, p, m, h =>
    let t := bget h (40000 + p);
    let j := bget h 4;
    let e1 := y0 16777216 h (p + 1);
    let t1 := bget h (40000 + (p + 1));
    let t2 := bget h (40000 + (p + 2));
    if m == 0 then
      if t == 6 then y11 n (p + 1) 1 h
      else if t == 8 then
        if t1 == 3 then
          if t2 == 9 then bset (bset h 3 (p + 3)) 6 1 else h
        else h
      else h
    else
      if t == 14 then y11 n e1 1 (bset (bset h (9000 + j) p) 4 (j + 1))
      else if t == 8 then
        if t1 == 3 then
          if t2 == 7 then y11 n (p + 3) 0 h else h
        else h
      else h

def y12 : Nat → Buf → UInt64 → Buf → Buf
  | 0, h, d, o => bnew
  | n + 1, h, d, o =>
    if d == 0 then o
    else
      let i := bget h (20000 + d - 1);
      let b := 10000 + 4 * i;
      let z4 := bget h b;
      let f1 := bget h (b + 1);
      let f2 := bget h (b + 2);
      let f3 := bget h (b + 3);
      if z4 == 1 then y12 n h (d - 1) (bpush (bpush o 1) f1)
      else if z4 == 2 then y12 n h (d - 1) (bpush (bpush (bpush o 2) f1) 1)
      else y12 n (bset (bset h (20000 + d - 1) f3) (20000 + d) f2) (d + 1) (bpush (bpush o 3) f1)

def y14 : Nat → Buf → UInt64 → Buf → Buf
  | 0, x, i, h => h
  | n + 1, x, i, h =>
    let v := bget x i;
    if i < bsize x then y14 n x (i + 1) (bpush h v) else h

def y13 (x : Buf) : Buf :=
  let c := bsize x;
  let h0 := bset (y14 16777216 x 0 (y5 40000 bnew)) 7 c;
  let t0 := bget h0 40000;
  let t1 := bget h0 40001;
  if t0 == 1 then
    if t1 == 14 then
      let e0 := y0 16777216 h0 2;
      let h := y11 16777216 e0 0 h0;
      let z1 := bget h 6;
      let p0 := bget h 3;
      if z1 == 1 then
        let g := y9 16777216 p0 1 0 0 (bset (bset h 1000 1) 1001 0);
        let z2 := bget g 0;
        let p1 := bget g 3;
        let z3 := bget g 1;
        let j := bget g 4;
        if z2 == 1 then
          if p1 == c then bpush (y12 16777216 (bset g 20000 z3) 1 (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 2) 20) 0) j) j) 0) 1)) 21
          else bnew
        else bnew
      else bnew
    else bnew
  else bnew

end C

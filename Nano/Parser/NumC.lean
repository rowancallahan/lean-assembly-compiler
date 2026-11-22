/- Nano/Parser/NumC: the NUMERAL TYPING check `u10` of the parser's output (specification: `NumSpec.numOkP`,
Nano/Parser/NumSpec.lean).  Input: the serialized program `ParSpec.serialize p` (IR v2.1); output: the same Buf if every
def passes, else the EMPTY Buf.  Per def (`u48`):
* the MAIN machine `u40` walks the body in pre-order with an explicit TASK stack `t` (records of 3 words: kind, a, b;
  `tt` records): 0 COL d (`col` at demand d), 1 LIT (`litG`), 2 CMP (`cmpG`: the two operands at the cursor), 3 LETG s
  (`letG`), 4 CLOSE d gb (end a group), 5 POPM bt (drop let bindings), 6 BINDM s pos (bind slot s to `lw` of the value
  at pos), 7 COLSEQ k (COL 1 on the next k nodes), 8 COLAT pos (COL 1 at pos), 9 LPSEQ s k (letG of a pair's fields).
  The cursor `c` moves through the serialization; every failed shape rule aborts (reject).  Groups are appended to `g`
  as records [n, d, ar, n slots] (in completion order); the open groups' slots are a stack in `s` (`gb`: the innermost
  group's base, where its arithmetic flag is kept, its slots above).  The environment is a BINDING CHAIN `b` (records
  [flags, slot, count], top `bt`), looked up from the innermost binding (`u18`).
* `lw` is the machine `u28` (tasks 0 NODE, 1 FIRST s, 2 AND s, 3 LEN s, 4 ZIP s, 5 BIND slot s0, 6 UNBIND bt,
  7 SEQ k; values: the per-word flags as consecutive words of `v`, top `vt`), on the same binding chain;
  `spineLet` is `u14`, `leaves` is `u13`, `shapeOk` is `u33` (all with explicit position stacks); `u12` skips nodes.
* the classes: `u56` runs the rounds of `marked` (a slot's word = the round that marked it), `u58` checks the groups. -/
import Nano.Codegen.Gen
namespace C

-- set word j (j ≤ size)
def u20 (b : Buf) (j v : UInt64) : Buf := if j < bsize b then bset b j v else bpush b v

-- a rejected tree task's result
def u64 (b t s y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let z := bsize b + bsize t + bsize s + bsize y + bsize y1 + bsize y2;
  (b, (0, (t, (0, (0, (s, (0, (0, (0, (y, (y1, y2)))))))))))

-- a tree task's result
def u65 (b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb ok : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let z := bsize b + bsize t + bsize s + bsize y + bsize y1 + bsize y2;
  (b, (bt, (t, (tt, (c, (s, (st, (gb, (ok, (y, (y1, y2)))))))))))

-- the end of k consecutive nodes from position i (0: error)
def u12 : Nat → Buf → UInt64 → UInt64 → UInt64
  | 0, x, i, k => 0
  | n + 1, x, i, k =>
    if k == 0 then i
    else
      let t := bget x i;
      if t == 1 then u12 n x (i + 2) (k - 1)
      else if t == 2 then u12 n x (i + 3) (k - 1)
      else if t == 3 then u12 n x (i + 2) (k + 1)
      else if t == 4 then u12 n x (i + 2) (k + 3)
      else if t == 5 then u12 n x (i + 3) (k + 1)
      else if t == 6 then u12 n x (i + 2) (k - 1 + bget x (i + 1))
      else if t == 8 then u12 n x (i + 3) (k - 1 + bget x (i + 2))
      else if t == 9 then u12 n x (i + 2) (k - 1 + g33 (bget x (i + 1)))
      else if t == 10 then u12 n x (i + 1) (k + 1)
      else if t == 11 then u12 n x (i + 1) k
      else 0

-- the end of the node at i (0: error)
def u15 (x : Buf) (i : UInt64) : UInt64 := if i == 0 then 0 else u12 16777216 x i 1

-- the node at q is a shift (1)
def u34 (x : Buf) (q : UInt64) : UInt64 :=
  if bget x q == 3 then (if bget x (q + 1) == 6 then 1 else if bget x (q + 1) == 7 then 1 else 0) else 0

-- leaves: the operands of the operator trees on the work stack w (top t), written to p from pt; (p, (pt, (w, 1))), ok 0 on error
def u13 : Nat → Buf → Buf → UInt64 → Buf → UInt64 → Buf × (UInt64 × (Buf × UInt64))
  | 0, x, p, pt, w, t => (p, (pt, (w, 0)))
  | n + 1, x, p, pt, w, t =>
    if t == 0 then (p, (pt, (w, 1)))
    else
      let q := bget w (t - 1);
      if bget x q == 3 then
        (if u34 x q == 1 then u13 n x (u20 p pt q) (pt + 1) w (t - 1)
         else
           (let e := u15 x (q + 2);
            if e == 0 then (p, (pt, (w, 0)))
            else u13 n x p pt (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1)))
      else u13 n x (u20 p pt q) (pt + 1) w (t - 1)

-- the scratch buffers are below 2^39 words (1)
def u63 (p w : Buf) : UInt64 := if bsize p < 549755813888 then (if bsize w < 549755813888 then 1 else 0) else 0

-- the leaves of the node at i, written to p from pt (w: the work stack)
def u16 (x p : Buf) (pt : UInt64) (w : Buf) (i : UInt64) : Buf × (UInt64 × (Buf × UInt64)) :=
  if u63 p w == 1 then u13 16777216 x p pt (u20 w 0 i) 1 else (p, (pt, (w, 0)))

-- spineLet of the nodes on the work stack: (w, r), r 1 some, 0 none, 2 error
def u14 : Nat → Buf → Buf → UInt64 → Buf × UInt64
  | 0, x, w, t => (w, 2)
  | n + 1, x, w, t =>
    if t == 0 then (w, 0)
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 5 then (w, 1)
      else if g == 4 then
        (let b := u15 x (u15 x (q + 2));
         let e := u15 x b;
         if e == 0 then (w, 2) else u14 n x (u20 (u20 w (t - 1) e) t b) (t + 1))
      else u14 n x w (t - 1)

-- spineLet of the node at i (w: the work stack)
def u17 (x w : Buf) (i : UInt64) : Buf × UInt64 :=
  if bsize w < 549755813888 then u14 16777216 x (u20 w 0 i) 1 else (w, 2)

-- post (a shift, or after one) of the nodes on the work stack: (w, r), r 1 some, 0 none, 2 error
def u71 : Nat → Buf → Buf → UInt64 → Buf × UInt64
  | 0, x, w, t => (w, 2)
  | n + 1, x, w, t =>
    if t == 0 then (w, 0)
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 3 then
        (if u34 x q == 1 then (w, 1)
         else
           (let e := u15 x (q + 2);
            if e == 0 then (w, 2) else u71 n x (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1)))
      else if g == 4 then
        (let p := u15 x (u15 x (q + 2));
         if p == 0 then (w, 2) else u71 n x (u20 w (t - 1) p) t)
      else if g == 5 then
        (let p := u15 x (q + 3);
         if p == 0 then (w, 2) else u71 n x (u20 w (t - 1) p) t)
      else u71 n x w (t - 1)

-- post of the node at i (w: the work stack)
def u72 (x w : Buf) (i : UInt64) : Buf × UInt64 :=
  if bsize w < 549755813888 then u71 16777216 x (u20 w 0 i) 1 else (w, 2)

-- slot q in the binding chain b (top t; records [flags, slot, count]): 0 / 1, 2 unbound, 3 error
def u18 : Nat → Buf → UInt64 → UInt64 → UInt64
  | 0, b, t, q => 3
  | n + 1, b, t, q =>
    if t == 0 then 2
    else if t < 2 then 3
    else
      let m := bget b (t - 1);
      let s := bget b (t - 2);
      if t - 2 < m then 3
      else if q < s then u18 n b (t - 2 - m) q
      else if q - s < m then bget b (t - 2 - m + (q - s))
      else u18 n b (t - 2 - m) q

-- push the env words of the k slots from s to v (top vt): (v, (vt, ok))
def u22 : Nat → Buf → UInt64 → Buf → UInt64 → UInt64 → UInt64 → Buf × (UInt64 × UInt64)
  | 0, b, bt, v, vt, s, k => (v, (vt, 0))
  | n + 1, b, bt, v, vt, s, k =>
    if k == 0 then (v, (vt, 1))
    else
      let e := u18 16777216 b bt s;
      if e == 3 then (v, (vt, 0))
      else u22 n b bt (u20 v vt (if e == 1 then 1 else 0)) (vt + 1) (s + 1) (k - 1)

-- push k zero words to v
def u23 : Nat → Buf → UInt64 → UInt64 → Buf × (UInt64 × UInt64)
  | 0, v, vt, k => (v, (vt, 0))
  | n + 1, v, vt, k => if k == 0 then (v, (vt, 1)) else u23 n (u20 v vt 0) (vt + 1) (k - 1)

-- zip: v[s + j] := v[s + 1 + j] and v[m + j] for j < k
def u24 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, v, s, m, j, k => (v, 0)
  | n + 1, v, s, m, j, k =>
    if j < k then u24 n (bset v (s + j) (bget v (s + 1 + j) &&& bget v (m + j))) s m (j + 1) k else (v, 1)

-- copy v[j .. e) to b at bt
def u25 : Nat → Buf → UInt64 → Buf → UInt64 → UInt64 → Buf × (UInt64 × UInt64)
  | 0, b, bt, v, j, e => (b, (bt, 0))
  | n + 1, b, bt, v, j, e => if j < e then u25 n (u20 b bt (bget v j)) (bt + 1) v (j + 1) e else (b, (bt, 1))

-- push the binding (v[j .. e), slot s) to the chain b
def u26 (b : Buf) (bt : UInt64) (v : Buf) (j e s : UInt64) : Buf × (UInt64 × UInt64) :=
  let (b1, z) := u25 16777216 b bt v j e;
  let (t1, k) := z;
  (u20 (u20 b1 t1 s) (t1 + 1) (e - j), (t1 + 2, k))

-- task record n := (k, a, c)
def u27 (t : Buf) (n k a c : UInt64) : Buf := u20 (u20 (u20 t (3 * n) k) (3 * n + 1) a) (3 * n + 2) c

-- the work buffers are below 2^40 words (1)
def u35 (v t b : Buf) : UInt64 :=
  if bsize v < 1099511627776 then (if bsize t < 1099511627776 then (if bsize b < 1099511627776 then 1 else 0) else 0) else 0

def u36 (b t g s : Buf) : UInt64 :=
  if bsize b < 1099511627776 then
    (if bsize t < 1099511627776 then (if bsize g < 1099511627776 then (if bsize s < 1099511627776 then 1 else 0) else 0) else 0)
  else 0

-- lw: the NODE task at the cursor c (tt: the tasks below it)
def u29 (x d b : Buf) (bt : UInt64) (v : Buf) (vt : UInt64) (t : Buf) (tt c : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64)))) :=
  let g := bget x c;
  let w := (if g == 9 then 1 else if g == 10 then 1 else if g == 11 then 1 else if g == 3 then u34 x c else 0);
  if w == 1 then
    (let e := u15 x c;
     (u20 v vt 0, (vt + 1, (t, (tt, (e, (if e == 0 then 0 else 1)))))))
  else if g == 1 then (u20 v vt 1, (vt + 1, (t, (tt, (c + 2, 1)))))
  else if g == 2 then
    (let (v1, z) := u22 16777216 b bt v vt (bget x (c + 1)) (bget x (c + 2));
     let (vt1, ok) := z;
     (v1, (vt1, (t, (tt, (c + 3, ok))))))
  else if g == 3 then
    (v, (vt, (u27 (u27 (u27 (u27 (u27 t tt 2 vt 0) (tt + 1) 1 (vt + 1) 0) (tt + 2) 0 0 0) (tt + 3) 1 vt 0) (tt + 4) 0 0 0,
      (tt + 5, (c + 2, 1)))))
  else if g == 4 then
    (let p := u15 x (u15 x (c + 2));
     (u20 v vt 0, (vt + 1, (u27 (u27 (u27 (u27 t tt 4 vt 0) (tt + 1) 0 0 0) (tt + 2) 3 vt 0) (tt + 3) 0 0 0,
       (tt + 4, (p, (if p == 0 then 0 else 1)))))))
  else if g == 5 then
    (v, (vt, (u27 (u27 (u27 (u27 t tt 6 bt 0) (tt + 1) 0 0 0) (tt + 2) 5 (bget x (c + 1)) vt) (tt + 3) 0 0 0,
      (tt + 4, (c + 3, 1)))))
  else if g == 6 then (v, (vt, (u27 t tt 7 (bget x (c + 1)) 0, (tt + 1, (c + 2, 1)))))
  else if g == 8 then
    (let e := u15 x c;
     let i := bget x (c + 1);
     let (v1, z) := u23 16777216 v vt (if 2 * i < bsize d then bget d (2 * i + 1) else 1);
     let (vt1, ok) := z;
     (v1, (vt1, (t, (tt, (e, (if e == 0 then 0 else ok)))))))
  else (v, (vt, (t, (tt, (c, 0)))))

-- the lw machine: (b, (v, (vt, (cursor, (ok, t)))))
def u28 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → Buf → UInt64 → UInt64 →
    Buf × (Buf × (UInt64 × (UInt64 × (UInt64 × Buf))))
  | 0, x, d, b, bt, v, vt, t, tt, c => (b, (v, (vt, (c, (0, t)))))
  | n + 1, x, d, b, bt, v, vt, t, tt, c =>
    if tt == 0 then (b, (v, (vt, (c, (1, t)))))
    else if u35 v t b == 0 then (b, (v, (vt, (c, (0, t)))))
    else
      let k := bget t (3 * tt - 3);
      let a := bget t (3 * tt - 2);
      let a2 := bget t (3 * tt - 1);
      let u := tt - 1;
      if k == 0 then
        (let (v1, z) := u29 x d b bt v vt t u c;
         let (vt1, z1) := z;
         let (t1, z2) := z1;
         let (tt1, z3) := z2;
         let (c1, ok) := z3;
         if ok == 1 then u28 n x d b bt v1 vt1 t1 tt1 c1 else (b, (v1, (vt1, (c1, (0, t1))))))
      else if k == 1 then u28 n x d b bt (u20 v a (if a < vt then bget v a else 0)) (a + 1) t u c
      else if k == 2 then u28 n x d b bt (bset v a (bget v a &&& bget v (a + 1))) (a + 1) t u c
      else if k == 3 then u28 n x d b bt (bset v a (vt - a - 1)) vt t u c
      else if k == 4 then
        (let l := bget v a;
         let m := a + 1 + l;
         let e := vt - m;
         let q := (if l < e then l else e);
         let (v1, ok) := u24 16777216 v a m 0 q;
         if ok == 1 then u28 n x d b bt v1 (a + q) t u c else (b, (v1, (vt, (c, (0, t))))))
      else if k == 5 then
        (let (b1, z) := u26 b bt v a2 vt a;
         let (bt1, ok) := z;
         if ok == 1 then u28 n x d b1 bt1 v a2 t u c else (b1, (v, (vt, (c, (0, t))))))
      else if k == 6 then u28 n x d b a v vt t u c
      else if k == 7 then
        (if a == 0 then u28 n x d b bt v vt t u c
         else u28 n x d b bt v vt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 0 0) (tt + 1) c)
      else (b, (v, (vt, (c, (0, t)))))

-- lw of the node at c (bindings b, top bt; scratch v, w): (b, (v, (vt, (end, (ok, w)))))
def u31 (x d b : Buf) (bt : UInt64) (v w : Buf) (c : UInt64) : Buf × (Buf × (UInt64 × (UInt64 × (UInt64 × Buf)))) :=
  if u63 v w == 1 then u28 16777216 x d b bt v 0 (u27 w 0 0 0 0) 1 c else (b, (v, (0, (c, (0, w)))))

-- isL of the node at c: (b, (r, (v, w))), r 1 yes, 0 no, 2 error
def u32 (x d b : Buf) (bt : UInt64) (v w : Buf) (c : UInt64) : Buf × (UInt64 × (Buf × Buf)) :=
  let (b1, z) := u31 x d b bt v w c;
  let (v1, z1) := z;
  let (vt, z2) := z1;
  let (e, z3) := z2;
  let (ok, w1) := z3;
  if ok == 1 then (b1, ((if vt == 1 then (if bget v1 0 == 1 then 1 else 0) else 0), (v1, w1))) else (b1, (2, (v1, w1)))

-- mixIte of the node at q: (b, (r, (v, w))), r 1 yes, 0 no, 2 error
def u70 (x d b : Buf) (bt : UInt64) (v w : Buf) (q : UInt64) : Buf × (UInt64 × (Buf × Buf)) :=
  if bget x q == 4 then
    (let tp := u15 x (u15 x (q + 2));
     let ep := u15 x tp;
     let (b1, z) := u32 x d b bt v w tp;
     let (lt, z1) := z;
     let (v1, w1) := z1;
     let (b2, z2) := u32 x d b1 bt v1 w1 ep;
     let (le, z3) := z2;
     let (v2, w2) := z3;
     let (w3, st) := u17 x w2 tp;
     let (w4, se) := u17 x w3 ep;
     let (w5, pe) := u72 x w4 ep;
     if ep == 0 then (b2, (2, (v2, w5)))
     else if lt == 2 then (b2, (2, (v2, w5)))
     else if le == 2 then (b2, (2, (v2, w5)))
     else if st == 2 then (b2, (2, (v2, w5)))
     else if se == 2 then (b2, (2, (v2, w5)))
     else if pe == 2 then (b2, (2, (v2, w5)))
     else (b2, ((lt &&& (se ||| pe)) ||| (le &&& st), (v2, w5))))
  else (b, (0, (v, w)))

-- shapeOk of the leaves p[j .. e) (l: an earlier leaf is literal-only): (b, (r, (v, w))), r 1 ok, 0 rejected or error
def u33 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → UInt64 → UInt64 → Buf → Buf → Buf × (UInt64 × (Buf × Buf))
  | 0, x, d, b, bt, p, j, e, l, v, w => (b, (0, (v, w)))
  | n + 1, x, d, b, bt, p, j, e, l, v, w =>
    if j < e then
      (let q := bget p j;
       let (w1, h) := u17 x w q;
       if h == 0 then
         (let (b0, z0) := u70 x d b bt v w1 q;
          let (mx, z9) := z0;
          let (v0, w0) := z9;
          if mx == 0 then
            (let (b1, z) := u32 x d b0 bt v0 w0 q;
             let (r, z1) := z;
             let (v1, w2) := z1;
             if r == 2 then (b1, (0, (v1, w2)))
             else if u34 x q == 1 then (if l == 1 then (b1, (0, (v1, w2))) else u33 n x d b1 bt p (j + 1) e (l ||| r) v1 w2)
             else u33 n x d b1 bt p (j + 1) e (l ||| r) v1 w2)
          else (b0, (0, (v0, w0))))
       else (b, (0, (v, w1))))
    else (b, (1, (v, w)))

-- push COLAT tasks for p[j - 1], …, p[0] (p[0] on top)
def u43 : Nat → Buf → UInt64 → Buf → UInt64 → Buf × (UInt64 × UInt64)
  | 0, t, tt, p, j => (t, (tt, 0))
  | n + 1, t, tt, p, j => if j == 0 then (t, (tt, 1)) else u43 n (u27 t tt 8 (bget p (j - 1)) 0) (tt + 1) p (j - 1)

-- COL d at the cursor, not literal-only: by tag (tt: the tasks below; y, y1, y2: scratch)
def u42 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb e : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let g := bget x c;
  if g == 3 then
    (if u34 x c == 1 then
      (let (b1, z) := u32 x d b bt y y1 (c + 2);
       let (r, z1) := z;
       let (y3, y4) := z1;
       if r == 0 then
         (let (y5, h) := u17 x y4 (c + 2);
          let (b2, z2) := u70 x d b1 bt y3 y5 (c + 2);
          let (ma, z3) := z2;
          let (y6, y7) := z3;
          let (b3, z4) := u70 x d b2 bt y6 y7 (u15 x (c + 2));
          let (mb, z5) := z4;
          let (y8, y9) := z5;
          if h == 0 then
            (if ma == 0 then
              (if mb == 0 then
                (if u15 x (c + 2) == 0 then u64 b3 t s y8 y9 y2
                 else u65 b3 bt (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) (c + 2) s st gb 1 y8 y9 y2)
               else u64 b3 t s y8 y9 y2)
             else u64 b3 t s y8 y9 y2)
          else u64 b3 t s y8 y9 y2)
       else u64 b1 t s y3 y4 y2)
     else
      (let (p, z) := u16 x y2 0 y1 c;
       let (pt, z1) := z;
       let (y4, ok) := z1;
       if ok == 1 then
         (let (b1, z2) := u33 16777216 x d b bt p 0 pt 0 y y4;
          let (h, z3) := z2;
          let (y3, y5) := z3;
          if h == 1 then
            (let (t1, z4) := u43 16777216 t tt p pt;
             let (tt1, ok1) := z4;
             u65 b1 bt t1 tt1 c s st gb ok1 y3 y5 p)
          else u64 b1 t s y3 y5 p)
       else u64 b t s y y4 p))
  else if g == 4 then
    (if e == 0 then
      (let (b1, z) := u70 x d b bt y y1 c;
       let (mx, z1) := z;
       let (y3, y4) := z1;
       if mx == 0 then u65 b1 bt (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0) (tt + 3) (c + 2) s st gb 1 y3 y4 y2
       else u64 b1 t s y3 y4 y2)
     else u65 b bt (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0) (tt + 3) (c + 2) s st gb 1 y y1 y2)
  else if g == 5 then
    (let l := bget x (c + 1);
     u65 b bt (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 0 e 0) (tt + 2) 6 l (c + 3)) (tt + 3) 3 l 0) (tt + 4) (c + 3) s st gb 1 y y1 y2)
  else if g == 6 then u65 b bt (u27 t tt 7 (bget x (c + 1)) 0) (tt + 1) (c + 2) s st gb 1 y y1 y2
  else if g == 8 then
    (let i := bget x (c + 1);
     let k := bget x (c + 2);
     if k == 0 then u65 b bt t tt (c + 3) s st gb 1 y y1 y2
     else u65 b bt (u27 (u27 t tt 7 (k - 1) 0) (tt + 1) 0 (if 2 * i < bsize d then (if bget d (2 * i) == 1 then 2 else 1) else 1) 0) (tt + 2) (c + 3) s st gb 1 y y1 y2)
  else if g == 9 then u65 b bt (u27 t tt 7 (g33 (bget x (c + 1))) 0) (tt + 1) (c + 2) s st gb 1 y y1 y2
  else if g == 10 then u65 b bt (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) (c + 1) s st gb 1 y y1 y2
  else if g == 11 then u65 b bt (u27 t tt 0 1 0) (tt + 1) (c + 1) s st gb 1 y y1 y2
  else if g == 1 then u65 b bt t tt (c + 2) s st gb 1 y y1 y2
  else if g == 2 then u65 b bt t tt (c + 3) s st gb 1 y y1 y2
  else u64 b t s y y1 y2

-- COL d at the cursor
def u41 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb e : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let (b1, z) := u32 x d b bt y y1 c;
  let (r, z1) := z;
  let (y3, y4) := z1;
  if r == 2 then u64 b1 t s y3 y4 y2
  else if r == 1 then
    u65 b1 bt (u27 (u27 t tt 4 e gb) (tt + 1) 1 0 0) (tt + 2) c (u20 s st 0) (st + 1) st 1 y3 y4 y2
  else u42 x d b1 bt t tt c s st gb e y3 y4 y2

-- LIT at the cursor
def u44 (x b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let g := bget x c;
  if g == 2 then u65 b bt t tt (c + 3) (u20 s st (bget x (c + 1))) (st + 1) gb 1 y y1 y2
  else if g == 3 then
    u65 b bt (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0) (tt + 2) (c + 2) (bset s gb 1) st gb 1 y y1 y2
  else if g == 4 then
    u65 b bt (u27 (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0) (tt + 2) 2 0 0) (tt + 3) (c + 2) s st gb 1 y y1 y2
  else if g == 5 then
    (let l := bget x (c + 1);
     u65 b bt (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 1 0 0) (tt + 2) 6 l (c + 3)) (tt + 3) 3 l 0) (tt + 4) (c + 3) s st gb 1 y y1 y2)
  else
    (let e := u15 x c;
     u65 b bt t tt e s st gb (if e == 0 then 0 else 1) y y1 y2)

-- CMP: the operands at the cursor
def u45 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let bp := u15 x c;
  if bp == 0 then u64 b t s y y1 y2
  else
    (let (p1, z) := u16 x y2 0 y1 c;
     let (pt1, z1) := z;
     let (y3, o1) := z1;
     let (p2, z2) := u16 x p1 pt1 y3 bp;
     let (pt2, z3) := z2;
     let (y4, o2) := z3;
     if o1 == 1 then
       (if o2 == 1 then
         (let (b1, z4) := u33 16777216 x d b bt p2 0 pt2 0 y y4;
          let (h, z5) := z4;
          let (y5, y6) := z5;
          if h == 1 then
            (let (b2, z6) := u32 x d b1 bt y5 y6 c;
             let (la, z7) := z6;
             let (y7, y8) := z7;
             let (b3, z8) := u32 x d b2 bt y7 y8 bp;
             let (lb, z9) := z8;
             let (y9, y10) := z9;
             if la == 2 then u64 b3 t s y9 y10 p2
             else if lb == 2 then u64 b3 t s y9 y10 p2
             else if (la &&& lb) == 1 then
               u65 b3 bt (u27 (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0) (tt + 2) 1 0 0) (tt + 3) c (u20 s st 0) (st + 1) st 1 y9 y10 p2
             else u65 b3 bt (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) c s st gb 1 y9 y10 p2)
          else u64 b1 t s y5 y6 p2)
        else u64 b t s y y4 p2)
     else u64 b t s y y4 p2)

-- the value at the cursor is bound to slot l: COL m on it, or LIT into a new group (t: tt tasks)
def u66 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb l m : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  let (b1, z) := u32 x d b bt y y1 c;
  let (r, z1) := z;
  let (y3, y4) := z1;
  if r == 2 then u64 b1 t s y3 y4 y2
  else if r == 1 then
    u65 b1 bt (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0) (tt + 2) c (u20 (u20 s st 0) (st + 1) l) (st + 2) st 1 y3 y4 y2
  else u65 b1 bt (u27 t tt 0 m 0) (tt + 1) c s st gb 1 y3 y4 y2

-- LETG slot l, the value at the cursor
def u46 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb l : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  if bget x c == 6 then u65 b bt (u27 t tt 9 l (bget x (c + 1))) (tt + 1) (c + 2) s st gb 1 y y1 y2
  else u66 x d b bt t tt c s st gb l 0 y y1 y2

-- LPSEQ: the next pair field (slot l, k fields left)
def u39 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb l k : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  if k == 0 then u65 b bt t tt c s st gb 1 y y1 y2
  else u66 x d b bt (u27 t tt 9 (l + 1) (k - 1)) (tt + 1) c s st gb l 0 y y1 y2

-- the tasks that read the tree
def u49 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb k a a2 : UInt64) (y y1 y2 : Buf) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × (UInt64 × (Buf × (Buf × Buf)))))))))) :=
  if k == 0 then u41 x d b bt t tt c s st gb a y y1 y2
  else if k == 1 then u44 x b bt t tt c s st gb y y1 y2
  else if k == 2 then u45 x d b bt t tt c s st gb y y1 y2
  else if k == 3 then u46 x d b bt t tt c s st gb a y y1 y2
  else if k == 9 then u39 x d b bt t tt c s st gb a a2 y y1 y2
  else u64 b t s y y1 y2

-- append s[j .. e) to g
def u47 : Nat → Buf → Buf → UInt64 → UInt64 → Buf × UInt64
  | 0, g, s, j, e => (g, 0)
  | n + 1, g, s, j, e => if j < e then u47 n (bpush g (bget s j)) s (j + 1) e else (g, 1)

-- the main machine: (groups, (cursor, (ok, (b, (t, (s, (y, (y1, y2))))))))
def u40 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → UInt64 → Buf → Buf → UInt64 → UInt64 → Buf → Buf → Buf →
    Buf × (UInt64 × (UInt64 × (Buf × (Buf × (Buf × (Buf × (Buf × Buf)))))))
  | 0, x, d, b, bt, t, tt, c, g, s, st, gb, y, y1, y2 => (g, (c, (0, (b, (t, (s, (y, (y1, y2))))))))
  | n + 1, x, d, b, bt, t, tt, c, g, s, st, gb, y, y1, y2 =>
    if tt == 0 then (g, (c, (1, (b, (t, (s, (y, (y1, y2))))))))
    else if u36 b t g s == 0 then (g, (c, (0, (b, (t, (s, (y, (y1, y2))))))))
    else
      let k := bget t (3 * tt - 3);
      let a := bget t (3 * tt - 2);
      let a2 := bget t (3 * tt - 1);
      let u := tt - 1;
      if k == 4 then
        (let (g1, ok) := u47 16777216 (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st;
         if ok == 1 then u40 n x d b bt t u c g1 s gb a2 y y1 y2 else (g1, (c, (0, (b, (t, (s, (y, (y1, y2)))))))))
      else if k == 5 then u40 n x d b a t u c g s st gb y y1 y2
      else if k == 6 then
        (let (b1, z) := u31 x d b bt y y1 a2;
         let (v, z1) := z;
         let (vt, z2) := z1;
         let (e, z3) := z2;
         let (ok, y3) := z3;
         if ok == 1 then
           (let (b2, z4) := u26 b1 bt v 0 vt a;
            let (bt1, ok1) := z4;
            if ok1 == 1 then u40 n x d b2 bt1 t u c g s st gb v y3 y2 else (g, (c, (0, (b2, (t, (s, (v, (y3, y2)))))))))
         else (g, (c, (0, (b1, (t, (s, (v, (y3, y2)))))))))
      else if k == 7 then
        (if a == 0 then u40 n x d b bt t u c g s st gb y y1 y2
         else u40 n x d b bt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 1 0) (tt + 1) c g s st gb y y1 y2)
      else if k == 8 then u40 n x d b bt (u27 t u 0 1 0) tt a g s st gb y y1 y2
      else
        (let (b1, z) := u49 x d b bt t u c s st gb k a a2 y y1 y2;
         let (bt1, z1) := z;
         let (t1, z2) := z1;
         let (tt1, z3) := z2;
         let (c1, z4) := z3;
         let (s1, z5) := z4;
         let (st1, z6) := z5;
         let (gb1, z7) := z6;
         let (ok, z8) := z7;
         let (y3, z9) := z8;
         let (y4, y5) := z9;
         if ok == 1 then u40 n x d b1 bt1 t1 tt1 c1 g s1 st1 gb1 y3 y4 y5 else (g, (c1, (0, (b1, (t1, (s1, (y3, (y4, y5)))))))))

-- every slot g[j .. e) is below n
def u52 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64
  | 0, g, j, e, n => 0
  | m + 1, g, j, e, n => if j < e then (if bget g j < n then u52 m g (j + 1) e n else 0) else 1

-- every slot of the groups from j is below n
def u51 : Nat → Buf → UInt64 → UInt64 → UInt64
  | 0, g, j, n => 0
  | m + 1, g, j, n =>
    if j < bsize g then
      (let l := bget g j;
       if u52 16777216 g (j + 3) (j + 3 + l) n == 1 then u51 m g (j + 3 + l) n else 0)
    else 1

-- some slot g[j .. e) was marked before round k (0 < f[v] < k): 1, none 0, error 2
def u53 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64
  | 0, f, g, j, e, k => 2
  | m + 1, f, g, j, e, k =>
    if j < e then
      (let w := bget f (bget g j);
       if w == 0 then u53 m f g (j + 1) e k
       else if w < k then 1
       else u53 m f g (j + 1) e k)
    else 0

-- mark the unmarked slots g[j .. e) with round k
def u54 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, f, g, j, e, k => (f, 0)
  | m + 1, f, g, j, e, k =>
    if j < e then
      (let v := bget g j;
       if bget f v == 0 then u54 m (bset f v k) g (j + 1) e k else u54 m f g (j + 1) e k)
    else (f, 1)

-- round k of `marked q`: the groups from j
def u55 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, f, g, j, q, k => (f, 0)
  | m + 1, f, g, j, q, k =>
    if j < bsize g then
      (let l := bget g j;
       let h := (if bget g (j + 1) == q then 1 else u53 16777216 f g (j + 3) (j + 3 + l) k);
       if h == 2 then (f, 0)
       else if h == 1 then
         (let (f1, ok) := u54 16777216 f g (j + 3) (j + 3 + l) k;
          if ok == 1 then u55 m f1 g (j + 3 + l) q k else (f1, 0))
       else u55 m f g (j + 3 + l) q k)
    else (f, 1)

-- rounds k .. r of `marked q` (the groups from g0)
def u56 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, f, g, g0, q, k, r => (f, 0)
  | m + 1, f, g, g0, q, k, r =>
    if r < k then (f, 1)
    else
      (let (f1, ok) := u55 16777216 f g g0 q k;
       if ok == 1 then u56 m f1 g g0 q (k + 1) r else (f1, 0))

-- zero words j .. k
def u57 : Nat → Buf → UInt64 → UInt64 → Buf × UInt64
  | 0, b, j, k => (b, 0)
  | m + 1, b, j, k => if j < k then u57 m (u20 b j 0) (j + 1) k else (b, 1)

-- some slot g[j .. e) is marked: 1, none 0, error 2
def u59 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64
  | 0, f, g, j, e => 2
  | m + 1, f, g, j, e => if j < e then (if bget f (bget g j) == 0 then u59 m f g (j + 1) e else 1) else 0

-- every group from j: not both UInt64 and Nat, no arithmetic unless UInt64
def u58 : Nat → Buf → Buf → Buf → UInt64 → UInt64
  | 0, f, h, g, j => 0
  | m + 1, f, h, g, j =>
    if j < bsize g then
      (let l := bget g j;
       let q := bget g (j + 1);
       let r := bget g (j + 2);
       let a := (if q == 1 then 1 else u59 16777216 f g (j + 3) (j + 3 + l));
       let o := (if q == 2 then 1 else u59 16777216 h g (j + 3) (j + 3 + l));
       if a == 2 then 0
       else if o == 2 then 0
       else if a == 1 then (if o == 1 then 0 else u58 m f h g (j + 3 + l))
       else if r == 1 then 0
       else u58 m f h g (j + 3 + l))
    else 1

-- the class check of the groups g from g0 (n slots; f, h: scratch): (ok, (f, h))
def u50 (g : Buf) (g0 n : UInt64) (f h : Buf) : UInt64 × (Buf × Buf) :=
  if n < 16777215 then
    (if u51 16777216 g g0 n == 1 then
      (let (z1, k1) := u57 16777216 f 0 n;
       let (f1, k2) := u56 16777216 z1 g g0 1 1 (n + 1);
       let (z2, k3) := u57 16777216 h 0 n;
       let (h1, k4) := u56 16777216 z2 g g0 2 1 (n + 1);
       if (k1 &&& k2 &&& k3 &&& k4) == 1 then (u58 16777216 f1 h1 g g0, (f1, h1)) else (0, (f1, h1)))
     else (0, (f, h)))
  else (0, (f, h))

-- one def: the body at i, n slots (b, t, g, s, y, y1, y2: the buffers): (end, (g, (b, (t, (s, (y2, (ok, (y, y1))))))))
def u48 (x d : Buf) (i n : UInt64) (b t g s y y1 y2 : Buf) :
    UInt64 × (Buf × (Buf × (Buf × (Buf × (Buf × (UInt64 × (Buf × Buf))))))) :=
  let g0 := bsize g;
  let (g1, z) := u40 16777216 x d b 0 (u27 t 0 0 1 0) 1 i g s 0 0 y y1 y2;
  let (e, z1) := z;
  let (ok, z2) := z1;
  let (b1, z3) := z2;
  let (t1, z4) := z3;
  let (s1, z5) := z4;
  let (y3, z6) := z5;
  let (y4, y5) := z6;
  if ok == 1 then (e, (g1, (b1, (t1, (s1, (y5, u50 g1 g0 n y3 y4))))))
  else (e, (g1, (b1, (t1, (s1, (y5, (0, (y3, y4))))))))

-- the def table: (kind, nres) per def
def u60 : Nat → Buf → Buf → UInt64 → Buf × UInt64
  | 0, x, d, i => (d, 0)
  | n + 1, x, d, i =>
    if i < bsize x then
      (if bget x i == 20 then
        (let e := u15 x (i + 6);
         if e == 0 then (d, 0)
         else if bget x e == 21 then u60 n x (bpush (bpush d (bget x (i + 4))) (bget x (i + 5))) (e + 1)
         else (d, 0))
       else (d, 0))
    else (d, 1)

-- the next position and pending count after the node at i (k pending nodes, it included)
def u77 (x : Buf) (i k : UInt64) : UInt64 × UInt64 :=
  let t := bget x i;
  if t == 1 then (i + 2, k - 1)
  else if t == 2 then (i + 3, k - 1)
  else if t == 3 then (i + 2, k + 1)
  else if t == 4 then (i + 2, k + 3)
  else if t == 5 then (i + 3, k + 1)
  else if t == 6 then (i + 2, k - 1 + bget x (i + 1))
  else if t == 8 then (i + 3, k - 1 + bget x (i + 2))
  else if t == 9 then (i + 2, k - 1 + g33 (bget x (i + 1)))
  else if t == 10 then (i + 1, k + 1)
  else if t == 11 then (i + 1, k)
  else (i, 0)

-- mark f[s + j .. s + k): (f, ok), ok 0 past the end of f
def u78 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, f, s, j, k => (f, 0)
  | n + 1, f, s, j, k =>
    if j < k then (if s + j < bsize f then u78 n (bset f (s + j) 1) s (j + 1) k else (f, 0)) else (f, 1)

-- mark slot s + j of each tuple field (from q, fields j .. k) with a let on its result spine: (f, (w, ok))
def u76 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × (Buf × UInt64)
  | 0, x, f, w, q, s, j, k => (f, (w, 0))
  | n + 1, x, f, w, q, s, j, k =>
    if j < k then
      (let (w1, h) := u17 x w q;
       let e := u15 x q;
       if h == 2 then (f, (w1, 0))
       else if e == 0 then (f, (w1, 0))
       else if h == 1 then
         (let (f1, ok) := u78 16777216 f s j (j + 1);
          if ok == 1 then u76 n x f1 w1 e s (j + 1) k else (f1, (w1, 0)))
       else u76 n x f w1 e s (j + 1) k)
    else (f, (w, 1))

-- mark the late slots of `let s (width wd) := the value at q`: (f, (w, ok))
def u75 (x f w : Buf) (q s wd : UInt64) : Buf × (Buf × UInt64) :=
  if bget x q == 6 then u76 16777216 x f w (q + 2) s 0 (bget x (q + 1))
  else
    (let (w1, h) := u17 x w q;
     if h == 2 then (f, (w1, 0))
     else if h == 1 then (let (f1, ok) := u78 16777216 f s 0 wd; (f1, (w1, ok)))
     else (f, (w1, 1)))

-- mark the late slots of the lets among the k nodes from i: (f, (w, ok))
def u73 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → Buf × (Buf × UInt64)
  | 0, x, f, w, i, k => (f, (w, 0))
  | n + 1, x, f, w, i, k =>
    if k == 0 then (f, (w, 1))
    else
      (let (f1, z) := (if bget x i == 5 then u75 x f w (i + 3) (bget x (i + 1)) (bget x (i + 2)) else (f, (w, 1)));
       let (w1, ok) := z;
       let (i1, k1) := u77 x i k;
       if ok == 1 then u73 n x f1 w1 i1 k1 else (f1, (w1, 0)))

-- no shift among the k nodes from i has a marked slot as its left operand (1)
def u74 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64
  | 0, x, f, i, k => 0
  | n + 1, x, f, i, k =>
    if k == 0 then 1
    else
      (let (i1, k1) := u77 x i k;
       if u34 x i == 1 then
         (if bget x (i + 2) == 2 then (if bget f (bget x (i + 3)) == 0 then u74 n x f i1 k1 else 0)
          else u74 n x f i1 k1)
       else u74 n x f i1 k1)

-- the late-slot check of the def at i (1): clear y2's slot marks, mark the late slots, check the shifts
def u79 (x y1 y2 : Buf) (i : UInt64) : Buf × (Buf × UInt64) :=
  let (f0, k0) := u57 16777216 y2 0 (bget x (i + 3));
  if k0 == 1 then
    (let (f1, z0) := u73 16777216 x f0 y1 (i + 6) 1;
     let (w1, k1) := z0;
     if k1 == 1 then (let k := u74 16777216 x f1 (i + 6) 1; (f1, (w1, k))) else (f1, (w1, 0)))
  else (f0, (y1, 0))

-- every def from i (b, t, g, s, y, y1, y2: the buffers, allocated once)
def u61 : Nat → Buf → Buf → UInt64 → Buf → Buf → Buf → Buf → Buf → Buf → Buf → UInt64
  | 0, x, d, i, b, t, g, s, y, y1, y2 => 0
  | n + 1, x, d, i, b, t, g, s, y, y1, y2 =>
    if i < bsize x then
      (let (f1, z0) := u79 x y1 y2 i;
       let (w1, k1) := z0;
       if k1 == 1 then
         (let (e, z) := u48 x d (i + 6) (bget x (i + 3)) b t g s y w1 f1;
          let (g1, z1) := z;
          let (b1, z2) := z1;
          let (t1, z3) := z2;
          let (s1, z4) := z3;
          let (y5, z5) := z4;
          let (ok, z6) := z5;
          let (y3, y4) := z6;
          if ok == 1 then (if bget x e == 21 then u61 n x d (e + 1) b1 t1 g1 s1 y3 y4 y5 else 0) else 0)
       else 0)
    else 1

-- 1: every def's numerals mean what Lean's mean
def u11 (x : Buf) : UInt64 :=
  if bget x 0 == 2 then
    (if bsize x < 8388608 then
      (let (d, ok) := u60 16777216 x bnew 1;
       if ok == 1 then u61 16777216 x d 1 bnew bnew bnew bnew bnew bnew bnew else 0)
     else 0)
  else 0

/-- **the numeral check**: the AST back if every def passes `NumSpec.numOkD`, else empty -/
def u10 (x : Buf) : Buf := if u11 x == 1 then x else bnew

end C

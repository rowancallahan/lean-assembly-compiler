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

-- leaves: the operands of the operator trees on the work stack w (top t), appended to p; (p, 1) or (p, 0) on error
def u13 : Nat → Buf → Buf → Buf → UInt64 → Buf × UInt64
  | 0, x, p, w, t => (p, 0)
  | n + 1, x, p, w, t =>
    if t == 0 then (p, 1)
    else
      let q := bget w (t - 1);
      if bget x q == 3 then
        (if u34 x q == 1 then u13 n x (bpush p q) w (t - 1)
         else
           (let e := u15 x (q + 2);
            if e == 0 then (p, 0)
            else u13 n x p (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1)))
      else u13 n x (bpush p q) w (t - 1)

-- the leaves of the node at i, appended to p
def u16 (x p : Buf) (i : UInt64) : Buf × UInt64 := u13 16777216 x p (bpush bnew i) 1

-- spineLet of the nodes on the work stack: 1 some, 0 none, 2 error
def u14 : Nat → Buf → Buf → UInt64 → UInt64
  | 0, x, w, t => 2
  | n + 1, x, w, t =>
    if t == 0 then 0
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 5 then 1
      else if g == 4 then
        (let b := u15 x (u15 x (q + 2));
         let e := u15 x b;
         if e == 0 then 2 else u14 n x (u20 (u20 w (t - 1) e) t b) (t + 1))
      else u14 n x w (t - 1)

-- spineLet of the node at i
def u17 (x : Buf) (i : UInt64) : UInt64 := u14 16777216 x (bpush bnew i) 1

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

-- lw: the NODE task at the cursor c (tt: the tasks below it)
def u29 (x d b : Buf) (bt : UInt64) (v : Buf) (vt : UInt64) (t : Buf) (tt c : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64)))) :=
  let g := bget x c;
  if g == 1 then (u20 v vt 1, (vt + 1, (t, (tt, (c + 2, 1)))))
  else if g == 2 then
    (let (v1, z) := u22 16777216 b bt v vt (bget x (c + 1)) (bget x (c + 2));
     let (vt1, ok) := z;
     (v1, (vt1, (t, (tt, (c + 3, ok))))))
  else if g == 3 then
    (if u34 x c == 1 then
      (let e := u15 x c;
       (u20 v vt 0, (vt + 1, (t, (tt, (e, (if e == 0 then 0 else 1)))))))
     else (v, (vt, (u27 (u27 (u27 (u27 (u27 t tt 2 vt 0) (tt + 1) 1 (vt + 1) 0) (tt + 2) 0 0 0) (tt + 3) 1 vt 0) (tt + 4) 0 0 0,
       (tt + 5, (c + 2, 1))))))
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
  else if g == 9 then
    (let e := u15 x c;
     (u20 v vt 0, (vt + 1, (t, (tt, (e, (if e == 0 then 0 else 1)))))))
  else if g == 10 then
    (let e := u15 x c;
     (u20 v vt 0, (vt + 1, (t, (tt, (e, (if e == 0 then 0 else 1)))))))
  else if g == 11 then
    (let e := u15 x c;
     (u20 v vt 0, (vt + 1, (t, (tt, (e, (if e == 0 then 0 else 1)))))))
  else (v, (vt, (t, (tt, (c, 0)))))

-- the lw machine: (b, (v, (vt, (cursor, ok))))
def u28 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → Buf → UInt64 → UInt64 →
    Buf × (Buf × (UInt64 × (UInt64 × UInt64)))
  | 0, x, d, b, bt, v, vt, t, tt, c => (b, (v, (vt, (c, 0))))
  | n + 1, x, d, b, bt, v, vt, t, tt, c =>
    if tt == 0 then (b, (v, (vt, (c, 1))))
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
         if ok == 1 then u28 n x d b bt v1 vt1 t1 tt1 c1 else (b, (v1, (vt1, (c1, 0)))))
      else if k == 1 then u28 n x d b bt (u20 v a (if a < vt then bget v a else 0)) (a + 1) t u c
      else if k == 2 then u28 n x d b bt (bset v a (bget v a &&& bget v (a + 1))) (a + 1) t u c
      else if k == 3 then u28 n x d b bt (bset v a (vt - a - 1)) vt t u c
      else if k == 4 then
        (let l := bget v a;
         let m := a + 1 + l;
         let e := vt - m;
         let q := (if l < e then l else e);
         let (v1, ok) := u24 16777216 v a m 0 q;
         if ok == 1 then u28 n x d b bt v1 (a + q) t u c else (b, (v1, (vt, (c, 0)))))
      else if k == 5 then
        (let (b1, z) := u26 b bt v a2 vt a;
         let (bt1, ok) := z;
         if ok == 1 then u28 n x d b1 bt1 v a2 t u c else (b1, (v, (vt, (c, 0)))))
      else if k == 6 then u28 n x d b a v vt t u c
      else if k == 7 then
        (if a == 0 then u28 n x d b bt v vt t u c
         else u28 n x d b bt v vt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 0 0) (tt + 1) c)
      else (b, (v, (vt, (c, 0))))

-- lw of the node at c (bindings b, top bt): (b, (v, (vt, (end, ok))))
def u31 (x d b : Buf) (bt c : UInt64) : Buf × (Buf × (UInt64 × (UInt64 × UInt64))) :=
  u28 16777216 x d b bt bnew 0 (u27 bnew 0 0 0 0) 1 c

-- isL of the node at c: 1 yes, 0 no, 2 error
def u32 (x d b : Buf) (bt c : UInt64) : Buf × UInt64 :=
  let (b1, z) := u31 x d b bt c;
  let (v, z1) := z;
  let (vt, z2) := z1;
  let (e, ok) := z2;
  if ok == 1 then (b1, (if vt == 1 then (if bget v 0 == 1 then 1 else 0) else 0)) else (b1, 2)

-- shapeOk of the leaves p[j .. e) (l: an earlier leaf is literal-only): 1 ok, 0 rejected or error
def u33 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, x, d, b, bt, p, j, e, l => (b, 0)
  | n + 1, x, d, b, bt, p, j, e, l =>
    if j < e then
      (let q := bget p j;
       if u17 x q == 0 then
         (let (b1, r) := u32 x d b bt q;
          if r == 2 then (b1, 0)
          else if u34 x q == 1 then (if l == 1 then (b1, 0) else u33 n x d b1 bt p (j + 1) e (l ||| r))
          else u33 n x d b1 bt p (j + 1) e (l ||| r))
       else (b, 0))
    else (b, 1)

-- push COLAT tasks for p[j - 1], …, p[0] (p[0] on top)
def u43 : Nat → Buf → UInt64 → Buf → UInt64 → Buf × (UInt64 × UInt64)
  | 0, t, tt, p, j => (t, (tt, 0))
  | n + 1, t, tt, p, j => if j == 0 then (t, (tt, 1)) else u43 n (u27 t tt 8 (bget p (j - 1)) 0) (tt + 1) p (j - 1)

-- COL d at the cursor, not literal-only: by tag (tt: the tasks below)
def u42 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb e : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  let g := bget x c;
  if g == 3 then
    (if u34 x c == 1 then
      (let (b1, r) := u32 x d b bt (c + 2);
       if r == 0 then
         (if u17 x (c + 2) == 0 then
           (b1, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c + 2, (s, (st, (gb, 1))))))))
          else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
       else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
     else
      (let (p, ok) := u16 x bnew c;
       if ok == 1 then
         (let (b1, h) := u33 16777216 x d b bt p 0 (bsize p) 0;
          if h == 1 then
            (let (t1, z) := u43 16777216 t tt p (bsize p);
             let (tt1, ok1) := z;
             (b1, (bt, (t1, (tt1, (c, (s, (st, (gb, ok1)))))))))
          else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
       else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))))
  else if g == 4 then
    (let tp := u15 x (u15 x (c + 2));
     let ep := u15 x tp;
     if ep == 0 then (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
     else
       (let (b1, lt) := u32 x d b bt tp;
        let (b2, le) := u32 x d b1 bt ep;
        let pt := u17 x tp;
        let pe := u17 x ep;
        if lt == 2 then (b2, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
        else if le == 2 then (b2, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
        else if pt == 2 then (b2, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
        else if pe == 2 then (b2, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
        else if e == 0 then
          (if ((lt &&& pe) ||| (le &&& pt)) == 1 then (b2, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
           else (b2, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, 1)))))))))
        else (b2, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, 1))))))))))
  else if g == 5 then
    (let l := bget x (c + 1);
     (b, (bt, (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 0 e 0) (tt + 2) 6 l (c + 3)) (tt + 3) 3 l 0,
       (tt + 4, (c + 3, (s, (st, (gb, 1)))))))))
  else if g == 6 then (b, (bt, (u27 t tt 7 (bget x (c + 1)) 0, (tt + 1, (c + 2, (s, (st, (gb, 1))))))))
  else if g == 8 then
    (let i := bget x (c + 1);
     let k := bget x (c + 2);
     if k == 0 then (b, (bt, (t, (tt, (c + 3, (s, (st, (gb, 1))))))))
     else (b, (bt, (u27 (u27 t tt 7 (k - 1) 0) (tt + 1) 0 (if 2 * i < bsize d then (if bget d (2 * i) == 1 then 2 else 1) else 1) 0,
       (tt + 2, (c + 3, (s, (st, (gb, 1)))))))))
  else if g == 9 then (b, (bt, (u27 t tt 7 (g33 (bget x (c + 1))) 0, (tt + 1, (c + 2, (s, (st, (gb, 1))))))))
  else if g == 10 then (b, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c + 1, (s, (st, (gb, 1))))))))
  else if g == 11 then (b, (bt, (u27 t tt 0 1 0, (tt + 1, (c + 1, (s, (st, (gb, 1))))))))
  else if g == 1 then (b, (bt, (t, (tt, (c + 2, (s, (st, (gb, 1))))))))
  else if g == 2 then (b, (bt, (t, (tt, (c + 3, (s, (st, (gb, 1))))))))
  else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))

-- COL d at the cursor
def u41 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb e : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  let (b1, r) := u32 x d b bt c;
  if r == 2 then (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
  else if r == 1 then (b1, (bt, (u27 (u27 t tt 4 e gb) (tt + 1) 1 0 0, (tt + 2, (c, (u20 s st 0, (st + 1, (st, 1))))))))
  else u42 x d b1 bt t tt c s st gb e

-- LIT at the cursor
def u44 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  let g := bget x c;
  if g == 2 then (b, (bt, (t, (tt, (c + 3, (u20 s st (bget x (c + 1)), (st + 1, (gb, 1))))))))
  else if g == 3 then (b, (bt, (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0, (tt + 2, (c + 2, (bset s gb 1, (st, (gb, 1))))))))
  else if g == 4 then
    (b, (bt, (u27 (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, 1))))))))
  else if g == 5 then
    (let l := bget x (c + 1);
     (b, (bt, (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 1 0 0) (tt + 2) 6 l (c + 3)) (tt + 3) 3 l 0,
       (tt + 4, (c + 3, (s, (st, (gb, 1)))))))))
  else
    (let e := u15 x c;
     (b, (bt, (t, (tt, (e, (s, (st, (gb, (if e == 0 then 0 else 1))))))))))

-- CMP: the operands at the cursor
def u45 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  let bp := u15 x c;
  if bp == 0 then (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
  else
    (let (p1, o1) := u16 x bnew c;
     let (p2, o2) := u16 x p1 bp;
     if o1 == 1 then
       (if o2 == 1 then
         (let (b1, h) := u33 16777216 x d b bt p2 0 (bsize p2) 0;
          if h == 1 then
            (let (b2, la) := u32 x d b1 bt c;
             let (b3, lb) := u32 x d b2 bt bp;
             if la == 2 then (b3, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
             else if lb == 2 then (b3, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
             else if (la &&& lb) == 1 then
               (b3, (bt, (u27 (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0) (tt + 2) 1 0 0, (tt + 3, (c, (u20 s st 0, (st + 1, (st, 1))))))))
             else (b3, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c, (s, (st, (gb, 1)))))))))
          else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
        else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
     else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))

-- LETG slot l, the value at the cursor
def u46 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb l : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  if bget x c == 6 then (b, (bt, (u27 t tt 9 l (bget x (c + 1)), (tt + 1, (c + 2, (s, (st, (gb, 1))))))))
  else
    (let (b1, r) := u32 x d b bt c;
     if r == 2 then (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
     else if r == 1 then
       (b1, (bt, (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0, (tt + 2, (c, (u20 (u20 s st 0) (st + 1) l, (st + 2, (st, 1))))))))
     else (b1, (bt, (u27 t tt 0 0 0, (tt + 1, (c, (s, (st, (gb, 1)))))))))

-- LPSEQ: the next pair field (slot l, k fields left)
def u39 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb l k : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  if k == 0 then (b, (bt, (t, (tt, (c, (s, (st, (gb, 1))))))))
  else
    (let t1 := u27 t tt 9 (l + 1) (k - 1);
     let (b1, r) := u32 x d b bt c;
     if r == 2 then (b1, (bt, (t1, (tt + 1, (c, (s, (st, (gb, 0))))))))
     else if r == 1 then
       (b1, (bt, (u27 (u27 t1 (tt + 1) 4 0 gb) (tt + 2) 1 0 0, (tt + 3, (c, (u20 (u20 s st 0) (st + 1) l, (st + 2, (st, 1))))))))
     else (b1, (bt, (u27 t1 (tt + 1) 0 1 0, (tt + 2, (c, (s, (st, (gb, 1)))))))))

-- the tasks that read the tree
def u49 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb k a a2 : UInt64) :
    Buf × (UInt64 × (Buf × (UInt64 × (UInt64 × (Buf × (UInt64 × (UInt64 × UInt64))))))) :=
  if k == 0 then u41 x d b bt t tt c s st gb a
  else if k == 1 then u44 x d b bt t tt c s st gb
  else if k == 2 then u45 x d b bt t tt c s st gb
  else if k == 3 then u46 x d b bt t tt c s st gb a
  else if k == 9 then u39 x d b bt t tt c s st gb a a2
  else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))

-- append s[j .. e) to g
def u47 : Nat → Buf → Buf → UInt64 → UInt64 → Buf × UInt64
  | 0, g, s, j, e => (g, 0)
  | n + 1, g, s, j, e => if j < e then u47 n (bpush g (bget s j)) s (j + 1) e else (g, 1)

-- the main machine: (groups, (cursor, ok))
def u40 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → UInt64 → Buf → Buf → UInt64 → UInt64 →
    Buf × (UInt64 × UInt64)
  | 0, x, d, b, bt, t, tt, c, g, s, st, gb => (g, (c, 0))
  | n + 1, x, d, b, bt, t, tt, c, g, s, st, gb =>
    if tt == 0 then (g, (c, 1))
    else
      let k := bget t (3 * tt - 3);
      let a := bget t (3 * tt - 2);
      let a2 := bget t (3 * tt - 1);
      let u := tt - 1;
      if k == 4 then
        (let (g1, ok) := u47 16777216 (bpush (bpush (bpush g (st - gb - 1)) a) (bget s gb)) s (gb + 1) st;
         if ok == 1 then u40 n x d b bt t u c g1 s gb a2 else (g1, (c, 0)))
      else if k == 5 then u40 n x d b a t u c g s st gb
      else if k == 6 then
        (let (b1, z) := u31 x d b bt a2;
         let (v, z1) := z;
         let (vt, z2) := z1;
         let (e, ok) := z2;
         if ok == 1 then
           (let (b2, z3) := u26 b1 bt v 0 vt a;
            let (bt1, ok1) := z3;
            if ok1 == 1 then u40 n x d b2 bt1 t u c g s st gb else (g, (c, 0)))
         else (g, (c, 0)))
      else if k == 7 then
        (if a == 0 then u40 n x d b bt t u c g s st gb
         else u40 n x d b bt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 1 0) (tt + 1) c g s st gb)
      else if k == 8 then u40 n x d b bt (u27 t u 0 1 0) tt a g s st gb
      else
        (let (b1, z) := u49 x d b bt t u c s st gb k a a2;
         let (bt1, z1) := z;
         let (t1, z2) := z1;
         let (tt1, z3) := z2;
         let (c1, z4) := z3;
         let (s1, z5) := z4;
         let (st1, z6) := z5;
         let (gb1, ok) := z6;
         if ok == 1 then u40 n x d b1 bt1 t1 tt1 c1 g s1 st1 gb1 else (g, (c1, 0)))

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

-- rounds k .. r of `marked q`
def u56 : Nat → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, f, g, q, k, r => (f, 0)
  | m + 1, f, g, q, k, r =>
    if r < k then (f, 1)
    else
      (let (f1, ok) := u55 16777216 f g 0 q k;
       if ok == 1 then u56 m f1 g q (k + 1) r else (f1, 0))

-- k zero words
def u57 : Nat → Buf → UInt64 → Buf × UInt64
  | 0, b, k => (b, 0)
  | m + 1, b, k => if bsize b < k then u57 m (bpush b 0) k else (b, 1)

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

-- the class check of the groups g (n slots)
def u50 (g : Buf) (n : UInt64) : UInt64 :=
  if n < 16777215 then
    (if u51 16777216 g 0 n == 1 then
      (let (z1, k1) := u57 16777216 bnew n;
       let (f, k2) := u56 16777216 z1 g 1 1 (n + 1);
       let (z2, k3) := u57 16777216 bnew n;
       let (h, k4) := u56 16777216 z2 g 2 1 (n + 1);
       if (k1 &&& k2 &&& k3 &&& k4) == 1 then u58 16777216 f h g 0 else 0)
     else 0)
  else 0

-- one def: the body at i, n slots: (end, ok)
def u48 (x d : Buf) (i n : UInt64) : UInt64 × UInt64 :=
  let (g, z) := u40 16777216 x d bnew 0 (u27 bnew 0 0 1 0) 1 i bnew bnew 0 0;
  let (e, ok) := z;
  if ok == 1 then (e, u50 g n) else (e, 0)

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

-- every def from i
def u61 : Nat → Buf → Buf → UInt64 → UInt64
  | 0, x, d, i => 0
  | n + 1, x, d, i =>
    if i < bsize x then
      (let (e, ok) := u48 x d (i + 6) (bget x (i + 3));
       if ok == 1 then (if bget x e == 21 then u61 n x d (e + 1) else 0) else 0)
    else 1

-- 1: every def's numerals mean what Lean's mean
def u11 (x : Buf) : UInt64 :=
  if bget x 0 == 2 then
    (if bsize x < 8388608 then
      (let (d, ok) := u60 16777216 x bnew 1;
       if ok == 1 then u61 16777216 x d 1 else 0)
     else 0)
  else 0

/-- **the numeral check**: the AST back if every def passes `NumSpec.numOkD`, else empty -/
def u10 (x : Buf) : Buf := if u11 x == 1 then x else bnew

end C

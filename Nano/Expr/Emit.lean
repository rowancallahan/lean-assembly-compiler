/- Nano/Expr/Emit: the Expr emitter E in nano's bootstrap subset (Testing/notes/EXPR.md §4). Same output as the
reference `ExprSpec.emitProg`: one `D name type value` line per def. E = C's lexer + parser text + this text; its
driver `m x = e99 x`. Written as Lean defs (the S text, as Nano/Lexer/Lex2.lean); the phrase table is EmitStr.
Buffers: `t` tokens (s10), `r` IR (y16 = serialize p), `h` shapes, `f` def table, `g` param codes, `a` per IR word
(end, inferred shape, side flag), `l` (globals 0..7, then per slot: shape, used, level), `s` stack (`q` its size).
Shapes: 0 none, 1 UInt64, 2 Buf, 3 List UInt8, 4 Nat, k ≥ 5 a pair (h[1 + 3(k-5)] = left, right, width).
Parameter codes: 2 * shape + 1 for the input. Work items (4 words): 1 phrase, 2 type, 3 node (p, exp, depth),
4 bvar, 5 nat literal, 6 node with leading unused `have`s dropped, 7 identifier at a token position. -/
import Nano.Lexer.Lex2
import Nano.Parser.Par1
import Nano.Parser.NumC
import Nano.Expr.EmitStr
set_option linter.unusedVariables false
namespace C

def e0 (b : Buf) (j v : UInt64) : Buf := if j < bsize b then bset b j v else bpush b v

/-! ## printing -/
def e1 : Nat → List UInt8 → List UInt8 → UInt64 → List UInt8
  | 0, x, o, w => o
  | n + 1, x, o, w => if w == 0 then o else e1 n x (put o (w &&& 255)) (w >>> 8)

/-- phrase `i` from word `j` on -/
def e2 : Nat → List UInt8 → List UInt8 → UInt64 → UInt64 → List UInt8
  | 0, x, o, i, j => o
  | n + 1, x, o, i, j =>
    let w := ew i j;
    if (w >>> 56) == 0 then e1 9 x o w else e2 n x (e1 9 x o w) i (j + 1)

def e3 : Nat → UInt64 → UInt64 → UInt64
  | 0, i, a => a
  | n + 1, i, a => if i == 0 then a else e3 n (i - 1) (a * 10)

/-- (k / p, k % p) for k < 10 p -/
def e4 : Nat → UInt64 → UInt64 → UInt64 → UInt64 × UInt64
  | 0, k, p, c => (c, k)
  | n + 1, k, p, c => if k < p then (c, k) else e4 n (k - p) p (c + 1)

/-- decimal digits of k from 10^i down; z: a digit was printed -/
def e5 : Nat → List UInt8 → List UInt8 → UInt64 → UInt64 → UInt64 → List UInt8
  | 0, x, o, k, i, z => o
  | n + 1, x, o, k, i, z =>
    let (c, u) := e4 16 k (e3 20 i 1) 0;
    let o1 := (if c == 0 then (if z == 0 then (if i == 0 then put o 48 else o) else put o 48) else put o (48 + c));
    if i == 0 then o1 else e5 n x o1 u (i - 1) (z ||| c)

def e6 (x : List UInt8) (o : List UInt8) (k : UInt64) : List UInt8 := e5 21 x o k 19 0

/-- the identifier bytes of the token at p (tag 14, then (1, byte)*, 0) -/
def e7 : Nat → List UInt8 → List UInt8 → Buf → UInt64 → List UInt8
  | 0, x, o, t, p => o
  | n + 1, x, o, t, p => if bget t p == 1 then e7 n x (put o (bget t (p + 1))) t (p + 2) else o

/-- phrases written as ` !<id>` (S-compact, Testing/nano/expr/expand.py; the output stays under the 2^19-byte capacity) -/
def e56 (i : UInt64) : UInt64 :=
  if 47 < i then 1 else if i == 9 then 1 else if i == 11 then 1 else if i == 41 then 1 else if 11 < i then (if i < 32 then 1 else 0) else 0

def e57 (x : List UInt8) (o : List UInt8) (i : UInt64) : List UInt8 :=
  if e56 i == 1 then e6 x (e2 4 x o 47 0) i else e2 32 x o i 0

/-! ## tokens -/
def e8 : Nat → Buf → UInt64 → UInt64
  | 0, t, p => p
  | n + 1, t, p => if bget t p == 0 then p + 1 else e8 n t (p + 2)

/-- the position after the token at p -/
def e9 (t : Buf) (p : UInt64) : UInt64 :=
  if bget t p == 5 then p + 9 else if bget t p == 14 then e8 16777216 t (p + 1) else p + 1

/-- the next `let` token from p (tag 2) -/
def e10 : Nat → Buf → UInt64 → UInt64
  | 0, t, p => p
  | n + 1, t, p => if bget t p == 2 then p else e10 n t (e9 t p)

/-- the next `[]` (30) or `bnew` (43) token from p -/
def e11 : Nat → Buf → UInt64 → UInt64
  | 0, t, p => p
  | n + 1, t, p => if bget t p == 30 then p else if bget t p == 43 then p else e11 n t (e9 t p)

/-! ## shapes -/
def e12 (h : Buf) (k : UInt64) : UInt64 := if k < 5 then 1 else bget h (3 * (k - 5) + 3)
def e13 (h : Buf) (k : UInt64) : UInt64 := bget h (3 * (k - 5) + 1)
def e14 (h : Buf) (k : UInt64) : UInt64 := bget h (3 * (k - 5) + 2)
def e15 (h : Buf) (a b : UInt64) : Buf × UInt64 :=
  let w := (e12 h a) + (e12 h b);
  let c := bget h 0;
  (bpush (bpush (bpush (bset h 0 (c + 1)) a) b) w, c + 5)

/-! ## types in def headers: a stack of shapes and `(` markers (1000) over a bottom marker (2000); `×` is implicit
between adjacent shapes, reduced right-nested at `)` and at the end -/
def e16 : Nat → Buf → UInt64 → Buf → UInt64 → Buf × (UInt64 × (Buf × UInt64))
  | 0, s, q, h, k => (s, (q, (h, k)))
  | n + 1, s, q, h, k =>
    if 999 < bget s (q - 1) then (s, (q, (h, k))) else
    let (h1, k1) := e15 h (bget s (q - 1)) k;
    e16 n s (q - 1) h1 k1

/-- reduce to the bottom: (h, (shape, (p, s))) -/
def e17 (s : Buf) (q : UInt64) (h : Buf) (p : UInt64) : Buf × (UInt64 × (UInt64 × Buf)) :=
  let (s1, z) := e16 16777216 s (q - 1) h (bget s (q - 1));
  let (q1, z1) := z;
  let (h1, k) := z1;
  (h1, (k, (p, s1)))

/-- parse a type from p up to a terminator at depth 0 (`)` 7, `→` 17, `:=` 9, `|` 18): (h, (shape, (p, s))) -/
def e18 : Nat → Buf → UInt64 → Buf → UInt64 → Buf → UInt64 → Buf × (UInt64 × (UInt64 × Buf))
  | 0, t, p, s, q, h, d => (h, (0, (p, s)))
  | n + 1, t, p, s, q, h, d =>
    if bget t p == 3 then e18 n t (p + 1) (e0 s q 1) (q + 1) h d
    else if bget t p == 36 then e18 n t (p + 1) (e0 s q 2) (q + 1) h d
    else if bget t p == 35 then e18 n t (p + 1) (e0 s q 4) (q + 1) h d
    else if bget t p == 37 then e18 n t (p + 2) (e0 s q 3) (q + 1) h d
    else if bget t p == 6 then e18 n t (p + 1) (e0 s q 1000) (q + 1) h (d + 1)
    else if bget t p == 16 then e18 n t (p + 1) s q h d
    else if bget t p == 7 then
      (if d == 0 then e17 s q h p
       else
        let (s1, z) := e16 16777216 s (q - 1) h (bget s (q - 1));
        let (q1, z1) := z;
        let (h1, k) := z1;
        e18 n t (p + 1) (e0 s1 (q1 - 1) k) q1 h1 (d - 1))
    else e17 s q h p

def e19 (t : Buf) (p : UInt64) (s : Buf) (h : Buf) : Buf × (UInt64 × (UInt64 × Buf)) :=
  e18 16777216 t p (bset s 0 2000) 1 h 0

/-! ## def headers → f: (name token, first param in g, param count, result shape) per def -/
/-- skip identifiers: (p, count) -/
def e20 : Nat → Buf → UInt64 → UInt64 → UInt64 × UInt64
  | 0, t, p, c => (p, c)
  | n + 1, t, p, c => if bget t p == 14 then e20 n t (e9 t p) (c + 1) else (p, c)

/-- append c copies of code k -/
def e21 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, g, k, c => g
  | n + 1, g, k, c => if c == 0 then g else e21 n (bpush g k) k (c - 1)

/-- the code of a parameter of shape k: the first `List UInt8` alone in its group is the input (u = 1 once used) -/
def e22 (k u c : UInt64) : UInt64 × UInt64 :=
  if k == 3 then (if u == 0 then (if c == 1 then (7, 1) else (6, u)) else (6, u)) else (2 * k, u)

/-- one binder group at p (`(`): (g, (h, (s, (p, (u, count))))) -/
def e28 (t : Buf) (p : UInt64) (g h s : Buf) (u : UInt64) : Buf × (Buf × (Buf × (UInt64 × (UInt64 × UInt64)))) :=
  let (p1, c) := e20 16777216 t (p + 1) 0;
  let (h1, z) := e19 t (p1 + 1) s h;
  let (k, z1) := z;
  let (p2, s1) := z1;
  let (j, u1) := e22 k u c;
  (e21 16777216 g j c, (h1, (s1, (p2 + 1, (u1, c)))))

/-- binder groups from p: (g, (h, (s, (p, count)))) -/
def e23 : Nat → Buf → UInt64 → Buf → Buf → Buf → UInt64 → UInt64 → Buf × (Buf × (Buf × (UInt64 × UInt64)))
  | 0, t, p, g, h, s, u, m => (g, (h, (s, (p, m))))
  | n + 1, t, p, g, h, s, u, m =>
    if bget t p == 6 then
      (let (g1, z) := e28 t p g h s u;
       let (h1, z1) := z;
       let (s1, z2) := z1;
       let (p1, z3) := z2;
       let (u1, c) := z3;
       e23 n t p1 g1 h1 s1 u1 (m + c))
    else (g, (h, (s, (p, m))))

/-- arrow types from p: states until `|`: (g, (h, (s, (p, (u, (count, result)))))) -/
def e24 : Nat → Buf → UInt64 → Buf → Buf → Buf → UInt64 → UInt64 → Buf × (Buf × (Buf × (UInt64 × (UInt64 × UInt64))))
  | 0, t, p, g, h, s, u, m => (g, (h, (s, (p, (m, 0)))))
  | n + 1, t, p, g, h, s, u, m =>
    let (h1, z) := e19 t p s h;
    let (k, z1) := z;
    let (p1, s1) := z1;
    if bget t p1 == 17 then
      (let (j, u1) := e22 k u 1;
       e24 n t (p1 + 1) (bpush g j) h1 s1 u1 (m + 1))
    else (g, (h1, (s1, (p1, (m, k)))))

/-- the position of the next `def` (1) from p, or the end -/
def e25 : Nat → Buf → UInt64 → UInt64
  | 0, t, p => p
  | n + 1, t, p => if bsize t < p + 1 then p else if bget t p == 1 then p else e25 n t (e9 t p)

/-- one header at p (tag 1): (f, (g, (h, s))) -/
def e26 (t : Buf) (p : UInt64) (f g h s : Buf) : Buf × (Buf × (Buf × Buf)) :=
  let p1 := e9 t (p + 1);
  let b := bsize g;
  if bget t p1 == 6 then
    (let (g1, z) := e23 16777216 t p1 g h s 0 0;
     let (h1, z1) := z;
     let (s1, z2) := z1;
     let (p2, m) := z2;
     let (h2, z3) := e19 t (p2 + 1) s1 h1;
     let (k, z4) := z3;
     let (p3, s2) := z4;
     (bpush (bpush (bpush (bpush f (p + 1)) b) m) k, (g1, (h2, s2))))
  else if bget t (p1 + 1) == 35 then
    (let (g1, z) := e24 16777216 t (p1 + 3) (bpush g 8) h s 0 1;
     let (h1, z1) := z;
     let (s1, z2) := z1;
     let (p2, z3) := z2;
     let (m, k) := z3;
     (bpush (bpush (bpush (bpush f (p + 1)) b) m) k, (g1, (h1, s1))))
  else
    (let (h1, z) := e19 t (p1 + 1) s h;
     let (k, z1) := z;
     let (p2, s1) := z1;
     (bpush (bpush (bpush (bpush f (p + 1)) b) 0) k, (g, (h1, s1))))

def e27 : Nat → Buf → UInt64 → Buf → Buf → Buf → Buf → Buf × (Buf × (Buf × Buf))
  | 0, t, p, f, g, h, s => (f, (g, (h, s)))
  | n + 1, t, p, f, g, h, s =>
    if bsize t < p + 1 then (f, (g, (h, s))) else
    let (f1, z) := e26 t p f g h s;
    let (g1, z1) := z;
    let (h1, s1) := z1;
    e27 n t (e25 16777216 t (p + 1)) f1 g1 h1 s1

/-! ## pass 1 over a def body: a[3p] end, a[3p+1] inferred shape, a[3p+2] side flag (1: `let (a, b)` / `[]`) -/
/-- header words of the node at p -/
def e30 (r : Buf) (p : UInt64) : UInt64 :=
  if bget r p == 2 then 3 else if bget r p == 5 then 3 else if bget r p == 8 then 3
  else if bget r p == 10 then 1 else if bget r p == 11 then 1 else 2

/-- non-input argument count of prim k -/
def e31 (k : UInt64) : UInt64 :=
  if k == 2 then 1 else if k == 4 then 2 else if k == 6 then 1 else if k == 7 then 2 else if k == 8 then 3
  else if k == 9 then 2 else 0

/-- children of the node at p -/
def e32 (r : Buf) (p : UInt64) : UInt64 :=
  if bget r p == 1 then 0 else if bget r p == 2 then 0 else if bget r p == 3 then 2 else if bget r p == 4 then 4
  else if bget r p == 5 then 2 else if bget r p == 6 then bget r (p + 1) else if bget r p == 8 then bget r (p + 2)
  else if bget r p == 9 then e31 (bget r (p + 1)) else if bget r p == 10 then 2 else 1

/-- result shape of prim k (side flag f for BNEW) -/
def e33 (k f : UInt64) : UInt64 :=
  if k == 1 then 4 else if k == 4 then 3 else if k == 5 then (if f == 1 then 3 else 2) else if k == 8 then 2
  else if k == 9 then 2 else 1

/-- the side flag of the node at p, from the token cursors c (lets) and n (nils): (a, (c, n)) -/
def e34 (r t a : Buf) (p c n : UInt64) : Buf × (UInt64 × UInt64) :=
  if bget r p == 5 then
    (let c1 := e10 16777216 t c;
     (bset a (3 * p + 2) (if bget t (c1 + 1) == 6 then 1 else 0), (e9 t c1, n)))
  else if bget r p == 9 then
    (if bget r (p + 1) == 5 then
      (let n1 := e11 16777216 t n;
       (bset a (3 * p + 2) (if bget t n1 == 30 then 1 else 0), (c, e9 t n1)))
     else (a, (c, n)))
  else (a, (c, n))

/-- complete the node at q (its end is p): (a, (l, h)) -/
def e35 (r f a l h : Buf) (q p : UInt64) : Buf × (Buf × Buf) :=
  let a1 := bset a (3 * q) p;
  if bget r q == 2 then
    (if bget r (q + 2) == 0 then (bset a1 (3 * q + 1) 3, (l, h))
     else (bset a1 (3 * q + 1) (bget l (8 + 3 * (bget r (q + 1)))), (bset l (9 + 3 * (bget r (q + 1))) 1, h)))
  else if bget r q == 4 then
    (let k2 := bget a1 (3 * (q + 2));
     let k3 := bget a1 (3 * k2);
     let k4 := bget a1 (3 * k3);
     let u := bget a1 (3 * k3 + 1);
     (bset a1 (3 * q + 1) (if u == 0 then bget a1 (3 * k4 + 1) else u), (l, h)))
  else if bget r q == 5 then (bset a1 (3 * q + 1) (bget a1 (3 * (bget a1 (3 * (q + 3))) + 1)), (l, h))
  else if bget r q == 6 then
    (if bget r (q + 1) == 2 then
      (let k2 := bget a1 (3 * (q + 2));
       let (h1, k) := e15 h (bget a1 (3 * (q + 2) + 1)) (bget a1 (3 * k2 + 1));
       (bset a1 (3 * q + 1) k, (l, h1)))
     else (bset a1 (3 * q + 1) 0, (l, h)))
  else if bget r q == 8 then (bset a1 (3 * q + 1) (bget f (4 * (bget r (q + 1)) + 3)), (l, h))
  else if bget r q == 9 then (bset a1 (3 * q + 1) (e33 (bget r (q + 1)) (bget a1 (3 * q + 2))), (l, h))
  else if bget r q == 10 then (bset a1 (3 * q + 1) 0, (l, h))
  else if bget r q == 11 then (bset a1 (3 * q + 1) 0, (l, h))
  else (bset a1 (3 * q + 1) 1, (l, h))

/-- the slot shapes of the `let` at u once its value v is complete -/
def e36 (r a l h : Buf) (u v : UInt64) : Buf :=
  if (bget a (3 * u + 2) &&& 1) == 1 then
    bset (bset l (8 + 3 * (bget r (u + 1))) (e13 h (bget a (3 * v + 1))))
      (8 + 3 * ((bget r (u + 1)) + (e12 h (e13 h (bget a (3 * v + 1)))))) (e14 h (bget a (3 * v + 1)))
  else bset l (8 + 3 * (bget r (u + 1))) (bget a (3 * v + 1))

/-! ## numeral classes (NumSpec.slotNat): run A of pass 1 sets literal-only flags (a[3p+2] bit 4) and the per-slot
literal env; pass B assigns modes (0 none, 1 + d demand d, 4 a tuple `let` value, 8 + g in literal group g) and
records (slot, group) pairs; the closure marks UInt64 groups (a[3(g+1)]) and slots; run 2 sets the natE flags (bit 8),
Nat comparisons (ite bit 1) and Nat lets (let bit 2, slot shape 4). l[3]: base of the per-slot words (env, in a group,
marked), l[4]: the run (0: A). -/
def e73 (a : Buf) (x : UInt64) : UInt64 := ((bget a (3 * x + 2)) >>> 2) &&& 1
def e74 (a : Buf) (x : UInt64) : UInt64 := ((bget a (3 * x + 2)) >>> 3) &&& 1

/-- literal-only flag of the completed node q (run A) -/
def e75 (r a l : Buf) (q : UInt64) : UInt64 :=
  if bget r q == 1 then 1
  else if bget r q == 2 then (if bget r (q + 2) == 1 then bget l (bget l 3 + 4 * (bget r (q + 1))) else 0)
  else if bget r q == 3 then
    (if bget r (q + 1) == 6 then 0 else if bget r (q + 1) == 7 then 0 else e73 a (q + 2) &&& e73 a (bget a (3 * (q + 2))))
  else if bget r q == 4 then
    (let k2 := bget a (3 * (q + 2));
     let k3 := bget a (3 * k2);
     e73 a k3 &&& e73 a (bget a (3 * k3)))
  else if bget r q == 5 then e73 a (bget a (3 * (q + 3)))
  else 0

/-- the flag word of the completed node q in run 2: natE (8), Nat comparison (ite: 1), side flags kept -/
def e76 (r a l : Buf) (q : UInt64) : UInt64 :=
  if bget r q == 1 then 8
  else if bget r q == 2 then (if bget r (q + 2) == 1 then (if bget l (8 + 3 * (bget r (q + 1))) == 4 then 8 else 0) else 0)
  else if bget r q == 4 then
    (let k2 := bget a (3 * (q + 2));
     let k3 := bget a (3 * k2);
     let k4 := bget a (3 * k3);
     (if e74 a k3 == 1 then (if e74 a k4 == 1 then 8 else 0) else 0) ||| (if e74 a (q + 2) == 1 then (if e74 a k2 == 1 then 1 else 0) else 0))
  else if bget r q == 5 then ((bget a (3 * q + 2)) &&& 3) ||| (if e74 a (bget a (3 * (q + 3))) == 1 then 8 else 0)
  else bget a (3 * q + 2)

def e60 (r a l : Buf) (q : UInt64) : Buf :=
  if bget l 4 == 0 then (if e75 r a l q == 1 then bset a (3 * q + 2) ((bget a (3 * q + 2)) ||| 4) else a)
  else bset a (3 * q + 2) (e76 r a l q)

/-- c env words from slot i to slot j (zr = 1: zeros) -/
def e63 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, l, b, i, j, c, zr => l
  | n + 1, l, b, i, j, c, zr =>
    if c == 0 then l else e63 n (bset l (b + 4 * j) (if zr == 1 then 0 else bget l (b + 4 * i))) b (i + 1) (j + 1) (c - 1) zr

/-- the env words of the value from p (end z) into slots from j: tuples descend, slots copy, others their flag -/
def e62 : Nat → Buf → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, r, a, l, h, p, z, j => l
  | n + 1, r, a, l, h, p, z, j =>
    if p < z then
      (if bget r p == 6 then e62 n r a l h (p + 2) z j
       else if bget r p == 2 then
         e62 n r a (e63 16777216 l (bget l 3) (bget r (p + 1)) j (bget r (p + 2)) 0) h (bget a (3 * p)) z (j + bget r (p + 2))
       else
         (let w := e12 h (bget a (3 * p + 1));
          e62 n r a (if w == 1 then bset l (bget l 3 + 4 * j) (e73 a p) else e63 16777216 l (bget l 3) 0 j w 1) h (bget a (3 * p)) z (j + w)))
    else l

/-- the `let` at u with value v is a Nat let (run 2): single, slot of class Nat, value natE -/
def e72 (r a l : Buf) (u v : UInt64) : UInt64 :=
  if (bget a (3 * u + 2) &&& 1) == 0 then
    (let b := bget l 3 + 4 * (bget r (u + 1));
     if bget l (b + 1) == 1 then (if bget l (b + 2) == 0 then e74 a v else 0) else 0)
  else 0

/-- after the slot shapes of the `let` at u (value v): run A the env, run 2 the Nat slot shape -/
def e70 (r a l h : Buf) (u v : UInt64) : Buf :=
  if bget l 4 == 0 then e62 1073741824 r a l h v (bget a (3 * v)) (bget r (u + 1))
  else if e72 r a l u v == 1 then bset l (8 + 3 * (bget r (u + 1))) 4 else l

def e71 (r a l : Buf) (u v : UInt64) : Buf :=
  if bget l 4 == 1 then (if e72 r a l u v == 1 then bset a (3 * u + 2) ((bget a (3 * u + 2)) ||| 2) else a) else a

/-- open the node at p: (s, (a, (c, n))) -/
def e38 (r t s a : Buf) (p q c n : UInt64) : Buf × (Buf × (UInt64 × UInt64)) :=
  let (a1, z) := e34 r t a p c n;
  (e0 (e0 s q p) (q + 1) (e32 r p), (a1, z))

/-- the pass: stack entries (node, children left), never empty (the caller opens the root); p the cursor -/
def e37 : Nat → Buf → Buf → Buf → UInt64 → Buf → UInt64 → Buf → Buf → Buf → UInt64 → UInt64 → Buf × (Buf × (Buf × (Buf × (UInt64 × UInt64))))
  | 0, r, t, f, p, s, q, a, l, h, c, n => (s, (a, (l, (h, (c, n)))))
  | k + 1, r, t, f, p, s, q, a, l, h, c, n =>
    if bget s (q - 1) == 0 then
      (let (a0, z) := e35 r f a l h (bget s (q - 2)) p;
       let (l1, h1) := z;
       let a1 := e60 r a0 l1 (bget s (q - 2));
       if q == 2 then (s, (a1, (l1, (h1, (c, n))))) else
       let w := bget s (q - 3) - 1;
       let u := bget s (q - 4);
       let l2 := (if bget r u == 5 then (if w == 1 then e70 r a1 (e36 r a1 l1 h1 u (bget s (q - 2))) h1 u (bget s (q - 2)) else l1) else l1);
       let a2 := (if bget r u == 5 then (if w == 1 then e71 r a1 l2 u (bget s (q - 2)) else a1) else a1);
       e37 k r t f p (bset s (q - 3) w) (q - 2) a2 l2 h1 c n)
    else
      (let (s1, z) := e38 r t s a p q c n;
       let (a1, z1) := z;
       let (c1, n1) := z1;
       e37 k r t f (p + e30 r p) s1 (q + 2) a1 l h c1 n1)

/-! ## pass 2: the work list -/
def e41 (s : Buf) (q k x y z : UInt64) : Buf := e0 (e0 (e0 (e0 s q k) (q + 1) x) (q + 2) y) (q + 3) z

def e43 (s : Buf) (i j : UInt64) : Buf :=
  let a0 := bget s i;
  let a1 := bget s (i + 1);
  let a2 := bget s (i + 2);
  let a3 := bget s (i + 3);
  e41 (e41 s i (bget s j) (bget s (j + 1)) (bget s (j + 2)) (bget s (j + 3))) j a0 a1 a2 a3

/-- reverse the items from word i to word j (the last item) -/
def e42 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, s, i, j => s
  | n + 1, s, i, j => if i < j then e42 n (e43 s i j) (i + 4) (j - 4) else s

/-- c phrase items k -/
def e44 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, s, q, k, c => (s, q)
  | n + 1, s, q, k, c => if c == 0 then (s, q) else e44 n (e41 s q 1 k 0 0) (q + 4) k (c - 1)

/-- parameter count (with the input) and codes of prim k -/
def e45 (k : UInt64) : UInt64 := if k == 1 then 1 else if k == 3 then 1 else if k == 8 then 3 else if k == 6 then 1 else 2
def e46 (k j : UInt64) : UInt64 :=
  if k == 1 then 7 else if k == 3 then 7 else if k == 2 then (if j == 0 then 7 else 2)
  else if k == 4 then (if j == 0 then 6 else 2) else if k == 6 then 4 else if k == 7 then (if j == 0 then 4 else 2)
  else if k == 8 then (if j == 0 then 4 else 2) else (if j == 0 then 4 else 2)

/-- argument items for c parameters from j (codes g[b + j], or prim k's when k ≠ 0), children from u -/
def e47 : Nat → Buf → UInt64 → Buf → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, s, q, a, g, l, h, k, b, j, c, u, d => (s, q)
  | n + 1, s, q, a, g, l, h, k, b, j, c, u, d =>
    if c == 0 then (s, q) else
    let w := (if k == 0 then bget g (b + j) else e46 k j);
    if (w &&& 1) == 1 then e47 n (e41 s q 4 (d - bget l 0) 0 0) (q + 4) a g l h k b (j + 1) (c - 1) u d
    else e47 n (e41 s q 3 u (w >>> 1) d) (q + 4) a g l h k b (j + 1) (c - 1) (bget a (3 * u)) d

/-- items of the node at p (expected shape e, depth d), pushed in output order from q: (s, (q, l)) -/
def e48 (r f g a h : Buf) (s : Buf) (q : UInt64) (l : Buf) (p e d : UInt64) : Buf × (UInt64 × Buf) :=
  if bget r p == 1 then
    (if e == 4 then
      (e41 (e41 (e41 (e41 (e41 s q 1 12 0 0) (q + 4) 2 4 0 0) (q + 8) 5 (bget r (p + 1)) 0 0) (q + 12) 1 14 0 0) (q + 16) 5 (bget r (p + 1)) 0 0, (q + 20, l))
     else
      (e41 (e41 (e41 (e41 (e41 s q 1 12 0 0) (q + 4) 2 1 0 0) (q + 8) 5 (bget r (p + 1)) 0 0) (q + 12) 1 13 0 0) (q + 16) 5 (bget r (p + 1)) 0 0, (q + 20, l)))
  else if bget r p == 2 then
    (if bget r (p + 2) == 0 then (e41 s q 4 (d - bget l 0) 0 0, (q + 4, l))
     else (e41 s q 4 (d - bget l (10 + 3 * (bget r (p + 1)))) 0 0, (q + 4, l)))
  else if bget r p == 3 then
    (e41 (e41 (e41 s q 1 (14 + bget r (p + 1)) 0 0) (q + 4) 3 (p + 2) 1 d) (q + 8) 3 (bget a (3 * (p + 2))) 1 d, (q + 12, l))
  else if bget r p == 4 then
    (let k2 := bget a (3 * (p + 2));
     let k3 := bget a (3 * k2);
     let k4 := bget a (3 * k3);
     let w := (if e == 0 then bget a (3 * p + 1) else e);
     let nc := (bget a (3 * p + 2)) &&& 1;
     let o := (if nc == 1 then 4 else 1);
     if bget r (p + 1) == 1 then
       (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 s q 1 22 0 0) (q + 4) 2 w 0 0) (q + 8) 1 (if nc == 1 then 48 else 23) 0 0)
         (q + 12) 3 (p + 2) o d) (q + 16) 3 k2 o d) (q + 20) 1 (if nc == 1 then 49 else 24) 0 0) (q + 24) 3 (p + 2) o d) (q + 28) 3 k2 o d)
         (q + 32) 1 25 0 0) (q + 36) 3 k3 e d) (q + 40) 3 k4 e d, (q + 44, l))
     else
       (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 s q 1 22 0 0) (q + 4) 2 w 0 0) (q + 8) 1 (if nc == 1 then 50 else 26) 0 0)
         (q + 12) 3 (p + 2) o d) (q + 16) 3 k2 o d) (q + 20) 1 (if nc == 1 then 51 else 27) 0 0) (q + 24) 6 (p + 2) o d) (q + 28) 6 k2 o d)
         (q + 32) 3 k3 e d) (q + 36) 3 k4 e d, (q + 40, l)))
  else if bget r p == 5 then
    (let b := bget a (3 * (p + 3));
     let v := bget a (3 * (p + 3) + 1);
     if ((bget a (3 * p + 2)) &&& 1) == 0 then
       (let nl := ((bget a (3 * p + 2)) >>> 1) &&& 1;
        e41 (e41 (e41 (e41 s q 1 4 0 0) (q + 4) 2 (if nl == 1 then 4 else v) 0 0) (q + 8) 3 (p + 3) (if nl == 1 then 4 else 0) d) (q + 12) 3 b e (d + 1),
        (q + 16, bset l (10 + 3 * (bget r (p + 1))) (d + 1)))
     else
       (let w := (if e == 0 then bget a (3 * p + 1) else e);
        (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 (e41 s q 1 28 0 0) (q + 4) 2 (e13 h v) 0 0)
          (q + 8) 2 (e14 h v) 0 0) (q + 12) 1 2 0 0) (q + 16) 2 v 0 0) (q + 20) 2 w 0 0) (q + 24) 3 (p + 3) 0 d)
          (q + 28) 1 2 0 0) (q + 32) 2 (e13 h v) 0 0) (q + 36) 1 2 0 0) (q + 40) 2 (e14 h v) 0 0) (q + 44) 3 b e (d + 2),
         (q + 48, bset (bset l (10 + 3 * (bget r (p + 1))) (d + 1)) (10 + 3 * ((bget r (p + 1)) + (e12 h (e13 h v)))) (d + 2)))))
  else if bget r p == 6 then
    (let k2 := bget a (3 * (p + 2));
     let x := (if e < 5 then 0 else e13 h e);
     let y := (if e < 5 then 0 else e14 h e);
     let u := (if x == 0 then bget a (3 * (p + 2) + 1) else x);
     let v := (if y == 0 then bget a (3 * k2 + 1) else y);
     (e41 (e41 (e41 (e41 (e41 s q 1 29 0 0) (q + 4) 2 u 0 0) (q + 8) 2 v 0 0) (q + 12) 3 (p + 2) x d) (q + 16) 3 k2 y d,
      (q + 20, l)))
  else if bget r p == 8 then
    (let i := bget r (p + 1);
     let (s1, q1) := e44 1048576 s q 0 (bget f (4 * i + 2));
     let (s2, q2) := e47 1048576 (e41 (e41 s1 q1 1 1 0 0) (q1 + 4) 7 (bget f (4 * i)) 0 0) (q1 + 8) a g l h 0 (bget f (4 * i + 1)) 0 (bget f (4 * i + 2)) (p + 3) d;
     (s2, (q2, l)))
  else if bget r p == 9 then
    (if bget r (p + 1) == 5 then
      (if bget a (3 * p + 2) == 1 then (e41 s q 1 30 0 0, (q + 4, l)) else (e41 s q 1 31 0 0, (q + 4, l)))
     else
      (let k := bget r (p + 1);
       let (s1, q1) := e44 8 s q 0 (e45 k);
       let (s2, q2) := e47 8 (e41 s1 q1 1 (31 + k) 0 0) (q1 + 4) a g l h k 0 0 (e45 k) (p + 2) d;
       (s2, (q2, l))))
  else
    -- CONTINUE: the self def's states, from param 1
    (let i := bget l 2;
     let m := bget f (4 * i + 2);
     let u := (if (m - 1) - (if bget l 0 == 0 then 0 else 1) == 1 then p + 1 else p + 3);
     let (s1, q1) := e44 1048576 s q 0 m;
     let (s2, q2) := e47 1048576 (e41 (e41 (e41 s1 q1 1 1 0 0) (q1 + 4) 7 (bget f (4 * i)) 0 0) (q1 + 8) 4 (d - bget l 1) 0 0) (q1 + 12) a g l h 0 (bget f (4 * i + 1)) 1 (m - 1) u d;
     (s2, (q2, l)))

/-- a node item; mode 6 first drops leading unused single `let`s -/
def e49 : Nat → Buf → Buf → Buf → Buf → Buf → Buf → UInt64 → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × (UInt64 × Buf)
  | 0, r, f, g, a, h, s, q, l, p, e, d, m => (s, (q, l))
  | n + 1, r, f, g, a, h, s, q, l, p, e, d, m =>
    if m == 6 then
      (if bget r p == 5 then
        (if ((bget a (3 * p + 2)) &&& 1) == 0 then
          (if bget l (9 + 3 * (bget r (p + 1))) == 0 then e49 n r f g a h s q l (bget a (3 * (p + 3))) e d m
           else e48 r f g a h s q l p e d)
         else e48 r f g a h s q l p e d)
       else e48 r f g a h s q l p e d)
    else e48 r f g a h s q l p e d

/-- run the work list: (s, (l, o)) -/
def e50 : Nat → List UInt8 → Buf → Buf → Buf → Buf → Buf → Buf → Buf → UInt64 → Buf → List UInt8 → Buf × (Buf × List UInt8)
  | 0, x, r, t, f, g, a, h, s, q, l, o => (s, (l, o))
  | n + 1, x, r, t, f, g, a, h, s, q, l, o =>
    if q == 0 then (s, (l, o)) else
    let k := bget s (q - 4);
    let y := bget s (q - 3);
    if k == 1 then e50 n x r t f g a h s (q - 4) l (e57 x o y)
    else if k == 4 then e50 n x r t f g a h s (q - 4) l (e6 x (e2 32 x o 43 0) y)
    else if k == 5 then e50 n x r t f g a h s (q - 4) l (e6 x (e2 32 x o 44 0) y)
    else if k == 7 then e50 n x r t f g a h s (q - 4) l (e7 16777216 x (e2 32 x o 45 0) t (y + 1))
    else if k == 2 then
      (if y < 5 then e50 n x r t f g a h s (q - 4) l (e57 x o (6 + y))
       else e50 n x r t f g a h (e41 (e41 s (q - 4) 2 (e14 h y) 0 0) q 2 (e13 h y) 0 0) (q + 4) l (e57 x o 11))
    else
      (let (s1, z) := e49 16777216 r f g a h s (q - 4) l y (bget s (q - 2)) (bget s (q - 1)) k;
       let (q1, l1) := z;
       e50 n x r t f g a h (e42 1048576 s1 (q - 4) (q1 - 4)) q1 l1 o)

/-! ## per def -/
/-- zero the slot table words 8 .. 8 + c -/
def e51 : Nat → Buf → UInt64 → UInt64 → Buf
  | 0, l, i, c => l
  | n + 1, l, i, c => if c == 0 then l else e51 n (e0 l i 0) (i + 1) (c - 1)

/-- parameter j of c from code base b: slot shapes and levels; slot cursor u -/
def e52 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, g, h, l, b, j, c, u => l
  | n + 1, g, h, l, b, j, c, u =>
    if c == 0 then l else
    let w := bget g (b + j);
    if (w &&& 1) == 1 then e52 n g h (bset l 0 (j + 1)) b (j + 1) (c - 1) u
    else e52 n g h (bset (bset l (8 + 3 * u) (w >>> 1)) (10 + 3 * u) (j + 1)) b (j + 1) (c - 1) (u + e12 h (w >>> 1))

/-- items for c params from j: phrase k then the parameter's type -/
def e53 : Nat → Buf → UInt64 → Buf → UInt64 → UInt64 → UInt64 → UInt64 → Buf × UInt64
  | 0, s, q, g, b, j, c, k => (s, q)
  | n + 1, s, q, g, b, j, c, k =>
    if c == 0 then (s, q) else e53 n (e41 (e41 s q 1 k 0 0) (q + 4) 2 ((bget g (b + j)) >>> 1) 0 0) (q + 8) g b (j + 1) (c - 1) k

/-- the items of def i whose IR starts at p (body at p + 6): (s, q) -/
def e54 (r f g a : Buf) (s : Buf) (i p : UInt64) : Buf × UInt64 :=
  let b := bget f (4 * i + 1);
  let m := bget f (4 * i + 2);
  let (s1, q1) := e53 1048576 (e41 (e41 s 0 1 6 0 0) 4 7 (bget f (4 * i)) 0 0) 8 g b 0 m 3;
  let (s2, q2) := e53 1048576 (e41 s1 q1 2 (bget f (4 * i + 3)) 0 0) (q1 + 4) g b 0 m 2;
  if bget r (p + 4) == 1 then
    (e41 (e41 (e41 (e41 (e41 (e41 (e41 s2 q2 1 41 0 0) (q2 + 4) 2 (bget f (4 * i + 3)) 0 0) (q2 + 8) 4 (m - 1) 0 0)
      (q2 + 12) 3 (p + 7) (bget f (4 * i + 3)) m) (q2 + 16) 1 42 0 0) (q2 + 20) 3 (bget a (3 * (p + 7))) (bget f (4 * i + 3)) (m + 1))
      (q2 + 24) 1 5 0 0, q2 + 28)
  else (e41 (e41 s2 q2 3 (p + 6) (bget f (4 * i + 3)) m) (q2 + 4) 1 5 0 0, q2 + 8)

/-! ## pass B: modes and (slot, group) records; the closure -/
/-- c children from x get mode m -/
def e66 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, a, x, c, m => a
  | n + 1, a, x, c, m => if c == 0 then a else (let y := bget a (3 * x); e66 n (bset a (3 * x + 1) m) y (c - 1) m)

/-- the fields from x of a tuple `let` value (records from header word hp) -/
def e67 : Nat → Buf → UInt64 → UInt64 → UInt64 → Buf
  | 0, a, x, c, hp => a
  | n + 1, a, x, c, hp =>
    if c == 0 then a else
    let y := bget a (3 * x);
    e67 n (if e73 a x == 1 then bset (bset a (3 * x + 1) (8 + x)) (3 * hp + 1) (8 + x) else bset a (3 * x + 1) 1) y (c - 1) (hp + 1)

/-- the children modes of node p in mode m -/
def e65 (r f g a : Buf) (p m : UInt64) : Buf :=
  let cm := (if 0 < m then (if m < 4 then 1 else 0) else 0);
  let dm := (if 7 < m then m else if cm == 1 then 2 else 0);
  if bget r p == 3 then e66 2 a (p + 2) 2 dm
  else if bget r p == 4 then
    (let k2 := bget a (3 * (p + 2));
     let a1 := e66 2 a (bget a (3 * k2)) 2 dm;
     if m == 0 then e66 2 a1 (p + 2) 2 0
     else if e73 a1 (p + 2) == 1 then
       (if e73 a1 k2 == 1 then bset (bset a1 (3 * (p + 2) + 1) (10 + p)) (3 * k2 + 1) (10 + p) else e66 2 a1 (p + 2) 2 2)
     else e66 2 a1 (p + 2) 2 2)
  else if bget r p == 5 then
    (let a1 := bset (bset (bset a (3 * (bget a (3 * (p + 3))) + 1) m) (3 * (p + 1) + 1) 0) (3 * (p + 2) + 1) 0;
     if m == 0 then bset a1 (3 * (p + 3) + 1) 0
     else if bget r (p + 3) == 6 then bset a1 (3 * (p + 3) + 1) 4
     else if e73 a1 (p + 3) == 1 then bset (bset a1 (3 * (p + 3) + 1) (11 + p)) (3 * (p + 1) + 1) (11 + p)
     else bset a1 (3 * (p + 3) + 1) 1)
  else if bget r p == 6 then
    (if m == 4 then e67 4 a (p + 2) (bget r (p + 1)) (p - 2) else e66 1048576 a (p + 2) (bget r (p + 1)) dm)
  else if bget r p == 8 then
    (if cm == 1 then
      (if 0 < bget r (p + 2) then
        (let y := bget a (3 * (p + 3));
         e66 1048576 (bset a (3 * (p + 3) + 1) (if bget g (bget f (4 * (bget r (p + 1)) + 1)) == 8 then 3 else 2)) y ((bget r (p + 2)) - 1) 2)
       else a)
     else e66 1048576 a (p + 3) (bget r (p + 2)) 0)
  else if bget r p == 9 then e66 8 a (p + 2) (e31 (bget r (p + 1))) dm
  else if bget r p == 10 then e66 2 a (p + 1) 2 dm
  else if bget r p == 11 then e66 1 a (p + 1) 1 dm
  else a

/-- pass B over the nodes from p (body end z): a node in a demand mode that is literal-only starts its group -/
def e64 : Nat → Buf → Buf → Buf → Buf → UInt64 → UInt64 → Buf
  | 0, r, f, g, a, p, z => a
  | n + 1, r, f, g, a, p, z =>
    if p < z then
      (let m0 := bget a (3 * p + 1);
       let c := (if 0 < m0 then (if m0 < 4 then e73 a p else 0) else 0);
       let m := (if c == 1 then 8 + p else m0);
       let a1 := (if c == 1 then (if m0 == 2 then bset a (3 * (p + 1)) 1 else a) else a);
       e64 n r f g (e65 r f g (bset a1 (3 * p + 1) m) p m) (p + e30 r p) z)
    else a

/-- one (slot s, group g) record: s is in a group; a marked group marks s and back (ch = 1: a change) -/
def e68 (a l : Buf) (s g ch : UInt64) : Buf × (Buf × UInt64) :=
  let b := bget l 3 + 4 * s;
  let l1 := bset l (b + 1) 1;
  let u := bget a (3 * (g + 1));
  let mk := bget l1 (b + 2);
  if (u ||| mk) == 1 then
    (if (u &&& mk) == 1 then (a, (l1, ch)) else (bset a (3 * (g + 1)) 1, (bset l1 (b + 2) 1, 1)))
  else (a, (l1, ch))

/-- one sweep over the records of the nodes from p -/
def e69 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → Buf × (Buf × UInt64)
  | 0, r, a, l, p, z, ch => (a, (l, ch))
  | n + 1, r, a, l, p, z, ch =>
    if p < z then
      (if bget r p == 2 then
        (if 7 < bget a (3 * p + 1) then
          (let (a1, y) := e68 a l (bget r (p + 1)) ((bget a (3 * p + 1)) - 8) ch;
           let (l1, ch1) := y;
           e69 n r a1 l1 (p + 3) z ch1)
         else e69 n r a l (p + 3) z ch)
       else if bget r p == 5 then
        (let (a1, y) := (if 7 < bget a (3 * (p + 1) + 1) then e68 a l (bget r (p + 1)) ((bget a (3 * (p + 1) + 1)) - 8) ch else (a, (l, ch)));
         let (l1, ch1) := y;
         let (a2, y1) := (if 7 < bget a1 (3 * (p + 2) + 1) then e68 a1 l1 ((bget r (p + 1)) + 1) ((bget a1 (3 * (p + 2) + 1)) - 8) ch1 else (a1, (l1, ch1)));
         let (l2, ch2) := y1;
         e69 n r a2 l2 (p + 3) z ch2)
       else e69 n r a l (p + e30 r p) z ch)
    else (a, (l, ch))

/-- sweeps until nothing changes -/
def e77 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → Buf × Buf
  | 0, r, a, l, p, z => (a, l)
  | n + 1, r, a, l, p, z =>
    let (a1, y) := e69 1073741824 r a l p z 0;
    let (l1, ch) := y;
    if ch == 0 then (a1, l1) else e77 n r a1 l1 p z

/-- def i at IR position p (tag 20): (h, (s, (a, (l, (c, (n, (next p, o))))))) -/
def e58 (x : List UInt8) (r t f g h s a l : Buf) (i p c n : UInt64) (o : List UInt8) : Buf × (Buf × (Buf × (Buf × (UInt64 × (UInt64 × (UInt64 × List UInt8)))))) :=
  let m := bget f (4 * i + 2);
  let ns := bget r (p + 3);
  let l1 := e52 1048576 g h (bset (bset (bset (bset (bset (e51 1073741824 l 0 (8 + 7 * (ns + 1))) 1 (m + 1)) 2 i) 0 0) 3 (8 + 3 * (ns + 1))) 4 0) (bget f (4 * i + 1)) 0 m 0;
  let (sA, yA) := e38 r t s a (p + 6) 0 c n;
  let (aA, yA1) := yA;
  let (cA, nA) := yA1;
  let (sB, zA) := e37 1073741824 r t f (p + 6 + e30 r (p + 6)) sA 2 aA l1 h cA nA;
  let (aB, zA1) := zA;
  let (lB, zA2) := zA1;
  let (hB, zA3) := zA2;
  let zb := bget aB (3 * (p + 6));
  let aC := e64 1073741824 r f g (bset aB (3 * (p + 6) + 1) 2) (p + 6) zb;
  let (aD, lD) := e77 1048576 r aC lB (p + 6) zb;
  let (s0, y) := e38 r t sB aD (p + 6) 0 c n;
  let (a0, y1) := y;
  let (c0, n0) := y1;
  let (s1, z) := e37 1073741824 r t f (p + 6 + e30 r (p + 6)) s0 2 a0 (bset lD 4 1) hB c0 n0;
  let (a1, z1) := z;
  let (l2, z2) := z1;
  let (h1, z3) := z2;
  let (c1, n1) := z3;
  let e := bget a1 (3 * (p + 6));
  let (s2, q2) := e54 r f g a1 s1 i p;
  let (s3, z4) := e50 1073741824 x r t f g a1 h1 (e42 1048576 s2 0 (q2 - 4)) q2 l2 o;
  let (l3, o1) := z4;
  (h1, (s3, (a1, (l3, (c1, (n1, (e + 1, o1)))))))

/-- every def from IR position p (tag 20): o -/
def e55 : Nat → List UInt8 → Buf → Buf → Buf → Buf → Buf → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, x, r, t, f, g, h, s, a, l, i, p, c, n, o => o
  | k + 1, x, r, t, f, g, h, s, a, l, i, p, c, n, o =>
    if bget r p == 20 then
      (let (h1, z) := e58 x r t f g h s a l i p c n o;
       let (s1, z1) := z;
       let (a1, z2) := z1;
       let (l1, z3) := z2;
       let (c1, z4) := z3;
       let (n1, z5) := z4;
       let (p1, o1) := z5;
       e55 k x r t f g h1 s1 a1 l1 (i + 1) p1 c1 n1 o1)
    else o

def e99 (x : List UInt8) : List UInt8 :=
  let r := u10 (y16 (s10 x));
  if bsize r == 0 then e2 4 x [] 46 0 else
  let t := s10 x;
  let (f, z) := e27 16777216 t 0 bnew bnew (bpush bnew 0) (bpush bnew 2000);
  let (g, z1) := z;
  let (h, s) := z1;
  e55 1073741824 x r t f g h s (e21 1073741824 bnew 0 (3 * bsize r)) (e21 16 bnew 0 8) 0 1 0 0 []

end C

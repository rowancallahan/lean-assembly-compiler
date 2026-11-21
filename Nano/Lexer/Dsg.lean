/- Nano/Lexer: the MATCH DESUGAR stage `t10` between the lexer (`s10`) and the parser (`y16`) (exp-syntax,
Testing/notes/SYNTAX_EXP.md §2; specification: `DsSpec.ds`, Nano/Lexer/DsSpec.lean).
Token words in, token words out (or the EMPTY Buf: reject).  `match E with | 3 => a | 7 => b | y => c` becomes
`let μ := E; if μ == 3 then a else if μ == 7 then b else let y := μ; c` (μ = the identifier spelled `$`, not a Lean
name); `| _ =>` becomes `else`; a first arm `| (x, y) =>` becomes `let (x, y) := μ;`.  `match` and `with` are the
identifiers with those spellings (Lean keywords).  Per paren depth d one cell: 0 no match, 1 a match still needing a
catch-all arm, 2 a match with its catch-all arm.  A match ends at the `)` of its depth, at the next `def` or at the end;
it must have its catch-all arm by then.  `|` at a depth whose cell is 1 is an arm, 2 is rejected, 0 is copied.
A text with no `match` token (`t11`) is passed through unchanged, without allocating (same memory as before).
`t12` first rejects a match with two literal arms of the same value (`DsSpec.dupOk`): each open match (per depth, `s`)
has an id; the literals seen are appended to `u` as (id, 8 value words), `t13`/`t14` look one up, `t15` adds one. -/
import Nano.Main.Chain
namespace C

def t1 : Nat → Buf → UInt64 → UInt64
  | 0, t, j => 0
  | n + 1, t, j => if j < bsize t then if bget t j == 0 then j + 1 else if bget t j == 1 then if j + 1 < bsize t then t1 n t (j + 2) else 0 else 0 else 0

def t0 (t : Buf) (i : UInt64) : UInt64 :=
  if bget t i == 5 then if i + 8 < bsize t then i + 9 else 0
  else if bget t i == 14 then t1 16777216 t (i + 1)
  else i + 1

def t2 (t : Buf) (i e : UInt64) : UInt64 :=
  if e == i + 12 then if bget t i == 14 then if bget t (i + 1) == 1 then if bget t (i + 2) == 109 then if bget t (i + 3) == 1 then if bget t (i + 4) == 97 then if bget t (i + 5) == 1 then if bget t (i + 6) == 116 then if bget t (i + 7) == 1 then if bget t (i + 8) == 99 then if bget t (i + 9) == 1 then if bget t (i + 10) == 104 then if bget t (i + 11) == 0 then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0

def t3 (t : Buf) (i e : UInt64) : UInt64 :=
  if e == i + 10 then if bget t i == 14 then if bget t (i + 1) == 1 then if bget t (i + 2) == 119 then if bget t (i + 3) == 1 then if bget t (i + 4) == 105 then if bget t (i + 5) == 1 then if bget t (i + 6) == 116 then if bget t (i + 7) == 1 then if bget t (i + 8) == 104 then if bget t (i + 9) == 0 then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0

def t4 (t : Buf) (i e : UInt64) : UInt64 :=
  if e == i + 4 then if bget t i == 14 then if bget t (i + 1) == 1 then if bget t (i + 2) == 95 then if bget t (i + 3) == 0 then 1 else 0 else 0 else 0 else 0 else 0

def t5 (o : Buf) : Buf := bpush (bpush (bpush (bpush o 14) 1) 36) 0

def t6 : Nat → Buf → UInt64 → UInt64 → Buf → Buf
  | 0, t, a, b, o => o
  | n + 1, t, a, b, o => if a < b then t6 n t (a + 1) b (bpush o (bget t a)) else o

def t8 (t : Buf) (j : UInt64) (o : Buf) : UInt64 × Buf :=
  let x := t0 t (j + 1);
  if bget t (j + 1) == 14 then if x == 0 then (0, bnew) else if bget t x == 15 then if bget t (x + 1) == 14 then
    let y := t0 t (x + 1);
    if y == 0 then (0, bnew) else if bget t y == 7 then if bget t (y + 1) == 19 then
      ((y + 2) * 4 + 2, bpush (t5 (bpush (bpush (t6 16777216 t (x + 1) y (bpush (t6 16777216 t (j + 1) x (bpush (bpush o 2) 6)) 15)) 7) 9)) 13)
    else (0, bnew) else (0, bnew)
  else (0, bnew) else (0, bnew) else (0, bnew)

def t7 (t : Buf) (j f : UInt64) (o : Buf) : UInt64 × Buf :=
  let e := t0 t j;
  if j < bsize t then
    if e == 0 then (0, bnew)
    else if bget t j == 5 then if bget t e == 19 then
        ((e + 1) * 4 + 1, bpush (t6 16777216 t j e (bpush (t5 (bpush (if f == 1 then o else bpush o 34) 32)) 23)) 33)
      else (0, bnew)
    else if t4 t j e == 1 then if bget t e == 19 then ((e + 1) * 4 + 2, if f == 1 then o else bpush o 34) else (0, bnew)
    else if bget t j == 14 then if bget t e == 19 then
        ((e + 1) * 4 + 2, bpush (t5 (bpush (t6 16777216 t j e (bpush (if f == 1 then o else bpush o 34) 2)) 9)) 13)
      else (0, bnew)
    else if bget t j == 6 then if f == 1 then t8 t j o else (0, bnew)
    else (0, bnew)
  else (0, bnew)

def t9 : Nat → Buf → UInt64 → UInt64 → Buf → UInt64 → Buf → Buf
  | 0, t, i, d, s, c, o => bnew
  | n + 1, t, i, d, s, c, o =>
    if i < bsize t then
      let e := t0 t i;
      let k := bget t i;
      if e == 0 then bnew
      else if c == 1 then
        if t3 t i e == 1 then
          if bget t e == 18 then
            let (q, o1) := t7 t (e + 1) 1 (bpush o 13);
            if q == 0 then bnew else t9 n t (q >>> 2) d (bset s d (q &&& 3)) 0 o1
          else bnew
        else if t2 t i e == 1 then bnew
        else if k == 18 then bnew
        else if k == 19 then bnew
        else t9 n t e d s 1 (t6 16777216 t i e o)
      else if t2 t i e == 1 then
        if bget s d == 1 then bnew else t9 n t e d s 1 (bpush (t5 (bpush o 2)) 9)
      else if t3 t i e == 1 then bnew
      else if k == 18 then
        if bget s d == 1 then
          let (q, o1) := t7 t e 0 o;
          if q == 0 then bnew else t9 n t (q >>> 2) d (bset s d (q &&& 3)) 0 o1
        else if bget s d == 2 then bnew
        else t9 n t e d s 0 (bpush o 18)
      else if k == 6 then t9 n t e (d + 1) (if d + 1 < bsize s then bset s (d + 1) 0 else bpush s 0) 0 (bpush o 6)
      else if k == 7 then
        if bget s d == 1 then bnew else if d == 0 then bnew else t9 n t e (d - 1) (bset s d 0) 0 (bpush o 7)
      else if k == 1 then
        if d == 0 then if bget s 0 == 1 then bnew else t9 n t e 0 (bset s 0 0) 0 (bpush o 1) else bnew
      else t9 n t e d s 0 (t6 16777216 t i e o)
    else if c == 1 then bnew else if d == 0 then if bget s 0 == 1 then bnew else o else bnew

def t14 (u : Buf) (k : UInt64) (t : Buf) (j : UInt64) : UInt64 :=
  if bget u (k + 1) == bget t (j + 1) then if bget u (k + 2) == bget t (j + 2) then if bget u (k + 3) == bget t (j + 3) then if bget u (k + 4) == bget t (j + 4) then if bget u (k + 5) == bget t (j + 5) then if bget u (k + 6) == bget t (j + 6) then if bget u (k + 7) == bget t (j + 7) then if bget u (k + 8) == bget t (j + 8) then 1 else 0 else 0 else 0 else 0 else 0 else 0 else 0 else 0

def t13 : Nat → Buf → UInt64 → UInt64 → Buf → UInt64 → UInt64
  | 0, u, k, id, t, j => 1
  | n + 1, u, k, id, t, j =>
    if k + 8 < bsize u then
      if bget u k == id then if t14 u k t j == 1 then 1 else t13 n u (k + 9) id t j else t13 n u (k + 9) id t j
    else 0

def t15 (u : Buf) (id : UInt64) (t : Buf) (j : UInt64) : Buf :=
  bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush u id) (bget t (j + 1))) (bget t (j + 2))) (bget t (j + 3))) (bget t (j + 4))) (bget t (j + 5))) (bget t (j + 6))) (bget t (j + 7))) (bget t (j + 8))

def t12 : Nat → Buf → UInt64 → UInt64 → Buf → Buf → UInt64 → UInt64 → UInt64
  | 0, t, i, d, s, u, m, c => 0
  | n + 1, t, i, d, s, u, m, c =>
    if i < bsize t then
      let e := t0 t i;
      if e == 0 then 0
      else if c == 1 then
        if t3 t i e == 1 then
          if bget t e == 18 then
            if bget t (e + 1) == 5 then
              if e + 10 < bsize t then if bget t (e + 10) == 19 then
                t12 n t (e + 11) d (bset s d (m + 1)) (t15 u (m + 1) t (e + 1)) (m + 1) 0
              else 0 else 0
            else
              let (q, o1) := t7 t (e + 1) 1 bnew;
              if q == 0 then 0 else t12 n t (q >>> 2) d (bset s d 0) u (m + 1) 0
          else 0
        else t12 n t e d s u m 1
      else if t2 t i e == 1 then t12 n t e d s u m 1
      else if bget t i == 18 then
        if bget s d == 0 then t12 n t e d s u m 0
        else if bget t e == 5 then
          if e + 9 < bsize t then if bget t (e + 9) == 19 then
            if t13 16777216 u 0 (bget s d) t e == 1 then 0
            else t12 n t (e + 10) d s (t15 u (bget s d) t e) m 0
          else 0 else 0
        else
          let (q, o1) := t7 t e 0 bnew;
          if q == 0 then 0 else t12 n t (q >>> 2) d (bset s d 0) u m 0
      else if bget t i == 6 then t12 n t e (d + 1) (if d + 1 < bsize s then bset s (d + 1) 0 else bpush s 0) u m 0
      else if bget t i == 7 then if d == 0 then 0 else t12 n t e (d - 1) s u m 0
      else if bget t i == 1 then t12 n t e 0 (bset s 0 0) u m 0
      else t12 n t e d s u m 0
    else 1

def t11 : Nat → Buf → UInt64 → UInt64
  | 0, t, i => 0
  | n + 1, t, i => if i < bsize t then if t0 t i == 0 then 0 else if t2 t i (t0 t i) == 1 then 0 else t11 n t (t0 t i) else 1

def t10 (t : Buf) : Buf :=
  if bsize t < 16777216 then
    if t11 16777216 t 0 == 1 then t else
    if t12 16777216 t 0 0 (bpush bnew 0) bnew 0 0 == 0 then bnew else
    let o := t9 16777216 t 0 0 (bpush bnew 0) 0 bnew;
    if bsize o < 16777216 then o else bnew
  else bnew

end C

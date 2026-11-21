/- Nano/Lexer: the lexer for the self-language S (Testing/notes/NANO_V2_CHECKPOINT.md, "S = self-language").
Output Buf: tag bytes; tags: def 1, let 2, UInt64 3, Int64 4, number 5 (+ 8 LE value bytes), ( 6, ) 7, : 8, := 9, + 10, - 11, * 12, ; 13,
ident 14 (+ (1,byte)* + 0), `,` 15, × 16, → 17, | 18, => 19, < 20, == 23, &&& 26, ||| 27, <<< 28, >>> 29 (restricted set: no ≤ ≠ && || Int64; the source itself uses only == and < in conditions, so build_self_S.py needs no desugaring),
[ 30, ] 31, if 32, then 33, else 34, Nat 35, Buf 36, List 37, UInt8 38.  Whitespace = space, newline.  Any other character: output empty.
Internal kinds: 0 reject, 90 skip, 91 end; trivia (SYNTAX_EXP.md): 92 namespace/open/section/end (skip the line), 93 private,
94 dash-dash, 95 slash-dash (nested, to the matching dash-slash; after a doc opener s15 first skips Lean's whitespace),
96 `@[` (names, spaces, commas to the `]`: s14); a 92 line must pass s13 (names, dots, spaces; no word `in`). Tags 39-47: len' rd len put bnew bsize bget bset bpush (= IR prim id + 38). -/
import Nano.Main.Chain
namespace C

def s0 (c : UInt64) : UInt64 :=
  if c < 48 then if c == 39 then 1 else 0
  else if c < 58 then 1
  else if c < 65 then 0
  else if c < 91 then 1
  else if c == 95 then 1
  else if c < 97 then 0
  else if c < 123 then 1
  else 0

def s1 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, p => p
  | n + 1, x, p => if p < len x then if s0 (rd x p) == 1 then s1 n x (p + 1) else p else p

def s2 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, e => 1
  | n + 1, x, i, e => if i < e then if rd x i < 48 then 0 else if 57 < rd x i then 0 else s2 n x (i + 1) e else 1

def s3 (x : List UInt8) (p e : UInt64) : UInt64 :=
  let c := rd x p;
  let d := e - p;
  let r0 := 14;
  let r1 := if d == 4 then if c == 101 then if rd x (p + 1) == 108 then if rd x (p + 2) == 115 then if rd x (p + 3) == 101 then 34 else r0 else r0 else r0 else r0 else r0;
  let r2 := if d == 4 then if c == 116 then if rd x (p + 1) == 104 then if rd x (p + 2) == 101 then if rd x (p + 3) == 110 then 33 else r1 else r1 else r1 else r1 else r1;
  let r3 := if d == 2 then if c == 105 then if rd x (p + 1) == 102 then 32 else r2 else r2 else r2;
  let r4 := if d == 3 then if c == 108 then if rd x (p + 1) == 101 then if rd x (p + 2) == 116 then 2 else r3 else r3 else r3 else r3;
  let r5 := if d == 3 then if c == 100 then if rd x (p + 1) == 101 then if rd x (p + 2) == 102 then 1 else r4 else r4 else r4 else r4;
  let r6 := if d == 4 then if c == 76 then if rd x (p + 1) == 105 then if rd x (p + 2) == 115 then if rd x (p + 3) == 116 then 37 else r5 else r5 else r5 else r5 else r5;
  let r7 := if d == 3 then if c == 66 then if rd x (p + 1) == 117 then if rd x (p + 2) == 102 then 36 else r6 else r6 else r6 else r6;
  let r8 := if d == 3 then if c == 78 then if rd x (p + 1) == 97 then if rd x (p + 2) == 116 then 35 else r7 else r7 else r7 else r7;
  let r9 := if d == 5 then if c == 85 then if rd x (p + 1) == 73 then if rd x (p + 2) == 110 then if rd x (p + 3) == 116 then if rd x (p + 4) == 56 then 38 else r8 else r8 else r8 else r8 else r8 else r8;
  let r10 := if d == 6 then if c == 85 then if rd x (p + 1) == 73 then if rd x (p + 2) == 110 then if rd x (p + 3) == 116 then if rd x (p + 4) == 54 then if rd x (p + 5) == 52 then 3 else r9 else r9 else r9 else r9 else r9 else r9 else r9;
  let r11 := if d == 2 then if c == 114 then if rd x (p + 1) == 100 then 40 else r10 else r10 else r10;
  let r12 := if d == 3 then if c == 108 then if rd x (p + 1) == 101 then if rd x (p + 2) == 110 then 41 else r11 else r11 else r11 else r11;
  let r13 := if d == 4 then if c == 108 then if rd x (p + 1) == 101 then if rd x (p + 2) == 110 then if rd x (p + 3) == 39 then 39 else r12 else r12 else r12 else r12 else r12;
  let r14 := if d == 3 then if c == 112 then if rd x (p + 1) == 117 then if rd x (p + 2) == 116 then 42 else r13 else r13 else r13 else r13;
  let r15 := if d == 4 then if c == 98 then if rd x (p + 1) == 110 then if rd x (p + 2) == 101 then if rd x (p + 3) == 119 then 43 else r14 else r14 else r14 else r14 else r14;
  let r16 := if d == 5 then if c == 98 then if rd x (p + 1) == 115 then if rd x (p + 2) == 105 then if rd x (p + 3) == 122 then if rd x (p + 4) == 101 then 44 else r15 else r15 else r15 else r15 else r15 else r15;
  let r17 := if d == 4 then if c == 98 then if rd x (p + 1) == 103 then if rd x (p + 2) == 101 then if rd x (p + 3) == 116 then 45 else r16 else r16 else r16 else r16 else r16;
  let r18 := if d == 4 then if c == 98 then if rd x (p + 1) == 115 then if rd x (p + 2) == 101 then if rd x (p + 3) == 116 then 46 else r17 else r17 else r17 else r17 else r17;
  let r19 := if d == 5 then if c == 98 then if rd x (p + 1) == 112 then if rd x (p + 2) == 117 then if rd x (p + 3) == 115 then if rd x (p + 4) == 104 then 47 else r18 else r18 else r18 else r18 else r18 else r18;
  let r20 := if d == 3 then if c == 101 then if rd x (p + 1) == 110 then if rd x (p + 2) == 100 then 92 else r19 else r19 else r19 else r19;
  let r21 := if d == 4 then if c == 111 then if rd x (p + 1) == 112 then if rd x (p + 2) == 101 then if rd x (p + 3) == 110 then 92 else r20 else r20 else r20 else r20 else r20;
  let r22 := if d == 7 then if c == 115 then if rd x (p + 1) == 101 then if rd x (p + 2) == 99 then if rd x (p + 3) == 116 then if rd x (p + 4) == 105 then if rd x (p + 5) == 111 then if rd x (p + 6) == 110 then 92 else r21 else r21 else r21 else r21 else r21 else r21 else r21 else r21;
  let r23 := if d == 9 then if c == 110 then if rd x (p + 1) == 97 then if rd x (p + 2) == 109 then if rd x (p + 3) == 101 then if rd x (p + 4) == 115 then if rd x (p + 5) == 112 then if rd x (p + 6) == 97 then if rd x (p + 7) == 99 then if rd x (p + 8) == 101 then 92 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22 else r22;
  let r24 := if d == 7 then if c == 112 then if rd x (p + 1) == 114 then if rd x (p + 2) == 105 then if rd x (p + 3) == 118 then if rd x (p + 4) == 97 then if rd x (p + 5) == 116 then if rd x (p + 6) == 101 then 93 else r23 else r23 else r23 else r23 else r23 else r23 else r23 else r23;
  r24

def s4 (x : List UInt8) (p : UInt64) : UInt64 := if p < len x then
    let c := rd x p;
    let d := rd x (p + 1);
    let f := rd x (p + 2);
    if c == 32 then 90
    else if c == 10 then 90
    else if c == 40 then 6
    else if c == 41 then 7
    else if c == 43 then 10
    else if c == 45 then if d == 45 then 94 else 11
    else if c == 42 then 12
    else if c == 59 then 13
    else if c == 44 then 15
    else if c == 91 then 30
    else if c == 93 then 31
    else if c == 58 then if d == 61 then 9 else 8
    else if c == 61 then if d == 61 then 23 else if d == 62 then 19 else 0
    else if c == 38 then if d == 38 then if f == 38 then 26 else 0 else 0
    else if c == 124 then if d == 124 then if f == 124 then 27 else 18 else 18
    else if c == 60 then if d == 60 then if f == 60 then 28 else 20 else 20
    else if c == 62 then if d == 62 then if f == 62 then 29 else 0 else 0
    else if c == 195 then if d == 151 then 16 else 0
    else if c == 226 then if d == 134 then if f == 146 then 17 else 0 else 0
    else if c == 47 then if d == 45 then 95 else 0
    else if c == 64 then if d == 91 then 96 else 0
    else if c < 48 then if c == 39 then s3 x p (s1 (len' x) x p) else 0
    else if c < 58 then if s2 (len' x) x p (s1 (len' x) x p) == 1 then 5 else 0
    else if s0 c == 1 then s3 x p (s1 (len' x) x p)
    else 0
  else 91

def s5 (x : List UInt8) (p k : UInt64) : UInt64 :=
  if k == 9 then p + 2
  else if k == 16 then p + 2
  else if k == 19 then p + 2
  else if k == 23 then p + 2
  else if k == 17 then p + 3
  else if k == 26 then p + 3
  else if k == 27 then p + 3
  else if k == 28 then p + 3
  else if k == 29 then p + 3
  else if k == 6 then p + 1
  else if k == 7 then p + 1
  else if k == 8 then p + 1
  else if k == 10 then p + 1
  else if k == 11 then p + 1
  else if k == 12 then p + 1
  else if k == 13 then p + 1
  else if k == 15 then p + 1
  else if k == 18 then p + 1
  else if k == 20 then p + 1
  else if k == 30 then p + 1
  else if k == 31 then p + 1
  else if k == 90 then p + 1
  else s1 (len' x) x p

def s6 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, a => a
  | n + 1, x, i, e, a => if i < e then s6 n x (i + 1) e (a * 10 + (rd x i - 48)) else a

def s7 : Nat → List UInt8 → UInt64 → UInt64 → Buf → Buf
  | 0, x, i, e, o => q0 o 0
  | n + 1, x, i, e, o => if i < e then s7 n x (i + 1) e (q0 (q0 o 1) (rd x i)) else q0 o 0

def s8 (v : UInt64) (o : Buf) : Buf := q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48))
    (v >>> 56)

def s11 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, d => 0
  | n + 1, x, i, d => if i < len x then
      if rd x i == 45 then if rd x (i + 1) == 47 then if d == 0 then i + 2 else s11 n x (i + 2) (d - 1) else s11 n x (i + 1) d
      else if rd x i == 47 then if rd x (i + 1) == 45 then s11 n x (i + 2) (d + 1) else s11 n x (i + 1) d
      else s11 n x (i + 1) d
    else 0

def s12 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, b => i
  | n + 1, x, i, b => if i < len x then if rd x i == b then i else s12 n x (i + 1) b else i

def s13 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => 0
  | n + 1, x, i => if i < len x then
      if rd x i == 10 then 1
      else if rd x i == 32 then
        if rd x (i + 1) == 105 then if rd x (i + 2) == 110 then
          if i + 3 < len x then if rd x (i + 3) == 32 then 0 else if rd x (i + 3) == 10 then 0 else s13 n x (i + 1) else 0
        else s13 n x (i + 1) else s13 n x (i + 1)
      else if rd x i == 46 then s13 n x (i + 1)
      else if s0 (rd x i) == 1 then s13 n x (i + 1)
      else 0
    else 1

def s14 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => 0
  | n + 1, x, i => if i < len x then
      if rd x i == 93 then i + 1
      else if rd x i == 32 then s14 n x (i + 1)
      else if rd x i == 44 then s14 n x (i + 1)
      else if s0 (rd x i) == 1 then s14 n x (i + 1)
      else 0
    else 0

def s15 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => 0
  | n + 1, x, i => if i < len x then
      if rd x i == 32 then s15 n x (i + 1)
      else if rd x i == 10 then s15 n x (i + 1)
      else if rd x i == 13 then if rd x (i + 1) == 10 then s15 n x (i + 1) else i
      else if rd x i == 45 then if rd x (i + 1) == 45 then s15 n x (s12 (len' x) x (i + 1) 10) else i
      else if rd x i == 47 then if rd x (i + 1) == 45 then if rd x (i + 2) == 45 then i else if rd x (i + 2) == 33 then i
        else if s11 (len' x) x (i + 2) 0 == 0 then 0 else s15 n x (s11 (len' x) x (i + 2) 0) else i
      else i
    else i

def s9 : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, x, p, o => bnew
  | n + 1, x, p, o =>
    let k := s4 x p;
    if k == 0 then bnew
    else if k == 91 then o
    else if k == 90 then s9 n x (p + 1) o
    else if k == 5 then s9 n x (s5 x p k) (s8 (s6 (len' x) x p (s5 x p k) 0) (q0 o 5))
    else if k == 14 then s9 n x (s5 x p k) (s7 (len' x) x p (s5 x p k) (q0 o 14))
    else if k == 94 then s9 n x (s12 (len' x) x (p + 2) 10) o
    else if k == 92 then if s13 (len' x) x (s5 x p k) == 1 then s9 n x (s12 (len' x) x (s5 x p k) 10) o else bnew
    else if k == 93 then s9 n x (s5 x p k) o
    else if k == 95 then
      let b := if rd x (p + 2) == 45 then s15 (len' x) x (p + 3) else if rd x (p + 2) == 33 then s15 (len' x) x (p + 3) else p + 2;
      if b == 0 then bnew else if s11 (len' x) x b 0 == 0 then bnew else s9 n x (s11 (len' x) x b 0) o
    else if k == 96 then if s14 (len' x) x (p + 2) == 0 then bnew else s9 n x (s14 (len' x) x (p + 2)) o
    else s9 n x (s5 x p k) (q0 o k)

def s10 (x : List UInt8) : Buf := s9 16777216 x 0 bnew

end C

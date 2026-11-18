/- Nano/V2Self/C: the lexer for the self-language S (Testing/notes/NANO_V2_CHECKPOINT.md, "S = self-language").
Output Buf: tag bytes; tags: def 1, let 2, UInt64 3, Int64 4, number 5 (+ 8 LE value bytes), ( 6, ) 7, : 8, := 9, + 10, - 11, * 12, ; 13,
ident 14 (+ (1,byte)* + 0), `,` 15, × 16, → 17, | 18, => 19, < 20, == 23, &&& 26, ||| 27, <<< 28, >>> 29 (restricted set: no ≤ ≠ && || Int64),
[ 30, ] 31, if 32, then 33, else 34, Nat 35, Buf 36, List 37, UInt8 38.  Whitespace = space, newline.  Any other character: output empty.
Internal kinds: 0 reject, 90 skip, 91 end. Tags 39-47: len' rd len put bnew bsize bget bset bpush (= IR prim id + 38). -/
import Nano.V2Self.C.Base
namespace C

def s0 (c : UInt64) : UInt64 := if (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || c == 39 || (48 ≤ c && c ≤ 57) then 1 else 0

def s1 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, p => p
  | n + 1, x, p => if p < len x && s0 (rd x p) == 1 then s1 n x (p + 1) else p

def s2 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, e => 1
  | n + 1, x, i, e => if i < e then if 48 ≤ rd x i && rd x i ≤ 57 then s2 n x (i + 1) e else 0 else 1

def s3 (x : List UInt8) (p e : UInt64) : UInt64 :=
  let c := rd x p;
  let d := e - p;
  let r0 := 14;
  let r1 := if d == 4 && c == 101 && rd x (p + 1) == 108 && rd x (p + 2) == 115 && rd x (p + 3) == 101 then 34 else r0;
  let r2 := if d == 4 && c == 116 && rd x (p + 1) == 104 && rd x (p + 2) == 101 && rd x (p + 3) == 110 then 33 else r1;
  let r3 := if d == 2 && c == 105 && rd x (p + 1) == 102 then 32 else r2;
  let r4 := if d == 3 && c == 108 && rd x (p + 1) == 101 && rd x (p + 2) == 116 then 2 else r3;
  let r5 := if d == 3 && c == 100 && rd x (p + 1) == 101 && rd x (p + 2) == 102 then 1 else r4;
  let r6 := if d == 4 && c == 76 && rd x (p + 1) == 105 && rd x (p + 2) == 115 && rd x (p + 3) == 116 then 37 else r5;
  let r7 := if d == 3 && c == 66 && rd x (p + 1) == 117 && rd x (p + 2) == 102 then 36 else r6;
  let r8 := if d == 3 && c == 78 && rd x (p + 1) == 97 && rd x (p + 2) == 116 then 35 else r7;
  let r10 := if d == 5 && c == 85 && rd x (p + 1) == 73 && rd x (p + 2) == 110 && rd x (p + 3) == 116 && rd x (p + 4) == 56 then 38 else r8;
  let r11 := if d == 6 && c == 85 && rd x (p + 1) == 73 && rd x (p + 2) == 110 && rd x (p + 3) == 116 && rd x (p + 4) == 54 && rd x (p + 5) == 52 then 3 else r10;
  let r12 := if d == 2 && c == 114 && rd x (p + 1) == 100 then 40 else r11;
  let r13 := if d == 3 && c == 108 && rd x (p + 1) == 101 && rd x (p + 2) == 110 then 41 else r12;
  let r14 := if d == 4 && c == 108 && rd x (p + 1) == 101 && rd x (p + 2) == 110 && rd x (p + 3) == 39 then 39 else r13;
  let r15 := if d == 3 && c == 112 && rd x (p + 1) == 117 && rd x (p + 2) == 116 then 42 else r14;
  let r16 := if d == 4 && c == 98 && rd x (p + 1) == 110 && rd x (p + 2) == 101 && rd x (p + 3) == 119 then 43 else r15;
  let r17 := if d == 5 && c == 98 && rd x (p + 1) == 115 && rd x (p + 2) == 105 && rd x (p + 3) == 122 && rd x (p + 4) == 101 then 44 else r16;
  let r18 := if d == 4 && c == 98 && rd x (p + 1) == 103 && rd x (p + 2) == 101 && rd x (p + 3) == 116 then 45 else r17;
  let r19 := if d == 4 && c == 98 && rd x (p + 1) == 115 && rd x (p + 2) == 101 && rd x (p + 3) == 116 then 46 else r18;
  if d == 5 && c == 98 && rd x (p + 1) == 112 && rd x (p + 2) == 117 && rd x (p + 3) == 115 && rd x (p + 4) == 104 then 47 else r19

def s4 (x : List UInt8) (p : UInt64) : UInt64 := if p < len x then
    let c := rd x p;
    let d := rd x (p + 1);
    let f := rd x (p + 2);
    if c == 32 then 90
    else if c == 10 then 90
    else if c == 40 then 6
    else if c == 41 then 7
    else if c == 43 then 10
    else if c == 45 then 11
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
    else if 48 ≤ c && c ≤ 57 then if s2 (len' x) x p (s1 (len' x) x p) == 1 then 5 else 0
    else if s0 c == 1 then s3 x p (s1 (len' x) x p)
    else 0
  else 91

def s5 (x : List UInt8) (p k : UInt64) : UInt64 :=
  if k == 9 || k == 16 || k == 19 || k == 23 then p + 2
  else if k == 17 || k == 26 || k == 27 || k == 28 || k == 29 then p + 3
  else if k == 6 || k == 7 || k == 8 || k == 10 || k == 11 || k == 12 || k == 13 || k == 15 || k == 18 || k == 20 || k == 30 || k == 31 || k == 90 then p + 1
  else s1 (len' x) x p

def s6 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, a => a
  | n + 1, x, i, e, a => if i < e then s6 n x (i + 1) e (a * 10 + (rd x i - 48)) else a

def s7 : Nat → List UInt8 → UInt64 → UInt64 → Buf → Buf
  | 0, x, i, e, o => q0 o 0
  | n + 1, x, i, e, o => if i < e then s7 n x (i + 1) e (q0 (q0 o 1) (rd x i)) else q0 o 0

def s8 (v : UInt64) (o : Buf) : Buf := q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48))
    (v >>> 56)

def s9 : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, x, p, o => bnew
  | n + 1, x, p, o =>
    let k := s4 x p;
    if k == 0 then bnew
    else if k == 91 then o
    else if k == 90 then s9 n x (p + 1) o
    else if k == 5 then s9 n x (s5 x p k) (s8 (s6 (len' x) x p (s5 x p k) 0) (q0 o 5))
    else if k == 14 then s9 n x (s5 x p k) (s7 (len' x) x p (s5 x p k) (q0 o 14))
    else s9 n x (s5 x p k) (q0 o k)

def s10 (x : List UInt8) : Buf := s9 16777216 x 0 bnew

end C

/- Nano/Codegen/JArm: the J → AArch64 TRANSLATOR (E3; PROTOTYPE, UNPROVEN, not part of the proven compiler).
Input: Gen's output (RISC-V code bytes, the J program `encJX`-encoded); output: the native A64 code bytes of the atom
encoding `wordsOf (atomize …)` of Nano/Run/NatImg.lean + NatEnc.lean (the spec), or EMPTY (reject).
* J is read ONLY through the accessor layer `e20` (kind) / `e21` `e22` `e23` (fields A B C) / `e24` (ALU op), so that
  it can later read an explicit IR instead of RISC-V words.  Kinds: 1 addi, 2 slli, 3 srli, 4 ld, 5 sd, 6 sb, 7 lbu,
  8 alu, 9 beq, 10 bne, 11 bltu, 12 bgeu, 13 jal, 14 jalr; 0 = no J instruction (or past the end).
  Fields: addi/slli/srli/ld/lbu d n imm; sd/sb s n off; alu d x y (op in e24); branches x y off; jal rd off; jalr 0 rs.
  Immediates as UInt64 two's complement, branch offsets in J instructions.
* `e35` = `cand` (the atom at J pc i, longest fused form first), atom codes: 1 li, 2 addi, 3 alu, 4 ld, 5 sd,
  6 ldp, 7 ldp (swapped), 8 cj geu, 9 cj ltu, 10 cj eq, 11 lpz, 12 bgeu, 13 beqz, 14 bnez, 15 ldrbx, 16 bgetI,
  17 bsetI, 18 bpushI, 19 align8, 20 jal, 21 jalr, 22 sb.  `e36` its J length, `e37` its side conditions (`NTm.ok`, and
  `li`'s list check), `e39` its jump target, `e40` its A64 words (`NTm.a`).
* Pass 1 (`e46`): atom boundaries, P[q] = 1 + word index of J pc q at every boundary (end included), 0 elsewhere.
  Pass 2 (`e47`): the words, branch offsets from P (here the buffer `z`); every jump target must be a boundary.
Register map = `ArmEnc.armReg`.  Lines are nano (B2 compiles them) and valid Lean. -/
import Nano.Main.Prelude
namespace C

/-! ## constants (`|||`/`&&&` take no bare numerals) -/
def e_0 : UInt64 := 0
def e_1 : UInt64 := 127
def e_2 : UInt64 := 31
def e_3 : UInt64 := 7
def e_4 : UInt64 := 63
def e_5 : UInt64 := 3
def e_6 : UInt64 := 255
def e_7 : UInt64 := 65535
def e_8 : UInt64 := 511
def e_9 : UInt64 := 524287
def e_10 : UInt64 := 67108863
def e_11 : UInt64 := 1
def e_12 : UInt64 := 15
def e_13 : UInt64 := 1023
def e_14 : UInt64 := e_0 - 1

/-! ## RISC-V fields of word v -/
/-- the RV word at word index i (Gen's word buffer) -/
def e0 (c : Buf) (i : UInt64) : UInt64 := bget c i
def e1 (v : UInt64) : UInt64 := v &&& e_1
def e2 (v : UInt64) : UInt64 := (v >>> 7) &&& e_2
def e3 (v : UInt64) : UInt64 := (v >>> 12) &&& e_3
def e4 (v : UInt64) : UInt64 := (v >>> 15) &&& e_2
def e5 (v : UInt64) : UInt64 := (v >>> 20) &&& e_2
/-- sign extension of 12, 13, 21 bit fields -/
def e10 (v : UInt64) : UInt64 := if v < 2048 then v else v - 4096
def e11 (v : UInt64) : UInt64 := if v < 4096 then v else v - 8192
def e12 (v : UInt64) : UInt64 := if v < 1048576 then v else v - 2097152
/-- I-immediate, S-immediate, B-offset (bytes), J-offset (bytes) -/
def e6 (v : UInt64) : UInt64 := e10 (v >>> 20)
def e7 (v : UInt64) : UInt64 := e10 (((v >>> 25) <<< 5) ||| ((v >>> 7) &&& e_2))
def e8 (v : UInt64) : UInt64 :=
  e11 ((((v >>> 31) &&& e_11) <<< 12) ||| (((v >>> 7) &&& e_11) <<< 11) ||| (((v >>> 25) &&& e_4) <<< 5) ||| (((v >>> 8) &&& e_12) <<< 1))
def e9 (v : UInt64) : UInt64 :=
  e12 ((((v >>> 31) &&& e_11) <<< 20) ||| (((v >>> 12) &&& e_6) <<< 12) ||| (((v >>> 20) &&& e_11) <<< 11) ||| (((v >>> 21) &&& e_13) <<< 1))
/-- 1 iff v is negative (two's complement) -/
def e14 (v : UInt64) : UInt64 := if 9223372036854775807 < v then 1 else 0
/-- a byte offset (multiple of 4) in instructions -/
def e13 (v : UInt64) : UInt64 := if e14 v == 1 then e_0 - ((e_0 - v) >>> 2) else v >>> 2
/-- J's ALU op (add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8) of funct3 / funct7, 0 if none -/
def e15 (f3 f7 : UInt64) : UInt64 :=
  if f7 == 0 then
    if f3 == 0 then 1 else if f3 == 7 then 4 else if f3 == 6 then 5 else if f3 == 1 then 6
    else if f3 == 5 then 7 else if f3 == 4 then 8 else 0
  else if f7 == 32 then (if f3 == 0 then 2 else 0)
  else if f7 == 1 then (if f3 == 0 then 3 else 0) else 0

/-! ## the J accessor layer (the only place that reads RISC-V words) -/
/-- the J kind of word v -/
def e25 (v : UInt64) : UInt64 :=
  let p := e1 v;
  let f := e3 v;
  if p == 19 then
    (if f == 0 then 1 else if f == 1 then (if (v >>> 26) == 0 then 2 else 0)
     else if f == 5 then (if (v >>> 26) == 0 then 3 else 0) else 0)
  else if p == 3 then (if f == 3 then 4 else if f == 4 then 7 else 0)
  else if p == 35 then (if f == 3 then 5 else if f == 0 then 6 else 0)
  else if p == 51 then (if e15 f (v >>> 25) == 0 then 0 else 8)
  else if p == 99 then
    (if (e8 v &&& e_5) == 0 then
      (if f == 0 then 9 else if f == 1 then 10 else if f == 6 then 11 else if f == 7 then 12 else 0)
     else 0)
  else if p == 111 then (if (e9 v &&& e_5) == 0 then 13 else 0)
  else if p == 103 then (if f == 0 then (if (v >>> 20) == 0 then (if e2 v == 0 then 14 else 0) else 0) else 0)
  else 0
/-- **J kind** at J pc i of n (0 past the end) -/
def e20 (c : Buf) (n i : UInt64) : UInt64 := if i < n then e25 (e0 c i) else 0
/-- **field A** -/
def e21 (c : Buf) (i : UInt64) : UInt64 :=
  let v := e0 c i;
  let k := e25 v;
  if k == 5 then e5 v else if k == 6 then e5 v else if 8 < k then (if k < 13 then e4 v else e2 v) else e2 v
/-- **field B** -/
def e22 (c : Buf) (i : UInt64) : UInt64 :=
  let v := e0 c i;
  let k := e25 v;
  if 8 < k then (if k < 13 then e5 v else e4 v) else e4 v
/-- **field C** -/
def e23 (c : Buf) (i : UInt64) : UInt64 :=
  let v := e0 c i;
  let k := e25 v;
  if k == 1 then e6 v else if k == 4 then e6 v else if k == 7 then e6 v
  else if k == 2 then (v >>> 20) &&& e_4 else if k == 3 then (v >>> 20) &&& e_4
  else if k == 5 then e7 v else if k == 6 then e7 v
  else if k == 8 then e5 v
  else if k == 13 then e13 (e9 v)
  else if 8 < k then (if k < 13 then e13 (e8 v) else 0) else 0
/-- **ALU op** -/
def e24 (c : Buf) (i : UInt64) : UInt64 := let v := e0 c i; e15 (e3 v) (v >>> 25)

/-! ## matching -/
def e60 (a b : UInt64) : UInt64 := if a == b then 1 else 0
def e61 (a b : UInt64) : UInt64 := if a == b then 0 else 1
/-- 1 iff the J instruction at i is (kind k, A a, B b, C x) -/
def e26 (c : Buf) (n i k a b x : UInt64) : UInt64 :=
  if e20 c n i == k then e60 (e21 c i) a * e60 (e22 c i) b * e60 (e23 c i) x else 0
/-- 1 iff the J instruction at i is `alu op d x y` -/
def e28 (c : Buf) (n i p d x y : UInt64) : UInt64 := e26 c n i 8 d x y * e60 (e24 c i) p
/-- 1 iff i is followed by `jal 0 _` -/
def e29 (c : Buf) (n i : UInt64) : UInt64 := if e20 c n (i + 1) == 13 then e60 (e21 c (i + 1)) 0 else 0

/-! ## li (`liBytes`, `liT`) -/
/-- C as an unsigned byte value (`Int.toNat`: negative ↦ 0) -/
def e30 (v : UInt64) : UInt64 := if e14 v == 1 then 0 else v
/-- `liBytes`: up to k pairs `slli _ _ _; addi _ _ c` from j, acc · 256 + c -/
def e31 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64
  | 0, c, n, j, a => a
  | k + 1, c, n, j, a =>
    if e20 c n j == 2 then (if e20 c n (j + 1) == 1 then e31 k c n (j + 2) (a * 256 + e30 (e23 c (j + 1))) else a) else a
/-- the li value of the atom at i -/
def e32 (c : Buf) (n i : UInt64) : UInt64 := e31 8 c n (i + 1) 0
/-- k pairs `slli d d 8; addi d d byte` from j, bytes from the top of s -/
def e33 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, c, n, j, d, s => 1
  | k + 1, c, n, j, d, s =>
    if e26 c n j 2 d d 8 * e26 c n (j + 1) 1 d d ((s >>> 56) &&& e_6) == 1 then e33 k c n (j + 2) d (s <<< 8) else 0
/-- 1 iff the list at i starts with `liT d v` -/
def e34 (c : Buf) (n i d v : UInt64) : UInt64 :=
  if v < 2048 then e26 c n i 1 d 0 v else e26 c n i 1 d 0 0 * e33 8 c n (i + 1) d v

/-! ## atoms -/
/-- **`cand`**: the atom code at J pc i (0: none) -/
def e35 (c : Buf) (n i : UInt64) : UInt64 :=
  let k := e20 c n i;
  let k2 := e20 c n (i + 1);
  if k == 1 then
    (if e22 c i == 0 then
      (if k2 == 2 then (if e23 c (i + 1) == 8 then
        (if e60 (e21 c (i + 1)) (e21 c i) * e60 (e22 c (i + 1)) (e21 c i) == 1 then 1 else 2) else 2) else 2)
     else 2)
  else if k == 4 then
    (if k2 == 4 then
      (if e23 c i == 0 then
        (if e23 c (i + 1) == 8 then
          (if e60 (e22 c i) (e22 c (i + 1)) * e61 (e21 c i) (e21 c (i + 1)) * e61 (e21 c i) (e22 c i)
              * e61 (e21 c (i + 1)) (e22 c i) == 1 then 6 else 4) else 4)
       else if e23 c i == 8 then
        (if e23 c (i + 1) == 0 then
          (if e60 (e22 c i) (e22 c (i + 1)) * e61 (e21 c i) (e21 c (i + 1)) * e61 (e21 c i) (e22 c i)
              * e61 (e21 c (i + 1)) (e22 c i) == 1 then 7 else 4) else 4)
       else 4)
     else 4)
  else if k == 5 then 5
  else if k == 12 then (if e23 c i == 2 then (if e29 c n i == 1 then 8 else 12) else 12)
  else if k == 11 then (if e23 c i == 2 then (if e29 c n i == 1 then 9 else 0) else 0)
  else if k == 9 then
    (if e23 c i == 2 then
      (if e29 c n i == 1 then (if e22 c i == 0 then 11 else 10) else (if e22 c i == 0 then 13 else 0))
     else (if e22 c i == 0 then 13 else 0))
  else if k == 10 then (if e22 c i == 0 then 14 else 0)
  else if k == 8 then
    (if e24 c i == 1 then
      (if k2 == 7 then (if e23 c (i + 1) == 0 then
        (if e60 (e21 c (i + 1)) (e21 c i) * e60 (e22 c (i + 1)) (e21 c i) == 1 then 15 else 3) else 3) else 3)
     else 3)
  else if k == 2 then
    (if e26 c n i 2 15 7 3 * e28 c n (i + 1) 1 15 15 5 == 1 then 18 else 16)
  else if k == 3 then
    (if e23 c i == 3 then (if k2 == 2 then (if e23 c (i + 1) == 3 then
      (if e60 (e21 c (i + 1)) (e21 c i) * e60 (e22 c (i + 1)) (e21 c i) == 1 then 19 else 0) else 0) else 0) else 0)
  else if k == 13 then 20
  else if k == 14 then 21
  else if k == 6 then (if e23 c i == 0 then 22 else 0)
  else 0
/-- the J length of atom t at i -/
def e36 (c : Buf) (n i t : UInt64) : UInt64 :=
  if t == 1 then (if e32 c n i < 2048 then 1 else 17)
  else if t == 16 then 1
  else if t == 6 then 2 else if t == 7 then 2 else if t == 8 then 2 else if t == 9 then 2 else if t == 10 then 2
  else if t == 11 then 2 else if t == 15 then 2 else if t == 18 then 2 else if t == 19 then 2 else 1
/-- the A64 register of J register r (`armReg`; 18 outside the map) -/
def e42 (r : UInt64) : UInt64 :=
  if r == 0 then 31 else if r == 1 then 30 else if r == 2 then 4 else if r == 10 then 0 else if r == 11 then 1
  else if r == 12 then 2 else if r == 13 then 3 else if r == 28 then 12 else if r == 29 then 13
  else if r == 30 then 10 else if r == 31 then 11 else if r == 5 then 5 else if r == 6 then 6
  else if r == 7 then 7 else if r == 8 then 8 else if r == 14 then 14 else if r == 15 then 15 else 18
/-- `mapped r` -/
def e38 (r : UInt64) : UInt64 := if e42 r == 18 then 0 else 1
/-- `mr r`: mapped, not x0 -/
def e39 (r : UInt64) : UInt64 := if r == 0 then 0 else e38 r
/-- the offset condition of ld / sd: `0 ≤ off → off % 8 = 0` -/
def e41 (f : UInt64) : UInt64 := if e14 f == 1 then 1 else e60 (f &&& e_3) 0
/-- **`NTm.ok`** (plus li's list check) of atom t at i -/
def e37 (c : Buf) (n i t : UInt64) : UInt64 :=
  let a := e21 c i;
  let b := e22 c i;
  let x := e23 c i;
  if t == 1 then
    (if a == 5 then e34 c n i a (e32 c n i) else if a == 6 then e34 c n i a (e32 c n i)
     else if a == 7 then e34 c n i a (e32 c n i) else 0)
  else if t == 2 then e39 a * e38 b
  else if t == 3 then e39 a * e39 b * e39 x
  else if t == 4 then e39 a * e39 b * e41 x
  else if t == 5 then e38 a * e39 b * e41 x
  else if t == 6 then e39 a * e39 (e21 c (i + 1)) * e39 b
  else if t == 7 then e39 a * e39 (e21 c (i + 1)) * e39 b
  else if t < 11 then e39 a * e39 b
  else if t == 12 then e39 a * e39 b
  else if t < 15 then e39 a
  else if t == 15 then e39 a * e39 b * e39 x
  else if t == 16 then e39 a * e39 b * (if x == 0 then 0 else if x < 64 then 1 else 0)
  else if t == 18 then 1
  else if t == 19 then e39 a * e39 b
  else if t == 20 then (if a < 2 then 1 else 0)
  else if t == 21 then (if b == 1 then 1 else e60 b 14)
  else if t == 22 then e39 a * e39 b
  else 0
/-- the J pc atom t at i jumps to, raw (no wrap check) -/
def e43 (c : Buf) (n i t : UInt64) : UInt64 :=
  if t == 8 then i + 1 + e23 c (i + 1) else if t == 9 then i + 1 + e23 c (i + 1)
  else if t == 10 then i + 1 + e23 c (i + 1) else if t == 11 then i + 1 + e23 c (i + 1)
  else if t == 12 then i + e23 c i else if t == 13 then i + e23 c i else if t == 14 then i + e23 c i
  else if t == 20 then i + e23 c i else e_0
/-- a negative J pc as 0 (`Int.toNat`) -/
def e66 (v : UInt64) : UInt64 := if e14 v == 1 then 0 else v
/-- `jt`: the J pc atom t at i jumps to (`tg`), e_14 if none -/
def e65 (c : Buf) (n i t : UInt64) : UInt64 :=
  if t < 8 then e_14 else if t < 15 then e66 (e43 c n i t) else if t == 20 then e66 (e43 c n i t) else e_14

/-! ## A64 words (64-bit forms) -/
/-- c ||| v << 10 ||| n << 5 ||| d (add/sub imm, uimm ldr/str, strb) -/
def e50 (c d n v : UInt64) : UInt64 := c ||| (v <<< 10) ||| (n <<< 5) ||| d
/-- three registers, base c -/
def e51 (c d n m : UInt64) : UInt64 := c ||| (m <<< 16) ||| (n <<< 5) ||| d
/-- movz / movk / movn d, #v, lsl 16j -/
def e52 (c d v j : UInt64) : UInt64 := c ||| (j <<< 21) ||| (v <<< 5) ||| d
/-- b.cond-form (b.cond c / cbz / cbnz) with word offset f -/
def e53 (c f : UInt64) : UInt64 := c ||| ((f &&& e_9) <<< 5)
/-- the number of 16-bit chunks of v equal to e -/
def e54 (v e : UInt64) : UInt64 :=
  (if (v &&& e_7) == e then 1 else 0) + (if ((v >>> 16) &&& e_7) == e then 1 else 0)
  + (if ((v >>> 32) &&& e_7) == e then 1 else 0) + (if ((v >>> 48) &&& e_7) == e then 1 else 0)
/-- `walk0` / `chain`: chunks j.. of v (shifted right 16j) that differ from e; f = 1 once the first word is out -/
def e55 : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Buf
  | 0, o, d, v, j, e, f => o
  | k + 1, o, d, v, j, e, f =>
    let x := v &&& e_7;
    if x == e then e55 k o d (v >>> 16) (j + 1) e f else
    if f == 1 then e55 k (bpush o (e52 4068474880 d x j)) d (v >>> 16) (j + 1) e 1 else
    if e == 0 then e55 k (bpush o (e52 3531603968 d x j)) d (v >>> 16) (j + 1) e 1 else
    e55 k (bpush o (e52 2457862144 d (65535 - x) j)) d (v >>> 16) (j + 1) e 1
/-- `liL d v` -/
def e56 (o : Buf) (d v : UInt64) : Buf :=
  if v < 65536 then bpush o (e52 3531603968 d v 0) else
  if (e_14 - v) < 65536 then bpush o (e52 2457862144 d (e_14 - v) 0) else
  if e54 v 0 < e54 v 65535 then e55 4 o d v 0 65535 0 else e55 4 o d v 0 0 0
/-- ldur / stur (base c) t, [n, #f], f signed 9 bit -/
def e62 (c t n f : UInt64) : UInt64 := c ||| ((f &&& e_8) <<< 12) ||| (n <<< 5) ||| t
/-- b / bl (base c), word offset f -/
def e63 (c f : UInt64) : UInt64 := c ||| (f &&& e_10)
/-- `memW`: 8-byte load (s = 0) / store (s = 1) of raw register t at [n + f] -/
def e57 (o : Buf) (s t n f : UInt64) : Buf :=
  if f < 32768 then
    (if (f &&& e_3) == 0 then bpush o (e50 (if s == 0 then 4181721088 else 4177526784) t n (f >>> 3))
     else bpush (bpush o (e50 3506438144 16 n (0 - f))) (e50 (if s == 0 then 4181721088 else 4177526784) t 16 0))
  else if f + 256 < 256 then bpush o (e62 (if s == 0 then 4164943872 else 4160749568) t n f)
  else bpush (bpush o (e50 3506438144 16 n (0 - f))) (e50 (if s == 0 then 4181721088 else 4177526784) t 16 0)
/-- the ALU base of op p (`aluC`) -/
def e58 (p : UInt64) : UInt64 :=
  if p == 1 then 2332033024 else if p == 2 then 3405774848 else if p == 3 then 2600485888
  else if p == 4 then 2315255808 else if p == 5 then 2852126720 else if p == 6 then 2596282368
  else if p == 7 then 2596283392 else 3388997632
/-- the word index of J pc t (P[t] − 1; 0 if no boundary) -/
def e59 (z : Buf) (t : UInt64) : UInt64 := if t < bsize z then (if bget z t == 0 then 0 else bget z t - 1) else 0
/-- **`NTm.a`**: the words of atom t at J pc i (word index h = bsize o) -/
def e40 (c : Buf) (n : UInt64) (z o : Buf) (i t : UInt64) : Buf :=
  let h := bsize o;
  let a := e42 (e21 c i);
  let b := e42 (e22 c i);
  let x := e23 c i;
  let g := e59 z (e65 c n i t);
  if t == 1 then e56 o a (e32 c n i)
  else if t == 2 then
    (if e22 c i == 0 then e56 o a x
     else if e14 x == 1 then bpush o (e50 3506438144 a b (0 - x)) else bpush o (e50 2432696320 a b x))
  else if t == 3 then
    (if e24 c i == 3 then bpush (bpush o (e52 3531603968 17 0 0)) (e51 2600485888 a b (e42 x))
     else bpush o (e51 (e58 (e24 c i)) a b (e42 x)))
  else if t == 4 then e57 o 0 a b x
  else if t == 5 then (if e21 c i == 0 then e57 (bpush o (e52 3531603968 17 0 0)) 1 17 b x else e57 o 1 a b x)
  else if t == 6 then bpush o (e50 2839543808 a b (e42 (e21 c (i + 1))))
  else if t == 7 then bpush o (e50 2839543808 (e42 (e21 c (i + 1))) b a)
  else if t == 8 then bpush (bpush o (e51 3942645760 16 a b)) (e53 1409286147 (g - (h + 1)))
  else if t == 9 then bpush (bpush o (e51 3942645760 16 a b)) (e53 1409286146 (g - (h + 1)))
  else if t == 10 then bpush (bpush o (e51 3942645760 16 a b)) (e53 1409286145 (g - (h + 1)))
  else if t == 12 then bpush (bpush o (e51 3942645760 16 a b)) (e53 1409286146 (g - (h + 1)))
  else if t == 11 then bpush o (e53 3036676096 (g - h) ||| a)
  else if t == 14 then bpush o (e53 3036676096 (g - h) ||| a)
  else if t == 13 then bpush o (e53 3019898880 (g - h) ||| a)
  else if t == 20 then bpush o (e63 (if e21 c i == 0 then 335544320 else 2483027968) (g - h))
  else if t == 21 then bpush o (e50 3592355840 0 b 0)
  else if t == 15 then bpush o (e51 945842176 a b (e42 x))
  else if t == 16 then bpush o (e50 3544186880 a b (63 - x) ||| (((64 - x) &&& e_4) <<< 16))
  else if t == 18 then bpush o (e51 2332036096 15 5 7)
  else if t == 19 then bpush (bpush (bpush o (e52 3531603968 16 3 0)) (e51 2596283392 a b 16)) (e51 2596282368 a a 16)
  else bpush o (e50 956301312 a b 0)

/-! ## the two passes -/
/-- n + 1 zero words -/
def e44 : Nat → Buf → UInt64 → Buf
  | 0, z, n => z
  | k + 1, z, n => if bsize z < n + 1 then e44 k (bpush z 0) n else z
/-- **pass 1**: boundaries; EMPTY z on reject -/
def e46 : Nat → Buf → UInt64 → UInt64 → Buf → Buf → Buf × Buf
  | 0, c, n, i, z, o => (bnew, o)
  | k + 1, c, n, i, z, o =>
    if i < n then
      let t := e35 c n i;
      if t == 0 then (bnew, o) else
      if e37 c n i t == 0 then (bnew, o) else
      let z1 := bset z i (bsize o + 1);
      let o1 := e40 c n z1 o i t;
      e46 k c n (i + e36 c n i t) z1 o1
    else if i == n then (if bsize o < 262144 then (bset z n (bsize o + 1), o) else (bnew, o)) else (bnew, o)
/-- 1 iff the jump target of atom t at i is a boundary (or there is none) -/
def e48 (c : Buf) (n : UInt64) (z : Buf) (i t : UInt64) : UInt64 :=
  let g := e65 c n i t;
  if g == e_14 then 1 else if g < n + 1 then e61 (bget z g) 0 else 0
/-- **pass 2**: the words; EMPTY on reject -/
def e47 : Nat → Buf → UInt64 → Buf → UInt64 → Buf → Buf
  | 0, c, n, z, i, o => bnew
  | k + 1, c, n, z, i, o =>
    if i < n then
      let t := e35 c n i;
      if e48 c n z i t == 0 then bnew else
      let o1 := e40 c n z o i t;
      e47 k c n z (i + e36 c n i t) o1
    else o
/-- the words as bytes, little-endian -/
def e49 : Nat → List UInt8 → Buf → UInt64 → List UInt8 → List UInt8
  | 0, c, w, i, o => o
  | k + 1, c, w, i, o =>
    if i < bsize w then
      let v := bget w i;
      e49 k c w (i + 1) (put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24))
    else o
/-- the RV words of code bytes (little-endian) -/
def e68 : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, c, i, w => w
  | k + 1, c, i, w =>
    if i + 3 < len c then
      e68 k c (i + 4) (bpush w ((rd c i) ||| ((rd c (i + 1)) <<< 8) ||| ((rd c (i + 2)) <<< 16) ||| ((rd c (i + 3)) <<< 24)))
    else w
/-- **the translator**: Gen's RISC-V words → native A64 words, or EMPTY -/
def e64 (c : Buf) : Buf :=
  let n := bsize c;
  if n == 0 then bnew else if 262144 < n then bnew else
  let (z, o) := e46 16777216 c n 0 (e44 16777216 bnew n) bnew;
  if bsize z == 0 then bnew else e47 16777216 c n z 0 bnew
/-- the translator on code bytes (stand-alone program: input = Gen's output) -/
def e45 (c : List UInt8) : List UInt8 :=
  if (len c &&& e_5) == 0 then
    let w := e64 (e68 (len' c) c 0 bnew);
    if bsize w == 0 then [] else e49 (len' c) c w 0 []
  else []

end C

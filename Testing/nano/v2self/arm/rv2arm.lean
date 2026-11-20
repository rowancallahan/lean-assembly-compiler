-- rv2arm (nano): RISC-V code bytes as C emits them (J programs, RvEnc.encJX) -> AArch64 code bytes. UNPROVEN GLUE.
-- Lines starting with -- are removed before B2 compiles this file (grep -v '^--'); the rest is nano and valid Lean.
-- Input: a 4-byte little-endian chunk index c, then the RV code. Output: the A64 blocks (4 words each) of RV words
-- z0*c .. z0*c + z0 - 1 (z0 = CHUNK_WORDS below). rv2arm.sh runs all chunks. Any word outside the J encodings, or out of range: EMPTY output.
-- Register map, block table and proof notes: PROOF_NOTES.md. Test oracle: rv2arm.py (same bytes).
--
-- CHUNK_WORDS = z0: RV words translated per call. A nano List holds < 2^19 elements, and every RV word gives 16
-- output bytes, so one call can take at most 2^19 / 16 = 32768 words; 32000 leaves a margin. rv2arm.sh reads this
-- line (keep the form `def z0 : UInt64 := N`).
def z0 : UInt64 := 32000
--
-- u0: RV register -> A64 register (0 -> xzr 31, only in ALU/compare operands; 2 (sp) -> x4; unknown -> 99)
def u0 (r : UInt64) : UInt64 :=
  if r == 0 then 31 else if r == 1 then 30 else if r == 2 then 4 else if r == 10 then 0 else if r == 11 then 1
  else if r == 12 then 2 else if r == 13 then 3 else if r == 28 then 12 else if r == 29 then 13
  else if r == 30 then 10 else if r == 31 then 11 else if r == 5 then 5 else if r == 6 then 6
  else if r == 7 then 7 else if r == 8 then 8 else if r == 14 then 14 else if r == 15 then 15 else 99
-- u2: 1 iff RV register r is mapped (x0 included)
def u2 (r : UInt64) : UInt64 := if u0 r < 32 then 1 else 0
-- sign extension of 12, 13, 21 bit fields (two's complement in UInt64); u7: 1 iff negative; u8: absolute value
def u4 (v : UInt64) : UInt64 := if v < 2048 then v else v - 4096
def u5 (v : UInt64) : UInt64 := if v < 4096 then v else v - 8192
def u6 (v : UInt64) : UInt64 := if v < 1048576 then v else v - 2097152
def u7 (v : UInt64) : UInt64 := if 9223372036854775807 < v then 1 else 0
def u8 (v : UInt64) : UInt64 := if u7 v == 1 then 0 - v else v
-- the RV word at word index i (little-endian; the input starts with a 4-byte chunk index, then the code)
def w (x : List UInt8) (i : UInt64) : UInt64 :=
  (rd x (4 * i + 4)) ||| ((rd x (4 * i + 5)) <<< 8) ||| ((rd x (4 * i + 6)) <<< 16) ||| ((rd x (4 * i + 7)) <<< 24)
-- RV fields: opcode, rd, funct3, rs1, rs2, I-immediate, S-immediate, B-offset (bytes), J-offset (bytes)
def o0 (v : UInt64) : UInt64 := v &&& 127
def o1 (v : UInt64) : UInt64 := (v >>> 7) &&& 31
def o2 (v : UInt64) : UInt64 := (v >>> 12) &&& 7
def o3 (v : UInt64) : UInt64 := (v >>> 15) &&& 31
def o4 (v : UInt64) : UInt64 := (v >>> 20) &&& 31
def o5 (v : UInt64) : UInt64 := u4 (v >>> 20)
def o6 (v : UInt64) : UInt64 := u4 (((v >>> 25) <<< 5) ||| ((v >>> 7) &&& 31))
def o7 (v : UInt64) : UInt64 :=
  u5 ((((v >>> 31) &&& 1) <<< 12) ||| (((v >>> 7) &&& 1) <<< 11) ||| (((v >>> 25) &&& 63) <<< 5) ||| (((v >>> 8) &&& 15) <<< 1))
def o8 (v : UInt64) : UInt64 :=
  u6 ((((v >>> 31) &&& 1) <<< 20) ||| (((v >>> 12) &&& 255) <<< 12) ||| (((v >>> 20) &&& 1) <<< 11) ||| (((v >>> 21) &&& 1023) <<< 1))
-- A64 base words (constants: a leading literal would elaborate as Nat in Lean)
def k1 : UInt64 := 3531603968
def k2 : UInt64 := 2432696320
def k3 : UInt64 := 3506438144
def k4 : UInt64 := 3942645760
def k5 : UInt64 := 1409286144
def k6 : UInt64 := 3592355840
def k7 : UInt64 := 4181721088
def k8 : UInt64 := 4177526784
def k15 : UInt64 := 4068474880
def k16 : UInt64 := 3019898880
def k17 : UInt64 := 2097152
def k11 : UInt64 := 960495616
def k12 : UInt64 := 956301312
def k13 : UInt64 := 2596282368
def k14 : UInt64 := 2596283392
-- A64 encoders (64-bit forms). a0 movz; a1 add imm; a2 sub imm; a3 register form (base op); a4 subs x16, n, b
def a0 (d i : UInt64) : UInt64 := k1 ||| (i <<< 5) ||| d
def a1 (d n i : UInt64) : UInt64 := k2 ||| (i <<< 10) ||| (n <<< 5) ||| d
def a2 (d n i : UInt64) : UInt64 := k3 ||| (i <<< 10) ||| (n <<< 5) ||| d
def a3 (c d n b : UInt64) : UInt64 := c ||| (b <<< 16) ||| (n <<< 5) ||| d
def a4 (n b : UInt64) : UInt64 := k4 ||| (b <<< 16) ||| (n <<< 5) ||| 16
-- a5 ldr/str (unsigned offset /8) base c; a7 ldrb/strb base c
def a5 (c t n f : UInt64) : UInt64 := c ||| ((f >>> 3) <<< 10) ||| (n <<< 5) ||| t
def a7 (c t n f : UInt64) : UInt64 := c ||| (f <<< 10) ||| (n <<< 5) ||| t
-- a8 b/bl (base c, word offset f); a9 b.cond; b0 br
def a8 (c f : UInt64) : UInt64 := c ||| (f &&& 67108863)
def a9 (c f : UInt64) : UInt64 := k5 ||| ((f &&& 524287) <<< 5) ||| c
def b0 (n : UInt64) : UInt64 := k6 ||| (n <<< 5)
-- b4 movk d, #i, lsl 16h; b5 cbz t, f
def b4 (d i h : UInt64) : UInt64 := k15 ||| (h * k17) ||| (i <<< 5) ||| d
def b5 (t f : UInt64) : UInt64 := k16 ||| ((f &&& 524287) <<< 5) ||| t
-- the padding word: add x16, x16, #0
def k0 : UInt64 := 2432696848
-- ALU op number (Gen's BIN: add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8) of an R-type word, 0 if none
def b1 (f3 f7 : UInt64) : UInt64 :=
  if f7 == 0 then
    if f3 == 0 then 1 else if f3 == 7 then 4 else if f3 == 6 then 5 else if f3 == 1 then 6
    else if f3 == 5 then 7 else if f3 == 4 then 8 else 0
  else if f7 == 32 then (if f3 == 0 then 2 else 0)
  else if f7 == 1 then (if f3 == 0 then 3 else 0) else 0
-- the A64 register-form base of ALU op c
def b2 (c : UInt64) : UInt64 :=
  if c == 1 then 2332033024 else if c == 2 then 3405774848 else if c == 3 then 2600485888
  else if c == 4 then 2315255808 else if c == 5 then 2852126720 else if c == 6 then 2596282368
  else if c == 7 then 2596283392 else 3388997632
-- b.cond condition of an RV branch funct3 (beq 0 -> eq 0, bne 1 -> ne 1, bltu 6 -> lo 3, bgeu 7 -> hs 2), 99 if none
def b3 (f3 : UInt64) : UInt64 :=
  if f3 == 0 then 0 else if f3 == 1 then 1 else if f3 == 6 then 3 else if f3 == 7 then 2 else 99
--
-- VALIDATION: 1 iff word v at index i (of n words) is a J encoding that the blocks handle
def c0 (v i n : UInt64) : UInt64 :=
  let p := o0 v;
  let f := o2 v;
  if p == 19 then
    if f == 0 then (if u2 (o3 v) == 1 then u2 (o1 v) else 0)
    else if f == 1 then (if (v >>> 26) == 0 then (if u2 (o3 v) == 1 then u2 (o1 v) else 0) else 0)
    else if f == 5 then (if (v >>> 26) == 0 then (if u2 (o3 v) == 1 then u2 (o1 v) else 0) else 0)
    else 0
  else if p == 3 then
    if o3 v == 0 then 0 else
    if u2 (o3 v) == 0 then 0 else
    if f == 3 then u2 (o1 v) else if f == 4 then u2 (o1 v) else 0
  else if p == 35 then
    if o3 v == 0 then 0 else
    if u2 (o3 v) == 0 then 0 else
    if f == 3 then u2 (o4 v) else if f == 0 then u2 (o4 v) else 0
  else if p == 51 then
    if b1 f (v >>> 25) == 0 then 0 else
    if u2 (o3 v) == 0 then 0 else
    if u2 (o4 v) == 0 then 0 else u2 (o1 v)
  else if p == 99 then
    if b3 f == 99 then 0 else
    if u2 (o3 v) == 0 then 0 else
    if u2 (o4 v) == 0 then 0 else
    if (o7 v &&& 3) == 0 then
      (if (o7 v) + 262140 < 524281 then (if 4 * i + o7 v < 4 * n then 1 else 0) else 0)
    else 0
  else if p == 111 then
    if o1 v < 2 then
      (if (o8 v &&& 3) == 0 then (if 4 * i + o8 v < 4 * n then 1 else 0) else 0)
    else 0
  else if p == 103 then
    if f == 0 then
      (if (v >>> 20) == 0 then (if o1 v == 0 then (if u0 (o3 v) < 31 then 1 else 0) else 0) else 0)
    else 0
  else 0
-- 1 iff all n words are valid (fuel: one step per word)
def c1 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, n => 1
  | k + 1, x, i, n =>
    if i < n then (if c0 (w x i) i n == 1 then c1 k x (i + 1) n else 0) else 1
--
-- EMISSION: q puts one word (4 bytes, little-endian); e0..e4 put a block of 0..4 words plus padding
def q (x : List UInt8) (o : List UInt8) (v : UInt64) : List UInt8 :=
  put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24)
def e0 (x : List UInt8) (o : List UInt8) : List UInt8 := q x (q x (q x (q x o k0) k0) k0) k0
def e1 (x : List UInt8) (o : List UInt8) (a : UInt64) : List UInt8 := q x (q x (q x (q x o a) k0) k0) k0
def e2 (x : List UInt8) (o : List UInt8) (a b : UInt64) : List UInt8 := q x (q x (q x (q x o a) b) k0) k0
def e3 (x : List UInt8) (o : List UInt8) (a b c : UInt64) : List UInt8 := q x (q x (q x (q x o a) b) c) k0
def e4 (x : List UInt8) (o : List UInt8) (a b c d : UInt64) : List UInt8 := q x (q x (q x (q x o a) b) c) d
-- J addi rd rs imm
def d0 (x : List UInt8) (o : List UInt8) (v : UInt64) : List UInt8 :=
  let r := o1 v;
  let s := o3 v;
  let i := o5 v;
  if r == 0 then e0 x o else
  if s == 0 then
    (if u7 i == 1 then e4 x o (a0 (u0 r) (65536 - u8 i)) (b4 (u0 r) 65535 1) (b4 (u0 r) 65535 2) (b4 (u0 r) 65535 3)
     else e1 x o (a0 (u0 r) i))
  else if u7 i == 1 then e1 x o (a2 (u0 r) (u0 s) (u8 i)) else e1 x o (a1 (u0 r) (u0 s) i)
-- the address rs+f in x16 (add/sub imm)
def d1 (s f : UInt64) : UInt64 := if u7 f == 1 then a2 16 (u0 s) (u8 f) else a1 16 (u0 s) f
-- the data register of a load/store: x17 for a store of x0 (zeroed first: xzr is never stored)
def y0 (t : UInt64) : UInt64 := if t == 0 then 17 else u0 t
-- emit w1 (and w2), after `movz x17, #0` when t = x0
def y1 (x : List UInt8) (o : List UInt8) (t w1 : UInt64) : List UInt8 :=
  if t == 0 then e2 x o (a0 17 0) w1 else e1 x o w1
def y2 (x : List UInt8) (o : List UInt8) (t w1 w2 : UInt64) : List UInt8 :=
  if t == 0 then e3 x o (a0 17 0) w1 w2 else e2 x o w1 w2
-- J ld / sd (c = 1 load, 0 store): ldr/str [xs,#f] if f in 8N and < 32768, else add/sub x16 + [x16]
def d2 (x : List UInt8) (o : List UInt8) (c t s f : UInt64) : List UInt8 :=
  let g := (if c == 1 then k7 else k8);
  if (f &&& 7) == 0 then
    (if f < 32768 then y1 x o t (a5 g (y0 t) (u0 s) f) else y2 x o t (d1 s f) (a5 g (y0 t) 16 0))
  else y2 x o t (d1 s f) (a5 g (y0 t) 16 0)
-- J lbu / sb (c = 1 load, 0 store): ldrb/strb [xs,#f] if 0 <= f < 4096, else via x16
def d3 (x : List UInt8) (o : List UInt8) (c t s f : UInt64) : List UInt8 :=
  let g := (if c == 1 then k11 else k12);
  if f < 4096 then y1 x o t (a7 g (y0 t) (u0 s) f) else y2 x o t (d1 s f) (a7 g (y0 t) 16 0)
-- an operand register: x0 is x17, which the block zeroes first (`movz x17, #0`); register 31 is never emitted
def z1 (r : UInt64) : UInt64 := if r == 0 then 17 else u0 r
-- J alu op rd a b (mul = madd d, a, b, x17 with x17 = 0)
def d6 (x : List UInt8) (o : List UInt8) (v : UInt64) : List UInt8 :=
  let r := o1 v;
  let a := o3 v;
  let b := o4 v;
  let p := b1 (o2 v) (v >>> 25);
  let w1 := a3 (b2 p) (u0 r) (z1 a) (z1 b);
  if r == 0 then e0 x o else
  if a == 0 then e2 x o (a0 17 0) w1 else
  if b == 0 then e2 x o (a0 17 0) w1 else
  if p == 3 then e2 x o (a0 17 0) w1 else e1 x o w1
-- J slli / srli rd rs sh (c = 1 left): movz x16,#sh; lslv/lsrv xd, xs, x16
def d7 (x : List UInt8) (o : List UInt8) (v c : UInt64) : List UInt8 :=
  let r := o1 v;
  let s := o3 v;
  let g := (if c == 1 then k13 else k14);
  if r == 0 then e0 x o else
  if s == 0 then e3 x o (a0 17 0) (a0 16 ((v >>> 20) &&& 63)) (a3 g (u0 r) 17 16)
  else e2 x o (a0 16 ((v >>> 20) &&& 63)) (a3 g (u0 r) (u0 s) 16)
-- compare-branch: subs x16, a, b; b.cond c (B - 1), after `movz x17, #0` (then B - 2) if an operand is x0
def d9 (x : List UInt8) (o : List UInt8) (a b c f : UInt64) : List UInt8 :=
  if a == 0 then e3 x o (a0 17 0) (a4 (z1 a) (z1 b)) (a9 c (f - 2)) else
  if b == 0 then e3 x o (a0 17 0) (a4 (z1 a) (z1 b)) (a9 c (f - 2)) else
  e2 x o (a4 (u0 a) (u0 b)) (a9 c (f - 1))
-- J beq/bne/bltu/bgeu a b B. beq against x0: cbz (B); beq x0 x0: b (B)
def d8 (x : List UInt8) (o : List UInt8) (v : UInt64) : List UInt8 :=
  let a := o3 v;
  let b := o4 v;
  if o2 v == 0 then
    (if a == 0 then (if b == 0 then e1 x o (a8 335544320 (o7 v)) else e1 x o (b5 (u0 b) (o7 v)))
     else if b == 0 then e1 x o (b5 (u0 a) (o7 v))
     else d9 x o a b 0 (o7 v))
  else d9 x o a b (b3 (o2 v)) (o7 v)
-- one block for the RV word v (already validated)
def t0 (x : List UInt8) (o : List UInt8) (v : UInt64) : List UInt8 :=
  let p := o0 v;
  let f := o2 v;
  if p == 19 then (if f == 0 then d0 x o v else if f == 1 then d7 x o v 1 else d7 x o v 0)
  else if p == 3 then
    (if o1 v == 0 then e0 x o else if f == 3 then d2 x o 1 (o1 v) (o3 v) (o5 v) else d3 x o 1 (o1 v) (o3 v) (o5 v))
  else if p == 35 then
    (if f == 3 then d2 x o 0 (o4 v) (o3 v) (o6 v) else d3 x o 0 (o4 v) (o3 v) (o6 v))
  else if p == 51 then d6 x o v
  else if p == 99 then d8 x o v
  else if p == 111 then
    (if o1 v == 0 then e1 x o (a8 335544320 (o8 v)) else e4 x o k0 k0 k0 (a8 2483027968 (o8 v - 3)))
  else e1 x o (b0 (u0 (o3 v)))
-- emit the blocks of words i .. e-1
def l0 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, e, n, o => o
  | k + 1, x, i, e, n, o =>
    if i < e then l0 k x (i + 1) e n (t0 x o (w x i)) else o
-- chunk c (input bytes 0..3) covers RV words z0*c .. z0*c + z0 - 1: at most 16*z0 output bytes (see z0). Every chunk validates the WHOLE program; invalid: empty output.
def l1 (x : List UInt8) (c n : UInt64) : List UInt8 :=
  let s := c * z0;
  let e := (if s + z0 < n then s + z0 else n);
  if c1 (len' x) x 0 n == 1 then l0 (len' x) x s e n [] else []
def m (x : List UInt8) : List UInt8 :=
  if len x < 4 then [] else
  if (len x &&& 3) == 0 then
    l1 x ((rd x 0) ||| ((rd x 1) <<< 8) ||| ((rd x 2) <<< 16) ||| ((rd x 3) <<< 24)) ((len x - 4) >>> 2)
  else []

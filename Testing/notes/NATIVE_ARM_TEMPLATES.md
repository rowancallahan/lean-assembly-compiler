# Gen (RISC-V / J) vs GenArm (native A64): template correspondence

Sources (branch nap-m2, read-only): `Nano/Codegen/Gen.lean` (G), `Nano/Codegen/GenArm.lean` (A),
`Nano/Run/{Call,CallA,Expr,Heap,Loop,Templates,EVX,EVXL,NdSem,NdDef,StartCode,ArmEnc}.lean`.
Nothing was built or run; all A64 decodings are by hand from the encoder bases in A:11-48.

## 0. Conventions

**Register map** (J register = RISC-V number; `ArmEnc.lean:49 armReg`, same as A:4-7 header):

| J | 0 | 1 ra | 2 sp | 5 t0 | 6 t1 | 7 t2 | 8 s0 | 10 a0 | 11 a1 | 12 a2 | 13 a3 | 14 a4 | 15 a5 | 28 t3 | 29 t4 | 30 t5 | 31 t6 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A64 | (none; zero) | x30 | x4 | x5 | x6 | x7 | x8 | x0 | x1 | x2 | x3 | x14 | x15 | x12 | x13 | x10 | x11 |

A64 scratch (no J counterpart): x16, x17, NZCV.

**Encoders decoded** (A:50-67, 101): `a1 d n v` = `add xd,xn,#v`; `a2` = `sub xd,xn,#v`; `a3 c d n m` = 3-reg form
(c: 0x8B add, 0xCB sub, 0x8A and, 0xAA orr, 0xCA eor, 0x9AC02000 lslv, 0x9AC02400 lsrv);
`a4 c d v j` = movz(0xD28)/movk(0xF28)/movn(0x928) `xd,#v,lsl 16j`; `a35 a_15 t n k` = `ldr xt,[xn,#8k]`,
`a35 a_16 t n k` = `str xt,[xn,#8k]` (NB the 4th argument is the SCALED offset: `a35 4181721088 8 2 1` = `ldr x8,[x2,#8]`,
`a35 4181721088 14 16 2` = `ldr x14,[x16,#16]`); `a36 a_17/a_18` = `ldur/stur xt,[xn,#simm9]`;
`a32 t u n` = `ldp xt,xu,[xn]` (xt=[xn], xu=[xn+8]); `a33 n m` = `subs x16,xn,xm`; `a34 d n m` = `add xd,xn,xm,lsl #3`;
`a35 (a3 a_11 0 0 6) 5 5 17` = `madd x5,x5,x6,x17`; `a3 945842176 5 12 6` (0x38606800) = `ldrb w5,[x12,x6]`;
`a35 956301312 15 14 0` (0x39000000) = `strb w15,[x14]`; `a16 c h b` = b.cond/cbz/cbnz word `c` at word h with
imm19 = (b-h) (WORD offset relative to the branch itself); literals 1409286147 = `b.lo`(cond 3), 1409286146 = `b.hs`(cond 2),
1409286145 = `b.ne`(cond 1); `a3 a_23 r 0 0` = `cbnz xr`, `a3 a_24 r 0 0` = `cbz xr`; `a3 a_26 0 14 0` = `br x14`;
3592356800 = `br x30`; 335544320 = `b .+0` (placeholder); `a_20 ||| k` = `b .+k words`.

**J side**: `CallProbe.J` (Call.lean:11-29), `step` (Call.lean:83-99). J branch/jal offsets are in J instructions
relative to the branch. `wr s 0 v = s` (x0 writes ignored), `jal rd off` links `b + lo(pc+1)`,
`jalr rd rs` jumps to `ly.un(x[rs] - b)`.

**Alignment notation**: `Jk = Am` means "after k J instructions of the template (J pc = start+k) the J state equals,
under the register map, the A64 state after m words (A64 pc = start'+m)", modulo x16/x17/NZCV unless stated.
"no boundary" = no A64 pc at which the state matches that J pc.

**Helper: lengths that are not constant** (details in section E):
* `M(v)` = number of words of `a6` (li) for value v, 1..4. J: `L(v) = (liT d v).length` = 1 if v < 2048 else 17.
* `ldw(f)` / `stw(f)` = number of words of `a9` for signed offset f: 1 if (0 <= f < 32768 and f%8 = 0) or (-256 <= f < 0);
  2 if -4095 <= f < -256; (3..6 otherwise - unreachable for slot offsets, see E).

---

## 1. push register (checked)

* G `g21` (G:74, t0) / `g22` (G:78, reg d); A `a10` (A:103). J: `push` Call.lean:166, `pushA` Expr.lean:134
  (`pushA tgt q r = push r (tgt - (q+2))`; tgt = 1 everywhere Gen uses it).
* J (start q): `0 addi 31 31 (-8)` ; `1 bgeu 31 30 2` ; `2 jal 0 (1-(q+2))` ; `3 sd r 31 0`. Length 4.
* A64 (start h): `0 sub x11,x11,#8` ; `1 subs x16,x11,x10` ; `2 b.lo word 1` (imm19 = 1-(h+2), relative to word h+2) ;
  `3 str xr,[x11]`. Length 4. No placeholder.
* Alignment: J0=A0, J1=A1. A2 (after subs) = J1 plus x16/NZCV written. `bgeu;jal` is fused into `subs;b.lo`:
  J pc q+2 (the `jal`) has NO A64 boundary. Taken/ok path: J3 = A3; OOM path: J at word 1 (after bgeu-not-taken + jal,
  2 J steps) = A64 at word 1 (after 1 branch). J4 = A4.
* Differences: x16 := x11 - x10, NZCV written. Branch polarity inverted (J skips the jal when t6 >= t5; A64 branches to the stub
  when x11 <u x10).

## 2. li d, v (constant)

* G `g23` (G:82); A `a6`/`a7`/`a8` (A:83/74/70). J: `liT` Expr.lean:35 (`liJ` :31, `liB` :32).
* J: `if v < 2048 then [addi d 0 v] else addi d 0 0 :: liB d v 8`, `liJ d v j = [slli d d 8, addi d d ((v / 2^(56-8j)) % 256)]`,
  j = 0..7 (top byte first). Length L(v) = 1 or 17.
* A64 (A:83-86):
  ```
  if v < 65536 then movz d,#v
  else if (2^64-1 - v) < 65536 then movn d,#(~v)
  else if a8 v 0 < a8 v 65535 then a7 4 o d v 0 65535 0   -- movn path
  else a7 4 o d v 0 0 0                                    -- movz path
  ```
  `a7` walks the four 16-bit chunks low to high, skips chunks equal to e (0 or 0xFFFF); the first emitted word is
  `movz d,#c,lsl 16j` (e=0) or `movn d,#(65535-c),lsl 16j` (e=65535); every later one is `movk d,#c,lsl 16j`.
  Length M(v) = 1 (first two cases), else 4 - (#chunks = 0xFFFF) on the movn path (taken iff #zero chunks < #0xFFFF chunks),
  else 4 - (#zero chunks). Range 1..4. No placeholder.
* Alignment: only J0 = A0 and J_L = A_M. No interior J pc has an A64 boundary and vice versa (partial values differ).
* Differences: only xd written on both sides; no flags, no x16/x17 (unless d = 16, see a5). Intermediate values differ.

### 2a. CONST v
* G `g36` c=1 (G:217) `g21 (g23 o 5 v)`; A `a24` c=1 (A:238) `a10 (a6 o 5 v) 5`. J: `constT 1 q v = liT 5 v ++ pushA 1 (q + L) 5`
  (Expr.lean:137); `lnV (.const v) = (liT 5 v).length + 4` (NdSem.lean:136).
* J length L(v)+4 (5 or 21); A64 length M(v)+4 (5..8). Alignment: li (section 2) then push (section 1).

## 3. slot load / store and signed add (A64-only helpers)

* A `a5` (A:88) `add d,n,#v signed`: `v < 4096`: `add xd,xn,#v` (1 word); `-v < 4096`: `sub xd,xn,#(-v)` (1 word);
  else `li x16,v ; add xd,xn,x16` (M(v)+1 words, x16 clobbered).
* A `a9 o s t n f` (A:93): 8-byte load (s=0) / store (s=1) of xt at [xn + f]:
  ```
  if f < 32768 then (if f &&& 7 == 0 then  ldr/str xt,[xn,#f]                       -- 1 word
                     else a5 o 16 n f ; ldr/str xt,[x16])                           -- >=2 words (never for slots)
  else if f + 256 < 512 then ldur/stur xt,[xn,#f]                                   -- 1 word, -256 <= f < 0
  else a5 o 16 n f ; ldr/str xt,[x16]                                               -- sub x16,xn,#-f ; ldr/str (2 words) if f >= -4095
  ```
* J counterpart is always ONE instruction (`ld rd rs off` / `sd rs2 rs1 off` / `addi`). Slot offset: G `g24` (G:94) =
  `Templates.slotOff` (Templates.lean:30) = `CallProbe.offOf` (Expr.lean:258): slot k < p at `8(p-1-k)+16`, slot k >= p at `-8(k-p+1)`.
* Alignment: J0 = A0, J1 = A_end. In the 2-word form the interior A64 point has x16 = xn + f (no J counterpart) and x16 stays
  clobbered afterwards.

## 4. LOCAL s w

* G `g25` (G:98) from `g36` c=2 (G:218); A `a20` (A:188) from `a24` c=2 (A:239). J: `localT 1 p s q w` (Expr.lean:261):
  per word k = s, s+1, ...: `[ld 5 8 (offOf p k)] ++ pushA 1 (q+1) 5`.
* J per word: `0 ld 5 8 off(k)` ; `1 addi 31 31 -8` ; `2 bgeu 31 30 2` ; `3 jal 0 ..` ; `4 sd 5 31 0`. Length 5w.
* A64 per word: `a9` load `x5,[x8,#off(k)]` (ldw(off) = 1 or 2 words: `ldr`, `ldur`, or `sub x16,x8,#n ; ldr x5,[x16]`), then push x5 (4).
  Length sum over k of (ldw(off(k)) + 4) = 5w + #{k : off(k) < -256}.
* Alignment per word: J0 = A0, J1 = A_ldw, then section 1 (J pc +3, the jal, no boundary).
* Differences: x16 possibly written by the load form AND by the push; flags.

## 5. pop into slots (LET, CONTINUE)

* G `g26` (G:105); A `a21` (A:194). Callers: work item 6 (LET: G:275 / A:299, `z` = slot, `y` = width), item 10 (CONTINUE:
  G:289 / A:313, `g26/a21 256 p 1 (p-1)`). J: `popSlot p k` Templates.lean:64, `popN p k0 w` Templates.lean:72
  (`popN p k0 (w+1) = popSlot p (k0+w) ++ popN p k0 w`, top word goes to slot k0+w-1).
* J per word: `0 ld 5 31 0` ; `1 addi 31 31 8` ; `2 sd 5 8 (slotOff p k)`. Length 3w.
* A64 per word: `0 ldr x5,[x11]` ; `1 add x11,x11,#8` ; then `a9` store `x5,[x8,#off]` (stw = 1 or 2 words: `str`, `stur`,
  or `sub x16,x8,#n ; str x5,[x16]`). Length 3w + #{k : off(k) < -256}.
* Alignment: J1 = A1, J2 = A2, J3 = A_end. 2-word store: interior point with x16 = x8 + off.
* CONTINUE: slots 1..p-1 are parameter slots (positive offsets) so always exactly 3(p-1) words on both sides.

## 6. pop two

* G `g30` (G:132); A `a11` (A:107). No standalone Proof definition (it is the first three J of `binT`, `ifHeadG`, `bgetT`, `bpushT`).
* J: `0 ld 6 31 0` ; `1 ld 5 31 8` ; `2 addi 31 31 k`. Length 3.
* A64: `0 ldp x6,x5,[x11]` ; `1 add x11,x11,#k`. Length 2.
* Alignment: J0 = A0, J2 = A1, J3 = A2. J pc +1 (t1 loaded, t0 not yet) has NO A64 boundary.
* Differences: both loads happen in one instruction (the DeepMind `ldp` lemma needs t != u, see NATIVE_ARM_PROOF_PLAN.md:33).

## 7. BIN op

* G `g31` (G:134) item 2 (G:263); A `a12` (A:109) item 2 (A:286). J: `binT op` Expr.lean:140.
* J: `0 ld 6 31 0` ; `1 ld 5 31 8` ; `2 addi 31 31 8` ; `3 alu op 5 5 6` ; `4 sd 5 31 0`. Length 5.
* A64, op != 3: `0 ldp x6,x5,[x11]` ; `1 add x11,x11,#8` ; `2 OP x5,x5,x6` ; `3 str x5,[x11]`. Length 4.
  OP: 1 add, 2 sub, 4 and, 5 orr, 6 lslv, 7 lsrv, 8 (and any other value) eor.
  op = 3: `0 ldp` ; `1 add x11,x11,#8` ; `2 movz x17,#0` ; `3 madd x5,x5,x6,x17` ; `4 str x5,[x11]`. Length 5.
* Alignment: J0 = A0, J2 = A1, J3 = A2, J4 = A3 (mul: A4), J5 = A4 (mul: A5). J pc +1 no boundary. Mul: A3 = J3 plus x17 = 0.
* Differences: x17 := 0 for mul. lslv/lsrv take the shift mod 64, same as J `aluf` (UInt64 shifts) - no difference in value.

## 8. PRIM p (G `g32` G:140, item 8 G:281; A `a13` A:117, item 8 A:305; J `primT` NdSem.lean:130)

### 8.1 ISIZE (1) / LEN (3)
* J `lenT 1 q = pushA 1 q 29` (Expr.lean:163); A `a10 o 13`. Exactly section 1 with r = 29 / x13. 4 = 4.

### 8.2 RD (2)
* J `rdT` (Expr.lean:177): `0 ld 6 31 0` ; `1 addi 5 0 0` ; `2 bgeu 6 29 3` ; `3 alu 1 5 28 6` ; `4 lbu 5 5 0` ; `5 sd 5 31 0`. Length 6.
* A64 (A:119-122): `0 ldr x6,[x11]` ; `1 movz x5,#0` ; `2 subs x16,x6,x13` ; `3 b.hs .+2` (to word 5) ; `4 ldrb w5,[x12,x6]` ;
  `5 str x5,[x11]`. Length 6.
* Alignment: J0=A0, J1=A1, J2=A2; A3 = J2 + x16/NZCV; after the branch J3 = A4 (in range) or J5 = A5 (out of range);
  J pc +4 (t0 = t3 + index, the byte address) has NO A64 boundary; J5 = A5, J6 = A6.
* Differences: A64 never materialises base+index in x5 (register-offset `ldrb`); x16, flags.

### 8.3 BNEW (5)
* J `bnewT 1 q kappa` (Heap.lean:7), W = (kappa+2)*8, L = L(W), L' = L(kappa):
  `addi 5 30 0` ; liT 6 W ; `alu 1 6 6 30` ; `bgeu 31 6 2` ; `jal 0 (1-(q+1+L+2))` ; liT 7 kappa ; `sd 0 5 0` ; `sd 7 5 8` ;
  `addi 30 6 0` ; pushA 1 (..) 5. Length 11 + L + L'.
* A64 (A:123-128), M = M(W), M' = M(kappa): `add x5,x10,#0` ; li x6,W ; `add x6,x6,x10` ; `subs x16,x11,x6` ; `b.lo word 1` ;
  li x7,kappa ; `movz x17,#0` ; `str x17,[x5]` ; `str x7,[x5,#8]` ; `add x10,x6,#0` ; push x5 (4). Length 12 + M + M'.
  (kappa = `bget r 9` = the generator's capacity parameter `u`; default 524288: J 45, A64 15 - M = 2, M' = 1.)
* Alignment: J1 = A1; J(1+L) = A(1+M); J(2+L) = A(2+M); `bgeu;jal` fused (J pc 3+L, the jal, no boundary); J(4+L) = A(4+M);
  J(4+L+L') = A(4+M+M'); `sd 0 5 0` (1 J) = `movz x17,#0 ; str x17,[x5]` (2 words, interior point = J state + x17=0);
  J(5+L+L') = A(6+M+M'); then 1:1 for `sd 7`, `addi 30`; then push.
* Differences: x17 := 0 (zero source), x16/flags twice (room check and push). Store order identical ([t0] then [t0+8]).

### 8.4 BSIZE (6)
* J `bsizeT` (Expr.lean:166): `ld 5 31 0` ; `ld 5 5 0` ; `sd 5 31 0`. A64 (A:130): `ldr x5,[x11]` ; `ldr x5,[x5]` ; `str x5,[x11]`.
  3 = 3, index for index, no scratch. Exact.

### 8.5 BGET (7)
* J `bgetT` (Expr.lean:208): `0 ld 6 31 0` ; `1 ld 5 31 8` ; `2 addi 31 31 8` ; `3 ld 7 5 0` ; `4 addi 14 0 0` ; `5 bgeu 6 7 4` ;
  `6 slli 6 6 3` ; `7 alu 1 5 5 6` ; `8 ld 14 5 16` ; `9 sd 14 31 0`. Length 10.
* A64 (A:131-135): `0 ldp x6,x5,[x11]` ; `1 add x11,x11,#8` ; `2 ldr x7,[x5]` ; `3 movz x14,#0` ; `4 subs x16,x6,x7` ;
  `5 b.hs .+3` (to word 8) ; `6 add x16,x5,x6,lsl #3` ; `7 ldr x14,[x16,#16]` ; `8 str x14,[x11]`. Length 9.
* Alignment: J2=A1, J3=A2, J4=A3, J5=A4; A5 = J5 + x16/NZCV; out of range: J9 = A8; in range: J6 = A6; J pc +7 and +8 have NO
  A64 boundary; J9 ~ A8 and J10 ~ A9 ONLY up to x5/x6 (next bullet).
* **Difference (register state at template exit, in-range path)**: J leaves t1 = 8*index and t0 = buf + 8*index; A64 leaves
  x6 = index, x5 = buf (x16 = buf + 8*index). So x5/x6 are NOT equal register-for-register after BGET. (Out of range they agree.)

### 8.6 BSET (8)
* J `bsetT` (Heap.lean:184): `0 ld 14 31 0` ; `1 ld 6 31 8` ; `2 ld 5 31 16` ; `3 addi 31 31 16` ; `4 ld 7 5 0` ; `5 bgeu 6 7 4` ;
  `6 slli 6 6 3` ; `7 alu 1 6 5 6` ; `8 sd 14 6 16`. Length 9.
* A64 (A:136-141): `0 ldp x14,x6,[x11]` ; `1 ldr x5,[x11,#16]` ; `2 add x11,x11,#16` ; `3 ldr x7,[x5]` ; `4 subs x16,x6,x7` ;
  `5 b.hs .+3` (to word 8 = end) ; `6 add x16,x5,x6,lsl #3` ; `7 str x14,[x16,#16]`. Length 8.
* Alignment: J2=A1 (J pc +1 no boundary), J3=A2, J4=A3, J5=A4, branch: J9 = A8 (out of range) or J6 = A6; J pc +7, +8 no boundary;
  J9 ~ A8 up to x6.
* **Difference**: in range J leaves t1 = buf + 8*index, A64 leaves x6 = index (x16 = buf + 8*index). x5 agrees (buf).

### 8.7 BPUSH (9) and PUT (4) (the `else` branch on both sides)
* J `bpushT 6 q` (Heap.lean:137): `0 ld 6 31 0` ; `1 ld 5 31 8` ; `2 addi 31 31 8` ; `3 ld 7 5 0` ; `4 ld 14 5 8` ; `5 bltu 7 14 2` ;
  `6 jal 0 (6-(q+6))` ; `7 slli 15 7 3` ; `8 alu 1 15 15 5` ; `9 sd 6 15 16` ; `10 addi 7 7 1` ; `11 sd 7 5 0`. Length 12.
* A64 (A:142-146): `0 ldp x6,x5,[x11]` ; `1 add x11,x11,#8` ; `2 ldp x7,x14,[x5]` ; `3 subs x16,x7,x14` ; `4 b.hs word 6`
  (imm19 = 6-(h+4)) ; `5 add x15,x5,x7,lsl #3` ; `6 str x6,[x15,#16]` ; `7 add x7,x7,#1` ; `8 str x7,[x5]`. Length 9.
* Alignment: J2=A1, J3=A2, J5=A3 (J pc +4: t2 loaded, a4 not - no boundary), A4 = J5 + x16/NZCV; `bltu;jal` fused: J pc +6 (the jal)
  no boundary; capacity path: both at word 6; J7 = A5; J pc +8 (a5 = 8*len) no boundary; J9 = A6 (x15 = buf + 8*len on both);
  J10=A7, J11=A8, J12=A9. Final registers agree exactly.
* Differences: x16/flags; second `ldp`.

## 9. IF (value and tail mode)

* G: visit `g36` c=4 (G:208/224) pushes items; item 3 (G:264-267) = head, item 4 (G:268-271) = else-jump + patch head, item 5
  (G:272) = patch end. A: `a24` c=4 (A:229/245), items 3/4/5 (A:287-298).
  J: `ifHeadG cmp lt` EVX.lean:37 (`cmpJ` :33; also `ifHead`/`ifHeadLt` Templates.lean:22/25); layout in `tm` NdSem.lean:161-163:
  `A ; B ; ifHeadG c (ln T) ; T ; [jal 0 (ln E + 1)] ; E`.
* J head: `0 ld 6 31 0` ; `1 ld 5 31 8` ; `2 addi 31 31 16` ; `3 beq 5 6 2` (cmp=1) or `bltu 5 6 2` (cmp=2) ; `4 jal 0 (lt+2)`
  (Gen: word 4 is a 0 placeholder, patched by item 4 via `g20`). Length 5.
* A64 head: `0 ldp x6,x5,[x11]` ; `1 add x11,x11,#16` ; `2 subs x16,x5,x6` ; `3 b.ne <ELSE>` (cmp=1, word 1409286145) or
  `b.hs <ELSE>` (cmp=2, word 1409286146) - word 3 is the PLACEHOLDER (imm19 = 0), patched by item 4 (`a18`) to the word after the
  else-jump. Length 4.
* Else-jump: J `[jal 0 (le+1)]` (1) ; A64 `b <END>` (1; placeholder 335544320 patched by item 5 via `a18`). 1 = 1.
* Alignment head: J2=A1 (J pc +1 no boundary), J3=A2, A3 = J3 + x16/NZCV; after the compare: then-branch J5 = A4; else-branch:
  J at ELSE (via beq-not-taken + jal, 2 J steps) = A64 at ELSE (1 branch). J pc +4 (the jal) no boundary.
* Recorded positions differ in meaning: Gen stores `h + 4` (the jal after the branch); GenArm stores `bsize o0` = index of the b.cond itself.
* Differences: x16 := x5 - x6, NZCV; polarity inverted (A64 branches to ELSE on the negated condition).

## 10. LOOP head / STEP / exit / CONTINUE

* G: `g36` c=9 (G:244-249), item 11 (G:295-298), item 9 (G:284-288), item 10 (G:289-294). A: `a24` c=9 (A:265-272),
  items 11 (A:319-322), 9 (A:308-312), 10 (A:313-318). J: `loopHead p dS`, `loopDec p` EVXL.lean:27-28 (abstract: `LoopT.head`,
  `LoopT.stepPre` Loop.lean:25-26); `tm` NdSem.lean:168-170; tail forms `tmT` NdSem.lean:177-179.
* Head. J: `0 ld 5 8 (slotOff p 0)` ; `1 beq 5 0 2` ; `2 jal 0 dS` (Gen: 0 placeholder at h+2, patched by item 11). Length 3.
  A64: `0 ldr x5,[x8,#8(p-1)+16]` (p >= 1; `ldur x5,[x8,#-8]` if p = 0) ; `1 cbnz x5,<STEP>` (PLACEHOLDER `cbnz x5,.+0`, patched by
  item 11 via `a18`). Length 2 (slot 0 offset is always a 1-word form). Loop head position `r[3]` = index of the load on both sides.
* Alignment: J0=A0, J1=A1; `beq;jal` fused into `cbnz`: J3 (zero arm) = A2; STEP: both at STEP with t0/x5 = fuel; J pc +2 (the jal)
  no boundary. No x16, no flags here.
* STEP prefix. J `loopDec p`: `addi 5 5 (-1)` ; `sd 5 8 (slotOff p 0)`. A64: `sub x5,x5,#1` ; `str x5,[x8,#off]` (or `stur`). 2 = 2, exact.
* Exit (non-tail node visited in tail mode): J `[jal 0 (X - here)]`; Gen pushes a 0 placeholder recorded in fixup buffer `f`;
  A64 `b` placeholder (335544320) recorded the same way; both patched at ENDDEF (`g28`/`a22`) to the epilogue start. 1 = 1.
* CONTINUE: J `popN p 1 (p-1) ++ [jal 0 (Hd - here)]`; A64 `a21 256 p 1 (p-1)` then `b <head>` (`a17 .. 0 (r[3])`, backward, no
  placeholder). 3(p-1)+1 = 3(p-1)+1.

## 11. CALL

* G item 7 (G:278) `g19 r1 o 1 (bget t z)`; A item 7 (A:302) `a17 r1 o 1 (bget t z)`. J: `tm (.call id as)` NdSem.lean:166:
  `tmL as ++ [jal 1 (T id - (h + lnL as))]`.
* J: `jal 1 off` (1). A64: `bl <def word>` (imm26 = b - h words) (1). Alignment 1 = 1.
* Difference: link value. J writes `b + lo(pc+1)` to x1; A64 writes the byte address of the next word to x30.

## 12. Def prologue

* G `g38` (G:310-329); A `a26` (A:334-352). J: `proA 1 f r` CallA.lean:6 (r = nslots - npw; abstract `pro` Call.lean:274);
  `defT` NdDef.lean:9 = `proA 1 f (nl - p) ++ tm S e (f + 12) ++ epi p q`.
* J (12): push 1 (0-3) ; push 8 (4-7) ; `8 addi 8 31 0` ; `9 addi 31 31 (-8r)` ; `10 bgeu 31 30 2` ; `11 jal 0 (1-(f+11))`.
* A64 (12): push x30 (0-3) ; push x8 (4-7) ; `8 add x8,x11,#0` ; `9 sub x11,x11,#8r` (`add x11,x11,#0` when r = 0; via `a5`,
  1 word since 8r <= 2000) ; `10 subs x16,x11,x10` ; `11 b.lo word 1`. Word 11 is first pushed as 0 and overwritten by `bset`
  inside `a26` itself (not a deferred fixup).
* Alignment: index for index, except J pcs f+2, f+6, f+11 (the three jals) have no A64 boundary; A2, A6, A11 are "after subs" points.
  Body starts at +12 on both sides. Def table entry `t[d]` = start word on both sides.
* Differences: x16/flags three times.

## 13. Def epilogue

* G item 12 (G:299-307) + `g29` (G:125); A item 12 (A:323-331) + `a23` (A:209). J: `epi p q` Call.lean:288, `copy`/`copyJ` Call.lean:217-221.
* J: `0 ld 14 8 8` ; `1 ld 15 8 0` ; for j = 0..q-1: `ld 5 31 (8(q-1-j))` ; `sd 5 8 (8p+16-8(j+1))` ; then
  `addi 31 8 (8p+16-8q)` ; `addi 8 15 0` ; `jalr 0 14`. Length 2q + 5.
* A64: `0 ldp x15,x14,[x8]` ; for each j: `ldr x5,[x11,#8(q-1-j)]` (1 word) ; store `x5,[x8,#d_j]`, d_j = 8p+16-8(j+1):
  `str` if d_j >= 0, `stur` if -256 <= d_j < 0, `sub x16,x8,#-d_j ; str x5,[x16]` if d_j < -256 ; then
  `add x11,x8,#n` or `sub x11,x8,#n` (via `a5`, 1 word) ; `add x8,x15,#0` ; `br x14`.
  Length 4 + 2q + #{j < q : 8(j+1) - 8p - 16 > 256}.
* Alignment: J2 = A1 (J pc +1: a4 loaded, a5 not - no boundary); copy pairs 1:1 (2-word store has an interior x16 point);
  last three 1:1.
* Differences: load order fused (`ldp`); x16 in the long store form. Negative d_j occur when q > p + 2 (Gen's J side just uses a
  negative `sd` offset).

## 14. Stubs (word 0, words 1-5, 6-10)

* G `g34` (G:169); A `a14` (A:149). J: `stubJ S` StartCode.lean:73.
* J: `0 jal 0 S` ; `1 addi 10 0 (-1)` ; `2 addi 11 0 0` ; `3 ld 1 12 0` ; `4 ld 8 12 8` ; `5 jalr 0 1` ; `6 addi 10 0 (-2)` ;
  `7 addi 11 0 0` ; `8 ld 1 12 0` ; `9 ld 8 12 8` ; `10 jalr 0 1`.
* A64: `0 b <start>` (placeholder 335544320, patched in `a28` by `a18 r o 0`) ; `1 movn x0,#0` ; `2 movz x1,#0` ; `3 ldr x30,[x2]` ;
  `4 ldr x8,[x2,#8]` ; `5 br x30` ; `6 movn x0,#1` ; `7 movz x1,#0` ; `8 ldr x30,[x2]` ; `9 ldr x8,[x2,#8]` ; `10 br x30`.
* Alignment: exactly one-to-one, 11 = 11, every J pc has its A64 boundary. No scratch, no flags.

## 15. Start code

* G `g35` (G:175), called from `g56` (G:350); A `a19` (A:168), called from `a28` (A:368). J: `startJ S w` StartCode.lean:64, length 32.
* J and A64 side by side (S / S' = start word):

| J pc | J | A64 idx | A64 |
|---|---|---|---|
| 0 | addi 30 12 16 | 0 | add x10,x2,#16 |
| 1 | srli 31 2 3 | 1, 2 | movz x16,#3 ; lsrv x11,x4,x16 |
| 2 | slli 31 31 3 | 3 | lslv x11,x11,x16 (reuses x16 = 3) |
| 3 | bgeu 31 30 4 | 4, 5 | subs x16,x11,x10 ; b.hs .+4 (to 9) |
| 4 | addi 10 0 (-1) | 6 | movn x0,#0 |
| 5 | addi 11 0 0 | 7 | movz x1,#0 |
| 6 | jalr 0 1 | 8 | br x30 |
| 7 | sd 1 12 0 | 9 | str x30,[x2] |
| 8 | sd 8 12 8 | 10 | str x8,[x2,#8] |
| 9 | addi 28 10 0 | 11 | add x12,x0,#0 |
| 10 | addi 29 11 0 | 12 | add x13,x1,#0 |
| 11 | jal 1 (w-(S+11)) | 13 | bl <main> (`a17 r o9 1 w`) |
| 12 | ld 5 31 0 | 14 | ldr x5,[x11] |
| 13 | ld 7 5 0 | 15 | ldr x7,[x5] |
| 14 | bne 7 0 4 | 16 | cbnz x7,.+4 (to 20) |
| 15 | addi 10 0 1 | 17 | movz x0,#1 |
| 16 | addi 11 0 0 | 18 | movz x1,#0 |
| 17 | jal 0 12 (to 29) | 19 | b .+12 (to 31) |
| 18 | addi 11 7 0 | 20 | add x1,x7,#0 |
| 19 | addi 6 5 16 | 21 | add x6,x5,#16 |
| 20 | addi 14 13 0 | 22 | add x14,x3,#0 |
| 21 | beq 7 0 7 (to 28) | 23 | cbz x7,.+7 (to 30) |
| 22 | ld 15 6 0 | 24 | ldr x15,[x6] |
| 23 | sb 15 14 0 | 25 | strb w15,[x14] |
| 24 | addi 6 6 8 | 26 | add x6,x6,#8 |
| 25 | addi 14 14 1 | 27 | add x14,x14,#1 |
| 26 | addi 7 7 (-1) | 28 | sub x7,x7,#1 |
| 27 | jal 0 (-6) (to 21) | 29 | b .-6 (to 23) |
| 28 | addi 10 0 0 | 30 | movz x0,#0 |
| 29 | ld 1 12 0 | 31 | ldr x30,[x2] |
| 30 | ld 8 12 8 | 32 | ldr x8,[x2,#8] |
| 31 | jalr 0 1 | 33 | br x30 |

* Lengths: J 32, A64 34. Map: pi(0)=0, pi(1)=1, pi(2)=3, pi(3)=4, pi(j)=j+2 for j >= 4. EVERY J pc has an A64 boundary here (the
  `bgeu` is not followed by a jal). Extra interior A64 points: 2 (x16 = 3) and 5 (after subs).
* No placeholders inside (all offsets are computed at emission); word 0 is patched just before (`a18 r o 0`).
* Differences: x16 = 3 then x16 = x11 - x10, NZCV. Everything else register-for-register.

---

## A. Return addresses (`jal 1 _`)

J lists containing `jal 1`: only (i) `tm (.call id as)` (NdSem.lean:166), return pc = h + lnL as + 1 (the instruction after the call),
and (ii) `startJ` index 11 (StartCode.lean:66), return pc = S + 12. `LinkOK` (Call.lean:60) quantifies over exactly these.
A64: `bl` (base `a_21`) is emitted only by `a17` with d = 1, called at A:175 (start code, word S'+13, return S'+14) and A:303
(work item 7). Both J sites therefore have `bl` and the A64 return address is the word after it, which is pi(return pc).
Every other J `jal` has rd = 0 and maps to `b`, to a fused conditional branch, or (stub exits) to the b.cond target.

## B. `jalr` uses

| J | where | A64 |
|---|---|---|
| `jalr 0 1` | stubJ 5, 10 (StartCode.lean:74-75) | `br x30` (3592356800), A:151, 153 |
| `jalr 0 1` | startJ 6, 31 (StartCode.lean:65, 70) | `br x30`, A:172, 185 |
| `jalr 0 14` | last of `epi` (Call.lean:289) | `br x14` (`a3 a_26 0 14 0`), A:213 |

No other `jalr`/`br`. The value in a4/x14 at the epilogue is the saved-ra cell `[s0+8]`, which holds a J link `b + lo(n)` on
the J side and an A64 byte address on the A64 side (so those memory cells and x30/x14 are not byte-equal across the two machines).

## C. Forward-branch patching

* Gen: `g19 r o d b` (G:65) emits `jal d` here -> word b (range check `g14`, error flag otherwise); `g20 r o p` (G:69) OVERWRITES
  word p (a literal 0 placeholder) with `g13 0 p (bsize o)`.
* GenArm: `a17 r o d b` (A:155) emits `b`/`bl` with imm26 = b - h (same `g14` check, on A64 word indices); `a18 r o p` (A:160):
  ```
  let v := bget o p;
  let w := (if (v >>> 26) == 5 then v ||| ((h - p) &&& a_34) else a16 v p h);
  ```
  i.e. it READS the placeholder and ORs the offset in: a `b` placeholder gets imm26, a `b.cond`/`cbnz` placeholder gets imm19
  (condition / register bits kept). Relies on the placeholder's offset field being 0. Same `g14 p h` range check (±2^18 words =
  exactly the imm19 range).
* Callers (identical structure on both sides): exit fixups at ENDDEF (`g28` G:116 / `a22` A:200); item 4 (patch the IF head, after
  pushing the else-jump placeholder; G:270 / A:294); item 5 (patch the else-jump; G:273 / A:297); item 11 (patch the LOOP head;
  G:297 / A:321); word 0 (G:358 / A:376).
* What the placeholder IS differs: IF head - Gen: the `jal` at head+4 (after `beq/bltu +8`); GenArm: the `b.cond` itself at head+3.
  LOOP head - Gen: the `jal` at h+2; GenArm: the `cbnz` at h1. Else-jump, exits, word 0: a `jal x0` vs a `b` (same role).
* The push/BNEW/BPUSH/prologue stub branches are not placeholders on either side (targets 1 and 6 are known).

## D. Fixed layout of words 0-10

See section 14: word 0 = jump to the start code (patched last), 1-5 out of memory (a0/x0 = -1, a1/x1 = 0, restore ra/x30 and s0/x8
from [a2]/[x2], return), 6-10 capacity (a0/x0 = -2, ...). J list `stubJ` vs A64 words: one-to-one, 11 = 11, no scratch. Stub
targets used by templates: word 1 from push, BNEW room check, prologue; word 6 from BPUSH/PUT.

## E. Word counts that depend on a value / operand

1. **`a6` li (A:83)**: M(v) in 1..4 by the 16-bit chunk pattern of v (rules in section 2). Used for CONST v (operand of the AST
   node), BNEW's W = (kappa+2)*8 and kappa (generator parameter `u`), and inside `a5`'s fallback. Gen's J side is also
   value-dependent but differently (1 or 17, threshold 2048).
2. **`a9` slot access (A:93)**: 1 word if offset in [0, 32768) and 8-aligned (`ldr`/`str`) or in [-256, 0) (`ldur`/`stur`);
   2 words (`sub x16,..; ldr/str [x16]`) if in [-4095, -256); longer forms (li x16) otherwise. For frame slots the offset is
   `g24 p s`: parameters 16..2008 (1 word); local number m = s-p+1 at -8m: 1 word for m <= 32, 2 words for 33 <= m <= 250
   (bounds from `g43`: s < 251, s + w <= nslots, and `g38`/`a26`: nslots < 251, p <= nslots). So it depends on the slot index
   and npw (static AST operands), not on a run-time value. Sites: LOCAL (load), LET pops (store), CONTINUE pops (always 1 word),
   LOOP head/STEP (slot 0: always 1 word), epilogue copy (loads always 1 word; stores 1 or 2 words by d_j, section 13).
3. **`a5` (A:88)**: 1 word for |v| < 4096; used with 8r <= 2000 (prologue) and |8p+16-8q| <= 2016 (epilogue), so always 1 word there;
   the li fallback is only reachable through `a9`'s long form, which the bounds above exclude.
4. **BIN**: 5 words for mul (op 3), 4 otherwise (operand of the node, not a value).
I could not find any other value-dependent length. (I did not re-derive the bound nslots < 251 beyond reading `g38`/`a26`
z0..z4 and `g43`; the "unreachable" claims in items 2-3 rest on those checks.)

## F. Summary of J pcs with NO A64 boundary

* the `jal 0 <stub>` after `bgeu` in every push (pc+2), BNEW room check, prologue (f+2, f+6, f+11); the `jal` after `bltu` in BPUSH (pc+6);
* the `jal 0 ELSE` after `beq/bltu` in the IF head (pc+4); the `jal 0 STEP` after `beq` in the LOOP head (pc+2);
* the point between the two `ld`s of every pop-two (BIN, IF head, BGET, BPUSH: pc+1), of BSET's first two `ld`s (pc+1),
  of BPUSH's `ld 7`/`ld 14` (pc+4), of the epilogue's `ld 14`/`ld 15` (pc+1);
* address-computation interiors: RD pc+4; BGET pc+7, pc+8; BSET pc+7, pc+8; BPUSH pc+8;
* all interior pcs of `liT`.

## G. Semantic differences relevant to a simulation relation

1. x16 and NZCV are written by every compare (push, BNEW, RD, BGET, BSET, BPUSH, IF head, prologue, start code) and x16 by
   the long slot form; x17 := 0 by mul and BNEW. None is read across a template boundary.
2. **BGET and BSET leave different values in mapped registers** (x5/x6 vs t0/t1, sections 8.5/8.6) on the in-range path. A
   register-for-register relation at template boundaries must exclude the dead temporaries (t0, t1; safest: t0 t1 t2 a4 a5).
   LOOP STEP does rely on t0/x5 = fuel across the head -> STEP jump, but that value agrees.
3. Link values and saved return addresses (x1/x30, a4/x14, frame cell [s0+8], [a2]) differ: J `b + lo(n)` vs A64 byte address.
4. Fused branches take 1 A64 step where J takes 2 (bgeu-not-taken + jal; beq-not-taken + jal), with inverted polarity.
5. `ldp` reads two cells in one step (pop-two, BSET, BPUSH header, epilogue); `ldrb [x12,x6]` replaces add + lbu.
6. `sd 0 5 0` (zero register) = `movz x17,#0 ; str x17,[x5]`.
7. Order of memory WRITES is the same in every template (checked: push, BNEW header, BPUSH, BSET, pops, epilogue copy, start code).
8. Range/acceptance: both use `g14` and the 2^18-word output limit, but on their own word indices, so one generator can raise
   the error flag where the other does not (also noted in Testing/notes/NATIVE_ARM_PROOF_PLAN.md:51-53).

## H. Not determined / caveats

* `Testing/nano/v2self/native_arm/README.md` is not in this branch; nothing here was checked against tests or a disassembler.
* A64 decodings are manual from the bases in A:11-48 (cross-checked against `ArmEnc.lean` where the same word exists:
  `aluC 3 = 0x9B004400` = madd with Ra = x17, `subsR`, `brR`).
* `ifHead`/`ifHeadLt` (Templates.lean) vs `ifHeadG` (EVX.lean): `tm` uses `ifHeadG`; I did not check which proofs still use the older two.
* CONTINUE with p = 0 (`p - 1` wraps in `g26`/`a21`) behaves identically on both sides; I assumed the width pass excludes it.

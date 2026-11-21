/- GenArm's IMAGE of a J program, as a list of ATOMS (M4; agreed with NATIVE-ARM-PROOF).
An atom `NTm` is a minimal group of J instructions whose machine code has an A64 boundary at both ends: its J
instructions `NTm.j` (position independent) and its A64 words `NTm.a π q h` (`q` = J pc of the atom, `h` = its word
index, `π` = word index of a J pc, used for branch targets).  Every GenArm template is a list of atoms
(Testing/notes/NATIVE_ARM_TEMPLATES.md); fused pairs (`bgeu; jal` → `subs; b.lo`, `ld; ld` → `ldp`, …) are ONE atom,
so their interior J pcs are not anchors.
* `NAt`: an atom with the flags "J register 5 / 6 (t0 / t1) is not related at the atom's start" (`Img.dead`).
* `jOf`, `wordsOf`, `imgOf` (bytes little-endian; layout: anchor ↦ 4·word index, any other J pc ↦ `2^64 + pc`;
  anchors = atom boundaries), `NWf` (size, per-atom side conditions `NTm.ok`, targets are anchors, the dead flags
  are consistent along every edge), and the image relation `NatV C I := ∃ tl, C = jOf tl ∧ I = imgOf tl ∧ NWf tl`.
Definitions only; the static laws (entry, off_le, vis_*, live_ret) are proved in NatImgLaws.lean. -/
import Nano.Run.GTarget
import Nano.Run.Expr
import Nano.Run.NatT.LiDef
namespace JT
open Proven.Top SimW CallProbe ArmEnc

/-- the compare of a fused compare-and-jump atom -/
inductive NCmp where
  | geu | ltu | eq
  deriving DecidableEq, Repr

/-- **atoms** -/
inductive NTm where
  /-- `liT d v` ↔ GenArm's `li` (`liL`: movz / movn / movk chain) -/
  | li (d : Nat) (v : UInt64)
  /-- `addi d n imm` ↔ `add` / `sub` immediate; `n = 0`: `li` of the (sign-extended) immediate -/
  | addi (d n : Nat) (imm : Int)
  /-- `alu op d a b` ↔ one 3-register word; mul (`op = 3`): `movz x17, #0; madd` -/
  | alu (op d a b : Nat)
  /-- `ld d n off` ↔ `ldr` / `ldur` / `sub x16; ldr [x16]` by the offset -/
  | ld (d n : Nat) (off : Int)
  /-- `sd s n off` ↔ `str` / `stur` / `sub x16; str [x16]`; `s = 0`: `movz x17, #0` first, then store x17 -/
  | sd (s n : Nat) (off : Int)
  /-- `ld a n 0; ld b n 8` (`sw`: the two J loads in the other order) ↔ `ldp xa, xb, [xn]` -/
  | ldp (a b n : Nat) (sw : Bool)
  /-- `b<c> a b 2; jal 0 off` ↔ `subs x16, xa, xb; b.<not c> target` (push, BNEW, prologue, BPUSH, IF head) -/
  | cj (c : NCmp) (a b : Nat) (off : Int)
  /-- `bgeu a b off` ↔ `subs x16, xa, xb; b.hs target` (RD, BGET, BSET, start code) -/
  | bgeu (a b : Nat) (off : Int)
  /-- `beq r 0 2; jal 0 off` ↔ `cbnz xr, target` (LOOP head) -/
  | lpz (r : Nat) (off : Int)
  /-- `bne r 0 off` ↔ `cbnz xr, target` -/
  | bnez (r : Nat) (off : Int)
  /-- `beq r 0 off` ↔ `cbz xr, target` -/
  | beqz (r : Nat) (off : Int)
  /-- `jal rd off` ↔ `b` (`rd = 0`) / `bl` (`rd = 1`) -/
  | jal (rd : Nat) (off : Int)
  /-- `jalr 0 rs` ↔ `br x<rs>` -/
  | jalr (rs : Nat)
  /-- `alu 1 d n m; lbu d d 0` ↔ `ldrb wd, [xn, xm]` (RD) -/
  | ldrbx (d n m : Nat)
  /-- BGET's tail `slli 6 6 3; alu 1 5 5 6; ld 14 5 16` ↔ `add x16, x5, x6, lsl #3; ldr x14, [x16, #16]` (t0, t1 die) -/
  | bgetI
  /-- BSET's tail `slli 6 6 3; alu 1 6 5 6; sd 14 6 16` ↔ `add x16, x5, x6, lsl #3; str x14, [x16, #16]` (t1 dies) -/
  | bsetI
  /-- BPUSH's address `slli 15 7 3; alu 1 15 15 5` ↔ `add x15, x5, x7, lsl #3` -/
  | bpushI
  /-- start code `srli d n 3; slli d d 3` ↔ `movz x16, #3; lsrv xd, xn, x16; lslv xd, xd, x16` -/
  | align8 (d n : Nat)
  /-- `sb s n 0` ↔ `strb ws, [xn]` -/
  | sb (s n : Nat)
  deriving DecidableEq

namespace NTm

/-- the J instructions of an atom -/
def j : NTm → List J
  | .li d v => liT d v
  | .addi d n imm => [.addi d n imm]
  | .alu op d a b => [.alu op d a b]
  | .ld d n off => [.ld d n off]
  | .sd s n off => [.sd s n off]
  | .ldp a b n sw => if sw then [.ld b n 8, .ld a n 0] else [.ld a n 0, .ld b n 8]
  | .cj c a b off => [match c with | .geu => .bgeu a b 2 | .ltu => .bltu a b 2 | .eq => .beq a b 2, .jal 0 off]
  | .bgeu a b off => [.bgeu a b off]
  | .lpz r off => [.beq r 0 2, .jal 0 off]
  | .bnez r off => [.bne r 0 off]
  | .beqz r off => [.beq r 0 off]
  | .jal rd off => [.jal rd off]
  | .jalr rs => [.jalr 0 rs]
  | .ldrbx d n m => [.alu 1 d n m, .lbu d d 0]
  | .bgetI => [.slli 6 6 3, .alu 1 5 5 6, .ld 14 5 16]
  | .bsetI => [.slli 6 6 3, .alu 1 6 5 6, .sd 14 6 16]
  | .bpushI => [.slli 15 7 3, .alu 1 15 15 5]
  | .align8 d n => [.srli d n 3, .slli d d 3]
  | .sb s n => [.sb s n 0]

/-- the J pc `q + off` -/
def jt (q : Nat) (off : Int) : Nat := ((q : Int) + off).toNat

/-- the J pcs an atom at J pc `q` may jump to (not its fall-through) -/
def tg (q : Nat) : NTm → List Nat
  | .cj _ _ _ off => [jt q (1 + off)]
  | .bgeu _ _ off => [jt q off]
  | .lpz _ off => [jt q (1 + off)]
  | .bnez _ off => [jt q off]
  | .beqz _ off => [jt q off]
  | .jal _ off => [jt q off]
  | _ => []

/-- the atom can pass control to the next atom (`jal` / `jalr` cannot; a call's return point is handled in `NWf`) -/
def ft : NTm → Bool
  | .jal _ _ => false
  | .jalr _ => false
  | _ => true

/-- 8-byte load (`st = false`) / store of raw register `t` at `[xn + off]` (GenArm's `a9`, the three reachable forms) -/
def memW (st : Bool) (t n : Nat) (off : Int) : List Nat :=
  if off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 then [if st then ArmEnc.str t n off.toNat else ArmEnc.ldr t n off.toNat]
  else if -256 ≤ off ∧ off < 0 then [if st then ArmEnc.stur t n off else ArmEnc.ldur t n off]
  else [ArmEnc.subi 16 n (-off).toNat, if st then ArmEnc.str t 16 0 else ArmEnc.ldr t 16 0]

/-- the condition code of the branch of `cj` (taken = the J compare fails, so J runs its `jal`) -/
def cjC : NCmp → Nat
  | .geu => 3
  | .ltu => 2
  | .eq => 1

/-- **the A64 words of an atom** at J pc `q`, word index `h`; `π` = word index of a J pc -/
def a (π : Nat → Nat) (q h : Nat) : NTm → List Nat
  | .li d v => liL (armReg d) v.toNat
  | .addi d n imm =>
    if n = 0 then liL (armReg d) (UInt64.ofInt imm).toNat
    else if imm < 0 then [ArmEnc.subi (armReg d) (armReg n) imm.natAbs]
    else [ArmEnc.addi (armReg d) (armReg n) imm.toNat]
  | .alu op d x y =>
    if op = 3 then [ArmEnc.movz 17 0, ArmEnc.rr (aluC 3) (armReg d) (armReg x) (armReg y)]
    else [ArmEnc.rr (aluC op) (armReg d) (armReg x) (armReg y)]
  | .ld d n off => memW false (armReg d) (armReg n) off
  | .sd s n off => if s = 0 then ArmEnc.movz 17 0 :: memW true 17 (armReg n) off else memW true (armReg s) (armReg n) off
  | .ldp x y n _ => [ArmEnc.ldp (armReg x) (armReg y) (armReg n)]
  | .cj c x y off => [ArmEnc.subsR (armReg x) (armReg y), ArmEnc.bc (cjC c) ((π (jt q (1 + off)) : Int) - ((h : Int) + 1))]
  | .bgeu x y off => [ArmEnc.subsR (armReg x) (armReg y), ArmEnc.bc 2 ((π (jt q off) : Int) - ((h : Int) + 1))]
  | .lpz r off => [ArmEnc.cbnz (armReg r) ((π (jt q (1 + off)) : Int) - (h : Int))]
  | .bnez r off => [ArmEnc.cbnz (armReg r) ((π (jt q off) : Int) - (h : Int))]
  | .beqz r off => [ArmEnc.cbz (armReg r) ((π (jt q off) : Int) - (h : Int))]
  | .jal rd off =>
    [if rd = 0 then ArmEnc.bB ((π (jt q off) : Int) - (h : Int)) else ArmEnc.blB ((π (jt q off) : Int) - (h : Int))]
  | .jalr rs => [ArmEnc.brR (armReg rs)]
  | .ldrbx d n m => [ArmEnc.ldrbR (armReg d) (armReg n) (armReg m)]
  | .bgetI => [ArmEnc.addLsl3 16 (armReg 5) (armReg 6), ArmEnc.ldr (armReg 14) 16 16]
  | .bsetI => [ArmEnc.addLsl3 16 (armReg 5) (armReg 6), ArmEnc.str (armReg 14) 16 16]
  | .bpushI => [ArmEnc.addLsl3 (armReg 15) (armReg 5) (armReg 7)]
  | .align8 d n => [ArmEnc.movz 16 3, ArmEnc.rr 0x9AC02400 (armReg d) (armReg n) 16,
      ArmEnc.rr 0x9AC02000 (armReg d) (armReg d) 16]
  | .sb s n => [ArmEnc.strb (armReg s) (armReg n) 0]

/-- the number of A64 words of an atom (it does not depend on `π`, `q`, `h`) -/
def alen (t : NTm) : Nat := (t.a (fun _ => 0) 0 0).length

/-- a mapped J register other than x0 -/
def mr (r : Nat) : Bool := mapped r && decide (r ≠ 0)

/-- the per-atom side conditions (registers, immediate ranges) -/
def ok : NTm → Bool
  | .li d _ => mr d
  | .addi d n imm => mr d && mapped n && decide (-4096 < imm ∧ imm < 4096) &&
      decide (n = 0 → -2048 ≤ imm ∧ imm < 2048)
  | .alu _ d x y => mr d && mr x && mr y
  | .ld d n off => mr d && mr n && decide (-4096 < off ∧ off < 32768 ∧ (0 ≤ off → off % 8 = 0))
  | .sd s n off => mapped s && mr n && decide (-4096 < off ∧ off < 32768 ∧ (0 ≤ off → off % 8 = 0))
  | .ldp x y n _ => mr x && mr y && mr n && decide (x ≠ y ∧ x ≠ n ∧ y ≠ n)
  | .cj _ x y _ => mr x && mr y
  | .bgeu x y _ => mr x && mr y
  | .lpz r _ => mr r
  | .bnez r _ => mr r
  | .beqz r _ => mr r
  | .jal rd _ => decide (rd = 0 ∨ rd = 1)
  | .jalr rs => decide (rs = 1 ∨ rs = 14)
  | .ldrbx d n m => mr d && mr n && mr m
  | .bgetI => true
  | .bsetI => true
  | .bpushI => true
  | .align8 d n => mr d && mr n
  | .sb s n => mr s && mr n

/-- the atom reads J register `r` before writing it -/
def reads (r : Nat) : NTm → Bool
  | .li _ _ => false
  | .addi _ n _ => n == r
  | .alu _ _ x y => x == r || y == r
  | .ld _ n _ => n == r
  | .sd s n _ => s == r || n == r
  | .ldp _ _ n _ => n == r
  | .cj _ x y _ => x == r || y == r
  | .bgeu x y _ => x == r || y == r
  | .lpz x _ => x == r
  | .bnez x _ => x == r
  | .beqz x _ => x == r
  | .jal _ _ => false
  | .jalr rs => rs == r
  | .ldrbx _ n m => n == r || m == r
  | .bgetI => r == 5 || r == 6
  | .bsetI => r == 5 || r == 6 || r == 14
  | .bpushI => r == 5 || r == 7
  | .align8 _ n => n == r
  | .sb s n => s == r || n == r

/-- on every exit of the atom, J register `r` holds a value the machine code computes too -/
def writes (r : Nat) : NTm → Bool
  | .li d _ => d == r
  | .addi d _ _ => d == r
  | .alu _ d _ _ => d == r
  | .ld d _ _ => d == r
  | .ldp x y _ _ => x == r || y == r
  | .ldrbx d _ _ => d == r
  | .bgetI => r == 14
  | .bpushI => r == 15
  | .align8 d _ => d == r
  | _ => false

/-- after the atom, J register `r` differs from its machine register -/
def kills (r : Nat) : NTm → Bool
  | .bgetI => r == 5 || r == 6
  | .bsetI => r == 6
  | _ => false

end NTm

/-- an atom with its dead flags: J register 5 / 6 is not related at the atom's start -/
structure NAt where
  t : NTm
  d5 : Bool
  d6 : Bool

/-- J register `r` is flagged dead at the start of `x` -/
def NAt.dead (x : NAt) (r : Nat) : Bool := (r == 5 && x.d5) || (r == 6 && x.d6)

/-- J register `r` is dead on the exits of `x` -/
def NAt.out (x : NAt) (r : Nat) : Bool := (x.dead r && !x.t.writes r) || x.t.kills r

/-- **the J program of an atom list** -/
def jOf (tl : List NAt) : List J := tl.flatMap fun x => x.t.j

/-- the atom boundaries from J pc `q`, word index `h`: (J pc, word index), the end included -/
def bnd : List NAt → Nat → Nat → List (Nat × Nat)
  | [], q, h => [(q, h)]
  | x :: l, q, h => (q, h) :: bnd l (q + x.t.j.length) (h + x.t.alen)

/-- the word index of J pc `pc` (0 when `pc` is not a boundary) -/
def widx (B : List (Nat × Nat)) (pc : Nat) : Nat := ((B.find? fun p => p.1 == pc).map Prod.snd).getD 0

/-- the words of an atom list from J pc `q`, word index `h` -/
def wordsFrom (π : Nat → Nat) : List NAt → Nat → Nat → List Nat
  | [], _, _ => []
  | x :: l, q, h => x.t.a π q h ++ wordsFrom π l (q + x.t.j.length) (h + x.t.alen)

/-- **the A64 words of an atom list** -/
def wordsOf (tl : List NAt) : List Nat := wordsFrom (widx (bnd tl 0 0)) tl 0 0

/-- the code bytes: every word little-endian -/
def wordBytes (A : List Nat) : List UInt8 :=
  A.flatMap fun w => [wbyte (BitVec.ofNat 32 w) 0, wbyte (BitVec.ofNat 32 w) 1, wbyte (BitVec.ofNat 32 w) 2,
    wbyte (BitVec.ofNat 32 w) 3]

/-- the byte offset of J pc `pc`: `4 · word index` at a boundary (the first one with that word index), else
`2^64 + pc` (never a code address) -/
def nOff (B : List (Nat × Nat)) (pc : Nat) : Nat :=
  if 4 * widx B pc < 2 ^ 64 ∧ ((B.find? fun p => 4 * p.2 == 4 * widx B pc).map Prod.fst) = some pc then 4 * widx B pc
  else 2 ^ 64 + pc

def nUn (B : List (Nat × Nat)) (a : Nat) : Nat :=
  if a < 2 ^ 64 then ((B.find? fun p => 4 * p.2 == a).map Prod.fst).getD 0 else a - 2 ^ 64

theorem nInv (B : List (Nat × Nat)) (pc : Nat) : nUn B (nOff B pc) = pc := by
  unfold nOff
  split
  · rename_i h
    unfold nUn
    rw [if_pos h.1, h.2]; rfl
  · unfold nUn
    rw [if_neg (by omega)]; omega

/-- the dead flags at the atom starts, from J pc `q` -/
def dl : List NAt → Nat → List (Nat × NAt)
  | [], _ => []
  | x :: l, q => (q, x) :: dl l (q + x.t.j.length)

/-- J pc `pc` is an anchor: an atom boundary -/
def nVis (tl : List NAt) (pc : Nat) : Prop := ∃ w, (pc, w) ∈ bnd tl 0 0

/-- J register `r` is not related at anchor `pc` -/
def nDead (tl : List NAt) (pc r : Nat) : Prop := ∃ x, (pc, x) ∈ dl tl 0 ∧ x.dead r = true

/-- **the image of an atom list** -/
def imgOf (tl : List NAt) : Img where
  code := wordBytes (wordsOf tl)
  ly := ⟨nOff (bnd tl 0 0), nUn (bnd tl 0 0), nInv (bnd tl 0 0)⟩
  vis := nVis tl
  dead := nDead tl

/-- **well-formed atom lists** -/
structure NWf (tl : List NAt) : Prop where
  /-- GenArm's size limit, on A64 words -/
  size : (wordsOf tl).length < 2 ^ 18
  ok : ∀ x ∈ tl, x.t.ok = true
  /-- no atom reads a dead register -/
  rd : ∀ x ∈ tl, ∀ r, x.dead r = true → x.t.reads r = false
  /-- fall-through: what is dead after an atom is flagged at the next one (so the last atom does not fall through
  with a dead register) -/
  fall : ∀ (pre : List NAt) (x : NAt) (suf : List NAt), tl = pre ++ x :: suf → x.t.ft = true →
    ∀ r, x.out r = true → nDead tl ((jOf pre).length + x.t.j.length) r
  /-- jump targets are anchors, flagged with what is dead after the atom -/
  tgt : ∀ (pre : List NAt) (x : NAt) (suf : List NAt), tl = pre ++ x :: suf → ∀ p ∈ x.t.tg (jOf pre).length,
    nVis tl p ∧ ∀ r, x.out r = true → nDead tl p r
  /-- function return (`jalr 0 14`): what is dead there is flagged at every return point (after a `jal 1`) -/
  ret : ∀ (pre : List NAt) (x : NAt) (suf : List NAt), tl = pre ++ x :: suf → x.t = .jalr 14 →
    ∀ (pre' : List NAt) (off : Int) (d5 d6 : Bool) (suf' : List NAt), tl = pre' ++ ⟨.jal 1 off, d5, d6⟩ :: suf' →
    ∀ r, x.dead r = true → nDead tl ((jOf pre').length + 1) r

/-- **the image relation of the native target**: `I` is the image of an atom list whose J program is `C` -/
def NatV (C : List J) (I : Img) : Prop := ∃ tl : List NAt, C = jOf tl ∧ I = imgOf tl ∧ NWf tl

end JT

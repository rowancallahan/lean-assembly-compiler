/- DRAFT (not in the lake build; no proofs): the statement of rv2arm's block correctness, the future
`armTarget.step_ok`. Checked to elaborate with Lean 4.29 against `Spec.Top` and `Machine/Call` (see README).
The proof plan is in PROOF_NOTES.md. It is to be proved once the ARM model builds, with `M := Spec's arm`.

Contents: `blockJ` = rv2arm's block of a J instruction at the J level (the same words as rv2arm.lean/.py; the
`#guard`s in ArmBlockCheck.lean compare it with the oracle on every distinct instruction of B2); J's own `step` at
link width 16 (`s.wk = 3`); `AccOK` = accesses in D, no wrap; `RelA` = the register/memory/code relation;
`BlockOK M` = one J step is matched by a run of ≤ 4 machine steps (A64 block) from `RelA` to `RelA`. -/
import Spec.Top
import Nano.V2Self.Proof.Machine.Call

namespace ArmBlock
open CallProbe Proven.Top

/-! ## register map π (RV → A64; RV sp (x2) ↦ x4; x0 ↦ 31, but no emitted word has a register field 31: an x0
operand is read from x17 after `movz x17, #0`) -/
def pi (r : Nat) : Nat :=
  match r with
  | 0 => 31 | 1 => 30 | 2 => 4 | 10 => 0 | 11 => 1 | 12 => 2 | 13 => 3 | 28 => 12 | 29 => 13 | 30 => 10 | 31 => 11
  | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 14 => 14 | 15 => 15 | _ => 99
/-- RV registers that live in an A64 general register (all mapped ones but x0) -/
def live (r : Nat) : Prop := pi r < 31 ∧ r ≠ 0
/-- RV register that rv2arm accepts (mapped, x0 included) -/
def rdOK (r : Nat) : Prop := pi r < 32
def wrOK (r : Nat) : Prop := pi r < 32

/-! ## A64 words (64-bit forms), as in rv2arm -/
def movz (d i : Nat) : Nat := 0xD2800000 + i * 2^5 + d
def movk (d i h : Nat) : Nat := 0xF2800000 + h * 2^21 + i * 2^5 + d
def addi (d n i : Nat) : Nat := 0x91000000 + i * 2^10 + n * 2^5 + d
def subi (d n i : Nat) : Nat := 0xD1000000 + i * 2^10 + n * 2^5 + d
def rr (c d n m : Nat) : Nat := c + m * 2^16 + n * 2^5 + d
def subsR (n m : Nat) : Nat := 0xEB000000 + m * 2^16 + n * 2^5 + 16
def mo (f : Int) (k : Nat) : Nat := (f % ((2 ^ k : Nat) : Int)).toNat
def ldr (t n f : Nat) : Nat := 0xF9400000 + (f / 8) * 2^10 + n * 2^5 + t
def str (t n f : Nat) : Nat := 0xF9000000 + (f / 8) * 2^10 + n * 2^5 + t
def ldrb (t n f : Nat) : Nat := 0x39400000 + f * 2^10 + n * 2^5 + t
def strb (t n f : Nat) : Nat := 0x39000000 + f * 2^10 + n * 2^5 + t
def bB (f : Int) : Nat := 0x14000000 + mo f 26
def blB (f : Int) : Nat := 0x94000000 + mo f 26
def bc (c : Nat) (f : Int) : Nat := 0x54000000 + mo f 19 * 2^5 + c
def cbz (t : Nat) (f : Int) : Nat := 0xB4000000 + mo f 19 * 2^5 + t
def brR (n : Nat) : Nat := 0xD61F0000 + n * 2^5
def PAD : Nat := addi 16 16 0
def aluC (op : Nat) : Nat :=
  match op with
  | 1 => 0x8B000000 | 2 => 0xCB000000 | 3 => 0x9B004400 | 4 => 0x8A000000 | 5 => 0xAA000000
  | 6 => 0x9AC02000 | 7 => 0x9AC02400 | _ => 0xCA000000
/-- x16 := x[rs] + f (rs ≠ x0) -/
def addr16 (rs : Nat) (f : Int) : Nat := if f < 0 then subi 16 (pi rs) f.natAbs else addi 16 (pi rs) f.toNat
def pad4 (l : List Nat) : List Nat := l ++ List.replicate (4 - l.length) PAD
/-- `movz x17, #0` when r = x0 (a store of x0 stores the zeroed x17; xzr is never used) -/
def zpre (r : Nat) : List Nat := if r = 0 then [movz 17 0] else []
def dat (r : Nat) : Nat := if r = 0 then 17 else pi r
/-- an operand: x0 is read from x17 (zeroed by the block first) -/
def opR (r : Nat) : Nat := if r = 0 then 17 else pi r
def compBr (c a b : Nat) (o : Int) : List Nat :=
  if a = 0 ∨ b = 0 then [movz 17 0, subsR (opR a) (opR b), bc c (4 * o - 2)]
  else [subsR (pi a) (pi b), bc c (4 * o - 1)]

/-- the real words of the block of J instruction `j` (before padding) -/
def body : J → List Nat
  | .addi rd rs imm =>
    if rd = 0 then [] else if rs = 0 then
      (if imm < 0 then [movz (pi rd) (65536 - imm.natAbs), movk (pi rd) 65535 1, movk (pi rd) 65535 2, movk (pi rd) 65535 3]
       else [movz (pi rd) imm.toNat])
    else if imm < 0 then [subi (pi rd) (pi rs) imm.natAbs] else [addi (pi rd) (pi rs) imm.toNat]
  | .ld rd rs f =>
    if rd = 0 then [] else if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [ldr (pi rd) (pi rs) f.toNat]
    else [addr16 rs f, ldr (pi rd) 16 0]
  | .sd r2 r1 f =>
    zpre r2 ++ if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [str (dat r2) (pi r1) f.toNat] else [addr16 r1 f, str (dat r2) 16 0]
  | .lbu rd rs f =>
    if rd = 0 then [] else if 0 ≤ f ∧ f < 4096 then [ldrb (pi rd) (pi rs) f.toNat] else [addr16 rs f, ldrb (pi rd) 16 0]
  | .sb r2 r1 f =>
    zpre r2 ++ if 0 ≤ f ∧ f < 4096 then [strb (dat r2) (pi r1) f.toNat] else [addr16 r1 f, strb (dat r2) 16 0]
  | .alu op rd a b =>
    if rd = 0 then [] else zpre (if a = 0 ∨ b = 0 ∨ op = 3 then 0 else 1) ++ [rr (aluC op) (pi rd) (opR a) (opR b)]
  | .slli rd rs sh => if rd = 0 then [] else zpre rs ++ [movz 16 sh, rr 0x9AC02000 (pi rd) (opR rs) 16]
  | .srli rd rs sh => if rd = 0 then [] else zpre rs ++ [movz 16 sh, rr 0x9AC02400 (pi rd) (opR rs) 16]
  | .beq a b o =>
    if a = 0 ∧ b = 0 then [bB (4 * o)] else if b = 0 then [cbz (pi a) (4 * o)] else if a = 0 then [cbz (pi b) (4 * o)]
    else compBr 0 a b o
  | .bne a b o => compBr 1 a b o
  | .bltu a b o => compBr 3 a b o
  | .bgeu a b o => compBr 2 a b o
  | .jal rd o => if rd = 0 then [bB (4 * o)] else [PAD, PAD, PAD, blB (4 * o - 3)]
  | .jalr _ rs => [brR (pi rs)]

def blockJ (j : J) : List Nat := pad4 (body j)

/-- RV I/S immediate range (12 bits signed): add/sub imm12 and the x16 address forms fit -/
def imm12 (i : Int) : Prop := -2048 ≤ i ∧ i < 2048

/-- the instructions rv2arm accepts (its validation `c0`, at the J level; `n` = program length), PLUS the encoding
ranges rv2arm takes for granted because its input is RV code (`imm12`); the same table as `ArmEnc.armOK` -/
def validJ (n pc : Nat) : J → Prop
  | .addi rd rs i => rdOK rs ∧ wrOK rd ∧ imm12 i
  | .ld rd rs f | .lbu rd rs f => rs ≠ 0 ∧ rdOK rs ∧ wrOK rd ∧ imm12 f
  | .sd r2 r1 f | .sb r2 r1 f => r1 ≠ 0 ∧ rdOK r1 ∧ wrOK r2 ∧ imm12 f
  | .alu op rd a b => 1 ≤ op ∧ op ≤ 8 ∧ rdOK a ∧ rdOK b ∧ wrOK rd
  | .slli rd rs sh | .srli rd rs sh => sh < 64 ∧ rdOK rs ∧ wrOK rd
  | .beq a b o | .bne a b o | .bltu a b o | .bgeu a b o =>
    rdOK a ∧ rdOK b ∧ 0 ≤ (pc : Int) + o ∧ (pc : Int) + o < n ∧ -65535 ≤ o ∧ o ≤ 65535
  | .jal rd o => (rd = 0 ∨ rd = 1) ∧ 0 ≤ (pc : Int) + o ∧ (pc : Int) + o < n ∧ -2 ^ 23 < o ∧ o < 2 ^ 23   -- b/bl imm26 reach (rv2arm c3)
  | .jalr rd rs => rd = 0 ∧ rs ≠ 0 ∧ pi rs < 31

/-! ## J with link width W: no definition needed any more. J's state carries `wk` (7536764), `step` links with
`s.w = 4·(s.wk + 1)`, and the ARM blocks are `step` at `s.wk = 3` (w = 16; `BlockOK` assumes it). -/

/-! ## the relation -/
/-- little-endian bytes of the code words -/
def codeBytes (ws : List Nat) : List UInt8 :=
  ws.flatMap fun w => [w.toUInt8, (w / 2^8).toUInt8, (w / 2^16).toUInt8, (w / 2^24).toUInt8]
def codeA (C : List J) : List UInt8 := codeBytes ((C.map blockJ).flatten)

/-- `RelA M C D K (pc, s) t`: A64 state t represents J state (pc, s) of program C.
`D` = the data addresses (8-aligned cells of J memory: work block, input, output), `K` = the values of the
registers the code must keep (x18..x29, and sp = register 31, which the blocks never touch; RV sp lives in x4).
Scratch x16/x17, NZCV and every other piece of machine state are free. -/
structure RelA (M : Machine) (C : List J) (D : Nat → Prop) (K : Nat → UInt64) (ps : Nat × St) (t : M.State) : Prop where
  cfg : M.configured t
  pc : (M.observe t).programCounter.toNat = ps.2.b + 16 * ps.1
  regs : ∀ r, live r → (M.observe t).register (pi r) = ps.2.x r
  zero : ps.2.x 0 = 0
  keep : ∀ r, 18 ≤ r → r ≤ 29 → (M.observe t).register r = K r
  spKeep : (M.observe t).register 31 = K 31
  code : ∀ i (h : i < (codeA C).length), (M.observe t).memory (UInt64.ofNat (ps.2.b + i)) = some (codeA C)[i]
  mem : ∀ a k, D a → k < 8 → (M.observe t).memory (UInt64.ofNat (a + k)) = some ((ps.2.m a >>> (8 * k).toUInt64).toUInt8)
  dAl : ∀ a, D a → a % 8 = 0
  dCode : ∀ a, D a → a + 8 ≤ ps.2.b ∨ ps.2.b + (codeA C).length ≤ a
  ram : ps.2.b + (codeA C).length ≤ M.ramEnd ∧ ∀ a, D a → a + 8 ≤ M.ramEnd

/-- the J step's memory accesses hit D (8-byte: the cell itself; byte: its cell), and a `jalr` target is a block.
Also no wrap (the no-wrap part of `JLay.SafeX`): J's `ea` clamps `x[rs] + imm` with `Int.toNat`, while the A64
add/sub (and the x16 address forms) wrap mod 2^64, so the two agree only for 0 ≤ x[rs] + imm < 2^64. In particular
`addi rd x0 imm` with imm < 0 (J: 0; A64: 2^64 + imm) is excluded here; that wrapping case is the separate
`JTarget.addi_ok`. -/
def NoWrap (v : UInt64) (i : Int) : Prop := 0 ≤ (v.toNat : Int) + i ∧ (v.toNat : Int) + i < 2 ^ 64
def AccOK (C : List J) (D : Nat → Prop) : Nat × St → Prop
  | (pc, s) => match C[pc]? with
    | some (.addi _ rs imm) => NoWrap (s.x rs) imm
    | some (.ld _ rs off) => NoWrap (s.x rs) off ∧ D (ea (s.x rs) off)
    | some (.sd _ r1 off) => NoWrap (s.x r1) off ∧ D (ea (s.x r1) off)
    | some (.lbu _ rs off) => NoWrap (s.x rs) off ∧ D (ea (s.x rs) off - ea (s.x rs) off % 8)
    | some (.sb _ r1 off) => NoWrap (s.x r1) off ∧ D (ea (s.x r1) off - ea (s.x r1) off % 8)
    | some (.jalr _ rs) => s.b ≤ (s.x rs).toNat ∧ ((s.x rs).toNat - s.b) % 16 = 0
    | _ => True

/-- **Block correctness** (the statement to prove for `M := arm`): if the J instruction at pc is valid, its accesses
are in D and do not wrap, J's link width is 16 (`s.wk = 3`), and t represents (pc, s), then the A64 block runs
(≤ 4 steps) to a state representing J's next state. -/
def BlockOK (M : Machine) : Prop :=
  ∀ (C : List J) (D : Nat → Prop) (K : Nat → UInt64) (pc : Nat) (s : St) (j : J) (t : M.State) (ps' : Nat × St),
    C[pc]? = some j → validJ C.length pc j → s.wk = 3 → AccOK C D (pc, s) → RelA M C D K (pc, s) t →
    step C (pc, s) = some ps' → ∃ t', Runs M t t' ∧ RelA M C D K ps' t'

end ArmBlock

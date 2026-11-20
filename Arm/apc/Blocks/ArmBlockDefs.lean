/- VERBATIM copy of the definitions of `Testing/nano/v2self/arm/ArmBlock.lean` (π, the A64 word encoders, `body`,
`blockJ`, `validJ`, `AccOK`), without `stepW`/`RelA`/`BlockOK` (those need `Spec.Top`'s `Machine`; `Block.lean`
states the DeepMind version). `Blocks/check_copy.sh` checks the copy. -/
import Nano.V2Self.Proof.Machine.Call
namespace ArmBlock
open CallProbe

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
  | .jal rd o => (rd = 0 ∨ rd = 1) ∧ 0 ≤ (pc : Int) + o ∧ (pc : Int) + o < n
  | .jalr rd rs => rd = 0 ∧ rs ≠ 0 ∧ pi rs < 31

/-- the J step's memory accesses hit D (8-byte: the cell itself; byte: its cell), and a `jalr` target is a block -/
def AccOK (C : List J) (D : Nat → Prop) : Nat × St → Prop
  | (pc, s) => match C[pc]? with
    | some (.ld _ rs off) => D (ea (s.x rs) off)
    | some (.sd _ r1 off) => D (ea (s.x r1) off)
    | some (.lbu _ rs off) => D (ea (s.x rs) off - ea (s.x rs) off % 8)
    | some (.sb _ r1 off) => D (ea (s.x r1) off - ea (s.x r1) off % 8)
    | some (.jalr _ rs) => s.b ≤ (s.x rs).toNat ∧ ((s.x rs).toNat - s.b) % 16 = 0
    | _ => True

end ArmBlock

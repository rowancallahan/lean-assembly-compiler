/- The ARM (AArch64) adapter's machine words (Sail-free; UNPROVEN encodings), the analogue of `RvEnc` for a future
`armTarget : JT.JTarget` (Machine/Target.lean). The words are rv2arm's block table, the same as
Testing/nano/v2self/arm/ArmBlock.lean `blockJ` (checked there against the Python oracle on every instruction of B2;
`Testing/nano/v2self/arm/check_armenc.sh` checks `ArmEnc.blk = ArmBlock.blockJ` on the same instructions).

PROOF NOTES (owner rule: semantics, conventions, which lemma covers it):
* Shape: `blockLen = 4`. J instruction pc ↦ byte `base + 16·pc`. The real words come first, then
  `PAD = add x16, x16, #0`, except `jal x1`, which is PAD, PAD, PAD, `bl`.
* Links (design V2, NANO_V2_ARM.md §0a): **needs J with link width W = 16** (`jal` links `b + 16·(pc+1)`, `jalr` jumps
  to `(x − b)/16`). With today's `CallProbe.step` (W = 4) a uniform 4-word block cannot be related by `JT.Rel`
  (E, 2026-11-20). The W-refactor of J is a separate unit.
* Registers `armReg` (π, = ArmBlock.pi): J 1 ↦ x30 (ra), 2 ↦ x4 (work top; Spec armMapping.workTop = 4, 1437a980),
  10..13 ↦ x0..x3, 28..31 ↦ x12, x13, x10, x11, and 5..8, 14, 15 ↦ the same number. Every other J register ↦ 99, a
  number that is no AArch64 register (observe reads it as 0; Gen never writes those, `armOK` refuses them).
  π avoids 16..29 and 31: no emitted word has a register field 31 (no xzr, wzr or sp anywhere).
* Scratch `armScratch = [16, 17]`: x16 = address / shift amount / `subs` destination, x17 = the zero for an x0 operand
  and `madd`'s addend. Both are dead at block boundaries; NZCV is written only by `subs` and read by the `b.cond` of the
  same block.
* Kept: x18..x29 and sp are never written or read (`armMapping.kept` = x19..x29, sp). `Laws.kept_map` holds by the
  "outside the image of reg and outside scratch" disjunct.
* `armOK` = rv2arm's validation (ArmBlock.validJ) PLUS the encoding ranges that rv2arm takes for granted because its
  input is RV code: |imm| < 2048 (RV I/S immediates) for addi / ld / sd / lbu / sb, so `add`/`sub` imm12 and the x16
  address forms fit; shift < 64; branch offsets within ±65535 J instructions (b.cond / cbz reach ±1 MiB).
* Per-block lemmas (`armTarget.step_ok`): Testing/nano/v2self/arm/PROOF_NOTES.md, one row per J kind. -/
import Nano.V2Self.Proof.Machine.Call
namespace ArmEnc
open CallProbe

/-! ## registers -/

/-- π: J register ↦ AArch64 register number (99 = not a register) -/
def armReg (r : Nat) : Nat :=
  match r with
  | 0 => 31 | 1 => 30 | 2 => 4 | 10 => 0 | 11 => 1 | 12 => 2 | 13 => 3 | 28 => 12 | 29 => 13 | 30 => 10 | 31 => 11
  | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 14 => 14 | 15 => 15 | _ => 99

/-- the registers the blocks may clobber -/
def armScratch : List Nat := [16, 17]

/-- a J register rv2arm accepts (mapped; x0 included) -/
def mapped (r : Nat) : Bool := armReg r < 32

/-! ## A64 words (64-bit forms; register fields are 5 bits, never 31) -/
def movz (d i : Nat) : Nat := 0xD2800000 + i * 2^5 + d
def movk (d i h : Nat) : Nat := 0xF2800000 + h * 2^21 + i * 2^5 + d
def addi (d n i : Nat) : Nat := 0x91000000 + i * 2^10 + n * 2^5 + d
def subi (d n i : Nat) : Nat := 0xD1000000 + i * 2^10 + n * 2^5 + d
def rr (c d n m : Nat) : Nat := c + m * 2^16 + n * 2^5 + d
/-- `subs x16, xn, xm` (the compare; x16 is scratch) -/
def subsR (n m : Nat) : Nat := 0xEB000000 + m * 2^16 + n * 2^5 + 16
/-- an offset field of `k` bits, two's complement -/
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
/-- `add x16, x16, #0` -/
def PAD : Nat := addi 16 16 0
/-- the register ALU, Gen's BIN numbering: add 1, sub 2, mul 3 (`madd …, x17`), and 4, orr 5, lslv 6, lsrv 7, eor 8 -/
def aluC (op : Nat) : Nat :=
  match op with
  | 1 => 0x8B000000 | 2 => 0xCB000000 | 3 => 0x9B004400 | 4 => 0x8A000000 | 5 => 0xAA000000
  | 6 => 0x9AC02000 | 7 => 0x9AC02400 | _ => 0xCA000000
/-- x16 := x[rs] + f (rs ≠ x0, |f| < 4096) -/
def addr16 (rs : Nat) (f : Int) : Nat := if f < 0 then subi 16 (armReg rs) f.natAbs else addi 16 (armReg rs) f.toNat
def pad4 (l : List Nat) : List Nat := l ++ List.replicate (4 - l.length) PAD
/-- `movz x17, #0` when r = x0 -/
def zpre (r : Nat) : List Nat := if r = 0 then [movz 17 0] else []
/-- a data / operand register: x0 is read from x17 (zeroed by the block first) -/
def opR (r : Nat) : Nat := if r = 0 then 17 else armReg r
def compBr (c a b : Nat) (o : Int) : List Nat :=
  if a = 0 ∨ b = 0 then [movz 17 0, subsR (opR a) (opR b), bc c (4 * o - 2)]
  else [subsR (armReg a) (armReg b), bc c (4 * o - 1)]

/-- the real words of the block of J instruction `j` (before padding) -/
def body : J → List Nat
  | .addi rd rs imm =>
    if rd = 0 then [] else if rs = 0 then
      (if imm < 0 then [movz (armReg rd) (65536 - imm.natAbs), movk (armReg rd) 65535 1, movk (armReg rd) 65535 2,
          movk (armReg rd) 65535 3]
       else [movz (armReg rd) imm.toNat])
    else if imm < 0 then [subi (armReg rd) (armReg rs) imm.natAbs] else [addi (armReg rd) (armReg rs) imm.toNat]
  | .ld rd rs f =>
    if rd = 0 then [] else if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [ldr (armReg rd) (armReg rs) f.toNat]
    else [addr16 rs f, ldr (armReg rd) 16 0]
  | .sd r2 r1 f =>
    zpre r2 ++ if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [str (opR r2) (armReg r1) f.toNat]
      else [addr16 r1 f, str (opR r2) 16 0]
  | .lbu rd rs f =>
    if rd = 0 then [] else if 0 ≤ f ∧ f < 4096 then [ldrb (armReg rd) (armReg rs) f.toNat]
    else [addr16 rs f, ldrb (armReg rd) 16 0]
  | .sb r2 r1 f =>
    zpre r2 ++ if 0 ≤ f ∧ f < 4096 then [strb (opR r2) (armReg r1) f.toNat] else [addr16 r1 f, strb (opR r2) 16 0]
  | .alu op rd a b =>
    if rd = 0 then [] else zpre (if a = 0 ∨ b = 0 ∨ op = 3 then 0 else 1) ++ [rr (aluC op) (armReg rd) (opR a) (opR b)]
  | .slli rd rs sh => if rd = 0 then [] else zpre rs ++ [movz 16 sh, rr 0x9AC02000 (armReg rd) (opR rs) 16]
  | .srli rd rs sh => if rd = 0 then [] else zpre rs ++ [movz 16 sh, rr 0x9AC02400 (armReg rd) (opR rs) 16]
  | .beq a b o =>
    if a = 0 ∧ b = 0 then [bB (4 * o)] else if b = 0 then [cbz (armReg a) (4 * o)]
    else if a = 0 then [cbz (armReg b) (4 * o)] else compBr 0 a b o
  | .bne a b o => compBr 1 a b o
  | .bltu a b o => compBr 3 a b o
  | .bgeu a b o => compBr 2 a b o
  | .jal rd o => if rd = 0 then [bB (4 * o)] else [PAD, PAD, PAD, blB (4 * o - 3)]
  | .jalr _ rs => [brR (armReg rs)]

/-- the block of a J instruction, as numbers -/
def blockJ (j : J) : List Nat := pad4 (body j)

/-- **`armTarget.enc`**: the block as A64 words (`blockLen = 4`) -/
def blk (j : J) : List (BitVec 32) := (blockJ j).map (BitVec.ofNat 32)

/-! ## encodability (`armTarget.lay`'s per-instruction part) -/

/-- an RV I/S immediate (12-bit signed) -/
def imm12 (i : Int) : Bool := -2048 ≤ i && i < 2048

/-- the J instructions `blk` encodes faithfully, at index `pc` of a program of `n` instructions -/
def armOK (n pc : Nat) : J → Bool
  | .addi rd rs i => mapped rs && mapped rd && imm12 i
  | .ld rd rs f | .lbu rd rs f => rs != 0 && mapped rs && mapped rd && imm12 f
  | .sd r2 r1 f | .sb r2 r1 f => r1 != 0 && mapped r1 && mapped r2 && imm12 f
  | .alu op rd a b => 1 ≤ op && op ≤ 8 && mapped a && mapped b && mapped rd
  | .slli rd rs sh | .srli rd rs sh => sh < 64 && mapped rs && mapped rd
  | .beq a b o | .bne a b o | .bltu a b o | .bgeu a b o =>
    mapped a && mapped b && 0 ≤ (pc : Int) + o && (pc : Int) + o < n && -65535 ≤ o && o ≤ 65535
  | .jal rd o => (rd == 0 || rd == 1) && 0 ≤ (pc : Int) + o && (pc : Int) + o < n
  | .jalr rd rs => rd == 0 && rs != 0 && armReg rs < 31

/-- every instruction of the program is encodable -/
def progOK (C : List J) : Bool := (List.range C.length).all fun i => match C[i]? with
  | some j => armOK C.length i j
  | none => false

/-! ## checks (decided by the kernel) -/

/-- every block is exactly 4 words (`Laws.enc_len`), on one instruction of every kind and shape -/
def sample : List J :=
  [.addi 10 0 (-1), .addi 10 0 5, .addi 14 12 16, .addi 14 15 (-24), .addi 0 0 0,
   .ld 14 12 8, .ld 1 8 (-16), .ld 14 12 300, .sd 14 12 16, .sd 0 8 (-8), .lbu 14 10 3, .lbu 14 10 (-5),
   .sb 0 13 7, .sb 14 13 (-3), .alu 1 14 14 15, .alu 3 14 14 15, .alu 8 14 0 15, .slli 14 15 3, .srli 31 2 3,
   .srli 14 0 1, .beq 14 15 2, .beq 14 0 2, .beq 0 0 1, .bne 14 15 (-3), .bltu 0 15 2, .bgeu 14 0 5,
   .jal 0 7, .jal 0 (-4), .jal 1 12, .jalr 0 14, .jalr 0 1]

example : sample.all (fun j => (blk j).length == 4) = true := by decide
/-- no register field is 31 in the sample's words (bits 0–4, 5–9, 16–20 where used) -/
example : sample.all (fun j => (blockJ j).all fun w => w % 32 != 31) = true := by decide

/-- the sample's words in hex, one block per line (for `llvm-mc --disassemble -triple=aarch64`) -/
def hex8 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "0x" ++ String.ofList (List.replicate (8 - s.length) '0') ++ s
def sampleHex : String := "\n".intercalate (sample.map fun j => " ".intercalate ((blockJ j).map hex8))

end ArmEnc

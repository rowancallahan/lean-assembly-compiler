/- DRAFT (not in the lake build; no proofs): the statement of rv2arm's block correctness, the future
`armTarget.step_ok`. Checked to elaborate with Lean 4.29 against `Spec.Top` and `Machine/Call` (see README).
The proof plan is in PROOF_NOTES.md. It is to be proved once the ARM model builds, with `M := Spec's arm`.

Contents: `blockJ` = rv2arm's block of a J instruction at the J level (the same words as rv2arm.lean/.py; the
`#guard`s in ArmBlockCheck.lean compare it with the oracle on every distinct instruction of B2); `stepW` = J with
link width W (NANO_V2_ARM.md §0a, V2; `stepW 4` = `CallProbe.step`); `RelA` = the register/memory/code relation;
`BlockOK M` = one J step is matched by a run of ≤ 4 machine steps (A64 block) from `RelA` to `RelA`. -/
import Spec.Top
import Nano.V2Self.Proof.Machine.Call

namespace ArmBlock
open CallProbe Proven.Top

/-! ## register map π (RV → A64; 31 = xzr in register forms, sp in imm/base forms) -/
def pi (r : Nat) : Nat :=
  match r with
  | 0 => 31 | 1 => 30 | 2 => 31 | 10 => 0 | 11 => 1 | 12 => 2 | 13 => 3 | 28 => 12 | 29 => 13 | 30 => 10 | 31 => 11
  | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 14 => 14 | 15 => 15 | _ => 99
/-- RV registers that live in an A64 general register (not x0, not sp) -/
def live (r : Nat) : Prop := pi r < 31 ∧ r ≠ 0 ∧ r ≠ 2
/-- RV register usable as a source (mapped, or sp) / as a destination (mapped or x0, not sp) -/
def rdOK (r : Nat) : Prop := r = 2 ∨ pi r < 32
def wrOK (r : Nat) : Prop := r ≠ 2 ∧ pi r < 32

/-! ## A64 words (64-bit forms), as in rv2arm -/
def movz (d i : Nat) : Nat := 0xD2800000 + i * 2^5 + d
def addi (d n i : Nat) : Nat := 0x91000000 + i * 2^10 + n * 2^5 + d
def subi (d n i : Nat) : Nat := 0xD1000000 + i * 2^10 + n * 2^5 + d
def rr (c d n m : Nat) : Nat := c + m * 2^16 + n * 2^5 + d
def cmpR (n m : Nat) : Nat := 0xEB000000 + m * 2^16 + n * 2^5 + 31
def mo (f : Int) (k : Nat) : Nat := (f % ((2 ^ k : Nat) : Int)).toNat
def ldr (t n f : Nat) : Nat := 0xF9400000 + (f / 8) * 2^10 + n * 2^5 + t
def str (t n f : Nat) : Nat := 0xF9000000 + (f / 8) * 2^10 + n * 2^5 + t
def ldur (t n : Nat) (f : Int) : Nat := 0xF8400000 + mo f 9 * 2^12 + n * 2^5 + t
def stur (t n : Nat) (f : Int) : Nat := 0xF8000000 + mo f 9 * 2^12 + n * 2^5 + t
def ldrb (t n f : Nat) : Nat := 0x39400000 + f * 2^10 + n * 2^5 + t
def strb (t n f : Nat) : Nat := 0x39000000 + f * 2^10 + n * 2^5 + t
def bB (f : Int) : Nat := 0x14000000 + mo f 26
def blB (f : Int) : Nat := 0x94000000 + mo f 26
def bc (c : Nat) (f : Int) : Nat := 0x54000000 + mo f 19 * 2^5 + c
def brR (n : Nat) : Nat := 0xD61F0000 + n * 2^5
def PAD : Nat := addi 16 16 0
def aluC (op : Nat) : Nat :=
  match op with
  | 1 => 0x8B000000 | 2 => 0xCB000000 | 3 => 0x9B007C00 | 4 => 0x8A000000 | 5 => 0xAA000000
  | 6 => 0x9AC02000 | 7 => 0x9AC02400 | _ => 0xCA000000
/-- imm/base operand of RV register r -/
def base (r : Nat) : Nat := pi r
/-- x16 := x[rs] + f -/
def addr16 (rs : Nat) (f : Int) : Nat := if f < 0 then subi 16 (base rs) f.natAbs else addi 16 (base rs) f.toNat
/-- sp copies (to x16 for operand a, x17 for b), and the operand registers -/
def pre (a b : Nat) : List Nat := (if a = 2 then [addi 16 31 0] else []) ++ (if b = 2 then [addi 17 31 0] else [])
def opA (a : Nat) : Nat := if a = 2 then 16 else pi a
def opB (b : Nat) : Nat := if b = 2 then 17 else pi b
def pad4 (l : List Nat) : List Nat := l ++ List.replicate (4 - l.length) PAD

/-- the real words of the block of J instruction `j` at J index `pc` (before padding) -/
def body : J → List Nat
  | .addi rd rs imm =>
    if rd = 0 then [] else if rs = 0 then
      (if imm < 0 then [movz 16 imm.natAbs, rr 0xCB000000 (pi rd) 31 16] else [movz (pi rd) imm.toNat])
    else if imm < 0 then [subi (pi rd) (base rs) imm.natAbs] else [addi (pi rd) (base rs) imm.toNat]
  | .ld rd rs f =>
    if rd = 0 then [] else if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [ldr (pi rd) (base rs) f.toNat]
    else if -256 ≤ f ∧ f < 256 then [ldur (pi rd) (base rs) f] else [addr16 rs f, ldr (pi rd) 16 0]
  | .sd r2 r1 f =>
    if f % 8 = 0 ∧ 0 ≤ f ∧ f < 32768 then [str (pi r2) (base r1) f.toNat]
    else if -256 ≤ f ∧ f < 256 then [stur (pi r2) (base r1) f] else [addr16 r1 f, str (pi r2) 16 0]
  | .lbu rd rs f =>
    if rd = 0 then [] else if 0 ≤ f ∧ f < 4096 then [ldrb (pi rd) (base rs) f.toNat] else [addr16 rs f, ldrb (pi rd) 16 0]
  | .sb r2 r1 f => if 0 ≤ f ∧ f < 4096 then [strb (pi r2) (base r1) f.toNat] else [addr16 r1 f, strb (pi r2) 16 0]
  | .alu op rd a b => if rd = 0 then [] else pre a b ++ [rr (aluC op) (pi rd) (opA a) (opB b)]
  | .slli rd rs sh =>
    if rd = 0 then [] else (if rs = 2 then [addi 17 31 0] else []) ++ [movz 16 sh, rr 0x9AC02000 (pi rd) (opB rs) 16]
  | .srli rd rs sh =>
    if rd = 0 then [] else (if rs = 2 then [addi 17 31 0] else []) ++ [movz 16 sh, rr 0x9AC02400 (pi rd) (opB rs) 16]
  | .beq a b o => pre a b ++ [cmpR (opA a) (opB b), bc 0 (4 * o - (pre a b).length - 1)]
  | .bne a b o => pre a b ++ [cmpR (opA a) (opB b), bc 1 (4 * o - (pre a b).length - 1)]
  | .bltu a b o => pre a b ++ [cmpR (opA a) (opB b), bc 3 (4 * o - (pre a b).length - 1)]
  | .bgeu a b o => pre a b ++ [cmpR (opA a) (opB b), bc 2 (4 * o - (pre a b).length - 1)]
  | .jal rd o => if rd = 0 then [bB (4 * o)] else [PAD, PAD, PAD, blB (4 * o - 3)]
  | .jalr _ rs => [brR (pi rs)]

def blockJ (j : J) : List Nat := pad4 (body j)

/-- the instructions rv2arm accepts (its validation `c0`, at the J level; `n` = program length) -/
def validJ (n pc : Nat) : J → Prop
  | .addi rd rs _ => rdOK rs ∧ wrOK rd
  | .ld rd rs _ | .lbu rd rs _ => rs ≠ 0 ∧ rdOK rs ∧ wrOK rd
  | .sd r2 r1 _ | .sb r2 r1 _ => r1 ≠ 0 ∧ rdOK r1 ∧ wrOK r2
  | .alu op rd a b => 1 ≤ op ∧ op ≤ 8 ∧ rdOK a ∧ rdOK b ∧ wrOK rd
  | .slli rd rs sh | .srli rd rs sh => sh < 64 ∧ rdOK rs ∧ wrOK rd
  | .beq a b o | .bne a b o | .bltu a b o | .bgeu a b o =>
    rdOK a ∧ rdOK b ∧ 0 ≤ (pc : Int) + o ∧ (pc : Int) + o < n ∧ -65535 ≤ o ∧ o ≤ 65535
  | .jal rd o => (rd = 0 ∨ rd = 1) ∧ 0 ≤ (pc : Int) + o ∧ (pc : Int) + o < n
  | .jalr rd rs => rd = 0 ∧ pi rs < 31

/-! ## J with link width W (V2). `stepW 4 = CallProbe.step` (same text with 4 replaced by W). -/
def stepW (W : Nat) (C : List J) : Nat × St → Option (Nat × St)
  | (pc, s) => match C[pc]? with
    | some (.jal rd off) => some (((pc : Int) + off).toNat, wr s rd (UInt64.ofNat (s.b + W * (pc + 1))))
    | some (.jalr rd rs) => some (((s.x rs).toNat - s.b) / W, wr s rd (UInt64.ofNat (s.b + W * (pc + 1))))
    | _ => step C (pc, s)

/-! ## the relation -/
/-- little-endian bytes of the code words -/
def codeBytes (ws : List Nat) : List UInt8 :=
  ws.flatMap fun w => [w.toUInt8, (w / 2^8).toUInt8, (w / 2^16).toUInt8, (w / 2^24).toUInt8]
def codeA (C : List J) : List UInt8 := codeBytes ((C.map blockJ).flatten)

/-- `RelA M C D K (pc, s) t`: A64 state t represents J state (pc, s) of program C.
`D` = the data addresses (8-aligned cells of J memory: work block, input, output), `K` = the values of the
registers the code must keep (x18..x29). Scratch x16/x17, NZCV and every other piece of machine state are free. -/
structure RelA (M : Machine) (C : List J) (D : Nat → Prop) (K : Nat → UInt64) (ps : Nat × St) (t : M.State) : Prop where
  cfg : M.configured t
  pc : (M.observe t).programCounter.toNat = ps.2.b + 16 * ps.1
  regs : ∀ r, live r → (M.observe t).register (pi r) = ps.2.x r
  sp : (M.observe t).register 31 = ps.2.x 2
  zero : ps.2.x 0 = 0
  keep : ∀ r, 18 ≤ r → r ≤ 29 → (M.observe t).register r = K r
  code : ∀ i (h : i < (codeA C).length), (M.observe t).memory (UInt64.ofNat (ps.2.b + i)) = some (codeA C)[i]
  mem : ∀ a k, D a → k < 8 → (M.observe t).memory (UInt64.ofNat (a + k)) = some ((ps.2.m a >>> (8 * k).toUInt64).toUInt8)
  dAl : ∀ a, D a → a % 8 = 0
  dCode : ∀ a, D a → a + 8 ≤ ps.2.b ∨ ps.2.b + (codeA C).length ≤ a
  ram : ps.2.b + (codeA C).length ≤ M.ramEnd ∧ ∀ a, D a → a + 8 ≤ M.ramEnd

/-- the J step's memory accesses hit D (8-byte: the cell itself; byte: its cell), and a `jalr` target is a block -/
def AccOK (C : List J) (D : Nat → Prop) : Nat × St → Prop
  | (pc, s) => match C[pc]? with
    | some (.ld _ rs off) => D (ea (s.x rs) off)
    | some (.sd _ r1 off) => D (ea (s.x r1) off)
    | some (.lbu _ rs off) => D (ea (s.x rs) off - ea (s.x rs) off % 8)
    | some (.sb _ r1 off) => D (ea (s.x r1) off - ea (s.x r1) off % 8)
    | some (.jalr _ rs) => s.b ≤ (s.x rs).toNat ∧ ((s.x rs).toNat - s.b) % 16 = 0
    | _ => True

/-- **Block correctness** (the statement to prove for `M := arm`): if the J instruction at pc is valid, its accesses
are in D, and t represents (pc, s), then the A64 block runs (≤ 4 steps) to a state representing J's next state. -/
def BlockOK (M : Machine) : Prop :=
  ∀ (C : List J) (D : Nat → Prop) (K : Nat → UInt64) (pc : Nat) (s : St) (j : J) (t : M.State) (ps' : Nat × St),
    C[pc]? = some j → validJ C.length pc j → AccOK C D (pc, s) → RelA M C D K (pc, s) t →
    stepW 16 C (pc, s) = some ps' → ∃ t', Runs M t t' ∧ RelA M C D K ps' t'

end ArmBlock

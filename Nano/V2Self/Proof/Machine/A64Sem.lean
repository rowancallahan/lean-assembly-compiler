/- The ABSTRACT AArch64 step interface `A64Sem M` for the ARM adapter (Sail-free; any `Machine` whose instructions
behave so). One field per instruction form the rv2arm blocks use (ArmEnc.body; Testing/nano/v2self/arm/PROOF_NOTES.md),
each stated through `observe` only, like the Sail `full_*` lemmas:
* the word sits at the pc (`WordAt`, little-endian bytes), the pc is a 4-aligned address in RAM (`PcOK`), the
  machine is `configured`, register fields are < 31 (no xzr / sp), immediates are in range;
* the fetched bytes are executable (`FetchX`), the bytes a load or store touches are readable/writable (`W`);
* then the machine RUNS (`GoesK`: some `Runs`, configured again, permissions kept) to the stated observable state.
Model providers (the DeepMind surrogate `Arm/apc`, later the Sail model) instantiate it; `ArmTarget` proves the
adapter's laws from it.  `subs` + `b.cond` are ONE field (`cmpbr`): NZCV is not observable, and the blocks only
use the flags of their own `subs`. -/
import Nano.V2Self.Proof.Machine.Target
import Nano.V2Self.Proof.Machine.ArmEnc
namespace JT
open Proven.Top

/-- the 32-bit word `w` is stored little-endian at byte address `a` -/
def WordAt (o : MachineState) (a w : Nat) : Prop :=
  ∀ k < 4, o.memory (UInt64.ofNat (a + k)) = some (wbyte (BitVec.ofNat 32 w) k)

/-- the pc is a 4-aligned word address in RAM (what a model needs to fetch) -/
def PcOK (M : Machine) (o : MachineState) : Prop :=
  o.programCounter.toNat % 4 = 0 ∧ M.ramStart ≤ o.programCounter.toNat ∧ o.programCounter.toNat + 4 ≤ M.ramEnd

/-- the bytes `pc .. pc + n − 1` are fetchable (`X`: executable) -/
def FetchX (M : Machine) (X : M.State → Nat → Prop) (s : M.State) (n : Nat) : Prop :=
  ∀ k < n, X s ((M.observe s).programCounter.toNat + k)

/-- a run keeps the permissions (`X`: executable, `W`: readable and writable bytes) -/
def Keep {M : Machine} (X W : M.State → Nat → Prop) (s s' : M.State) : Prop :=
  (∀ a, X s a → X s' a) ∧ (∀ a, W s a → W s' a)

/-- the machine runs from `s` to a configured state that shows `o`, keeping the permissions -/
def GoesK (M : Machine) (X W : M.State → Nat → Prop) (s : M.State) (o : MachineState) : Prop :=
  ∃ s', Runs M s s' ∧ M.configured s' ∧ M.observe s' = o ∧ Keep X W s s'

/-- byte `a` is in one of the call's data blocks (input, output, work) -/
def InBlocks (call : Call) (a : Nat) : Prop :=
  (call.inputAddress.toNat ≤ a ∧ a < call.inputAddress.toNat + call.inputLength) ∨
  (call.outputAddress.toNat ≤ a ∧ a < call.outputAddress.toNat + call.outputLength) ∨
  (call.workAddress.toNat ≤ a ∧ a < call.workAddress.toNat + call.workLength)

/-- `o` after an instruction that writes register `d` with `v` and falls through -/
def setReg (o : MachineState) (d : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, fun r => if r = d then v else o.register r, o.memory⟩

/-- `o` after a jump to `t` that writes no register -/
def jumpTo (o : MachineState) (t : UInt64) : MachineState := ⟨t, o.register, o.memory⟩

/-- the register ALU values (ArmEnc.aluC numbering): add, sub, madd (+ x17), and, orr, lslv, lsrv, eor -/
def aluV (op : Nat) (a b z : UInt64) : UInt64 :=
  if op = 1 then a + b else if op = 2 then a - b else if op = 3 then z + a * b else if op = 4 then a &&& b
  else if op = 5 then a ||| b else if op = 6 then a <<< b else if op = 7 then a >>> b else a ^^^ b

/-- the b.cond conditions the blocks use, after `subs x16, xa, xb`: EQ 0, NE 1, HS 2, LO 3 -/
def condV (c : Nat) (a b : UInt64) : Bool :=
  if c = 0 then a == b else if c = 1 then a != b else if c = 2 then decide (b.toNat ≤ a.toNat) else decide (a.toNat < b.toNat)

/-- `movk`'s new register value -/
def movkV (old : UInt64) (i h : Nat) : UInt64 :=
  (old &&& ~~~((0xFFFF : UInt64) <<< (16 * h).toUInt64)) ||| ((UInt64.ofNat i) <<< (16 * h).toUInt64)

/-- `o`'s memory after an 8-byte store of `v` at `a` -/
def store8 (o : MachineState) (a : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, o.register,
    fun u => if a ≤ u.toNat ∧ u.toNat < a + 8 then some (cbyte v (u.toNat - a)) else o.memory u⟩

/-- `o`'s memory after a byte store of `v`'s low byte at `a` -/
def store1 (o : MachineState) (a : Nat) (v : UInt64) : MachineState :=
  ⟨o.programCounter + 4, o.register, fun u => if u.toNat = a then some v.toUInt8 else o.memory u⟩

/-- **the A64 step facts the ARM blocks need** (all register fields < 31), over permission predicates `X`
(byte executable) and `W` (byte readable and writable): fetches need `X` at the pc, loads and stores need `W` on the
bytes they touch, and every step keeps both (W^X models such as DeepMind's; Sail: both `True`) -/
structure A64Sem (M : Machine) (X W : M.State → Nat → Prop) : Prop where
  /-- the calling convention and the RAM window -/
  map : M.mapping = armMapping
  ram : 2048 ≤ M.ramStart ∧ M.ramEnd ≤ 2 ^ 32
  /-- at a call's start the code is executable and the data blocks are readable and writable -/
  perm_init : ∀ (s : M.State) (call : Call) (code x : List UInt8), StartCorrect M s call code x →
    (∀ a, (M.observe s).programCounter.toNat ≤ a → a < (M.observe s).programCounter.toNat + code.length → X s a) ∧
    (∀ a, InBlocks call a → W s a)
  /-- `movz xd, #i` -/
  movz : ∀ (s : M.State) (d i : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → i < 2 ^ 16 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.movz d i) →
    GoesK M X W s (setReg (M.observe s) d (UInt64.ofNat i))
  /-- `movk xd, #i, lsl 16h` -/
  movk : ∀ (s : M.State) (d i h : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → i < 2 ^ 16 → h < 4 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.movk d i h) →
    GoesK M X W s (setReg (M.observe s) d (movkV ((M.observe s).register d) i h))
  /-- `add xd, xn, #i` -/
  addi : ∀ (s : M.State) (d n i : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → n < 31 → i < 4096 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.addi d n i) →
    GoesK M X W s (setReg (M.observe s) d ((M.observe s).register n + UInt64.ofNat i))
  /-- `sub xd, xn, #i` -/
  subi : ∀ (s : M.State) (d n i : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → n < 31 → i < 4096 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.subi d n i) →
    GoesK M X W s (setReg (M.observe s) d ((M.observe s).register n - UInt64.ofNat i))
  /-- the register ALU `add/sub/madd(+x17)/and/orr/lslv/lsrv/eor xd, xn, xm` -/
  alu : ∀ (s : M.State) (op d n m : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → 1 ≤ op → op ≤ 8 → d < 31 → n < 31 → m < 31 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.rr (ArmEnc.aluC op) d n m) →
    GoesK M X W s (setReg (M.observe s) d (aluV op ((M.observe s).register n) ((M.observe s).register m)
      ((M.observe s).register 17)))
  /-- `subs x16, xn, xm; b.cond f` (c: EQ 0, NE 1, HS 2, LO 3; f in words, from the b.cond) -/
  cmpbr : ∀ (s : M.State) (c n m : Nat) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 8 → c < 4 → n < 31 → m < 31 →
    -2 ^ 18 ≤ f → f < 2 ^ 18 → (M.observe s).programCounter.toNat + 8 ≤ M.ramEnd →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.subsR n m) →
    WordAt (M.observe s) ((M.observe s).programCounter.toNat + 4) (ArmEnc.bc c f) →
    GoesK M X W s ⟨if condV c ((M.observe s).register n) ((M.observe s).register m)
        then (M.observe s).programCounter + 4 + 4 * UInt64.ofInt f else (M.observe s).programCounter + 8,
      fun r => if r = 16 then (M.observe s).register n - (M.observe s).register m else (M.observe s).register r,
      (M.observe s).memory⟩
  /-- `cbz xt, f` -/
  cbz : ∀ (s : M.State) (t : Nat) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → -2 ^ 18 ≤ f → f < 2 ^ 18 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.cbz t f) →
    GoesK M X W s (jumpTo (M.observe s) (if (M.observe s).register t = 0
      then (M.observe s).programCounter + 4 * UInt64.ofInt f else (M.observe s).programCounter + 4))
  /-- `b f` -/
  b : ∀ (s : M.State) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → -2 ^ 25 ≤ f → f < 2 ^ 25 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.bB f) →
    GoesK M X W s (jumpTo (M.observe s) ((M.observe s).programCounter + 4 * UInt64.ofInt f))
  /-- `bl f` (x30 := the next word's address) -/
  bl : ∀ (s : M.State) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → -2 ^ 25 ≤ f → f < 2 ^ 25 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.blB f) →
    GoesK M X W s ⟨(M.observe s).programCounter + 4 * UInt64.ofInt f,
      fun r => if r = 30 then (M.observe s).programCounter + 4 else (M.observe s).register r, (M.observe s).memory⟩
  /-- `br xn` -/
  br : ∀ (s : M.State) (n : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → n < 31 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.brR n) →
    GoesK M X W s (jumpTo (M.observe s) ((M.observe s).register n))
  /-- `ldr xt, [xn, #f]` (8-aligned address in RAM; the loaded value is the one whose bytes are there) -/
  ldr : ∀ (s : M.State) (t n f : Nat) (v : UInt64), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 → f % 8 = 0 → f < 32768 →
    ((M.observe s).register n).toNat + f < 2 ^ 64 → (((M.observe s).register n).toNat + f) % 8 = 0 →
    M.ramStart ≤ ((M.observe s).register n).toNat + f → ((M.observe s).register n).toNat + f + 8 ≤ M.ramEnd →
    (∀ k < 8, W s (((M.observe s).register n).toNat + f + k)) →
    (∀ k < 8, (M.observe s).memory (UInt64.ofNat (((M.observe s).register n).toNat + f + k)) = some (cbyte v k)) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.ldr t n f) →
    GoesK M X W s (setReg (M.observe s) t v)
  /-- `str xt, [xn, #f]` -/
  str : ∀ (s : M.State) (t n f : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 → f % 8 = 0 → f < 32768 →
    ((M.observe s).register n).toNat + f < 2 ^ 64 → (((M.observe s).register n).toNat + f) % 8 = 0 →
    M.ramStart ≤ ((M.observe s).register n).toNat + f → ((M.observe s).register n).toNat + f + 8 ≤ M.ramEnd →
    (∀ k < 8, W s (((M.observe s).register n).toNat + f + k)) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.str t n f) →
    GoesK M X W s (store8 (M.observe s) (((M.observe s).register n).toNat + f) ((M.observe s).register t))
  /-- `ldrb wt, [xn, #f]` (zero-extended) -/
  ldrb : ∀ (s : M.State) (t n f : Nat) (b : UInt8), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 → f < 4096 →
    ((M.observe s).register n).toNat + f < 2 ^ 64 →
    M.ramStart ≤ ((M.observe s).register n).toNat + f → ((M.observe s).register n).toNat + f < M.ramEnd →
    W s (((M.observe s).register n).toNat + f) →
    (M.observe s).memory (UInt64.ofNat (((M.observe s).register n).toNat + f)) = some b →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.ldrb t n f) →
    GoesK M X W s (setReg (M.observe s) t b.toUInt64)
  /-- `strb wt, [xn, #f]` -/
  strb : ∀ (s : M.State) (t n f : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 → f < 4096 →
    ((M.observe s).register n).toNat + f < 2 ^ 64 →
    M.ramStart ≤ ((M.observe s).register n).toNat + f → ((M.observe s).register n).toNat + f < M.ramEnd →
    W s (((M.observe s).register n).toNat + f) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.strb t n f) →
    GoesK M X W s (store1 (M.observe s) (((M.observe s).register n).toNat + f) ((M.observe s).register t))

end JT

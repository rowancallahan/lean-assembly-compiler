/- `A64SemN M X W`: `A64Sem` (the rv2arm blocks' instruction forms) PLUS the eight forms only the native generator
`C/GenArm.lean` emits (Testing/notes/NATIVE_ARM_PROOF_PLAN.md, step A): `movn`, `movz` with a shift, `cbnz`, `ldur`, `stur`,
`ldp`, `ldrb` (register offset), `add` (register, lsl #3).  A separate structure, not new `A64Sem` fields, so the existing
instances and the rv2arm top theorems need nothing new; a model that proves `A64SemN` gives `A64Sem` by `toA64Sem`.
Same conventions as `A64Sem`: register fields < 31, statements through `observe`, `X`/`W` permissions.
The words are GenArm's (`a4 a_14`, `a3 a_23`, `a36 a_17/a_18`, `a32`, `a3 945842176`, `a34`), as `Nat`. -/
import Nano.Run.A64Sem
namespace ArmEnc

/-- `movz xd, #i, lsl 16h` (GenArm's first word of a constant whose low chunks are 0) -/
def movzH (d i h : Nat) : Nat := 0xD2800000 + h * 2^21 + i * 2^5 + d
/-- `movn xd, #i, lsl 16h` -/
def movn (d i h : Nat) : Nat := 0x92800000 + h * 2^21 + i * 2^5 + d
/-- `cbnz xt, f` -/
def cbnz (t : Nat) (f : Int) : Nat := 0xB5000000 + mo f 19 * 2^5 + t
/-- `ldur xt, [xn, #f]` (f a signed 9-bit byte offset) -/
def ldur (t n : Nat) (f : Int) : Nat := 0xF8400000 + mo f 9 * 2^12 + n * 2^5 + t
/-- `stur xt, [xn, #f]` -/
def stur (t n : Nat) (f : Int) : Nat := 0xF8000000 + mo f 9 * 2^12 + n * 2^5 + t
/-- `ldp xt, xu, [xn]` (xt := [xn], xu := [xn + 8]) -/
def ldp (t u n : Nat) : Nat := 0xA9400000 + u * 2^10 + n * 2^5 + t
/-- `ldrb wt, [xn, xm]` -/
def ldrbR (t n m : Nat) : Nat := 0x38606800 + m * 2^16 + n * 2^5 + t
/-- `add xd, xn, xm, lsl #3` -/
def addLsl3 (d n m : Nat) : Nat := 0x8B000C00 + m * 2^16 + n * 2^5 + d

end ArmEnc
namespace JT
open Proven.Top

/-- `movn`'s register value -/
def movnV (i h : Nat) : UInt64 := ~~~((UInt64.ofNat i) <<< (16 * h).toUInt64)

/-- `o` after `ldp xt, xu, [..]` loaded `v1`, `v2` -/
def setReg2 (o : MachineState) (t u : Nat) (v1 v2 : UInt64) : MachineState :=
  ⟨o.programCounter + 4, fun r => if r = u then v2 else if r = t then v1 else o.register r, o.memory⟩

/-- **the A64 step facts the native generator needs**: `A64Sem` and the seven extra forms -/
structure A64SemN (M : Machine) (X W : M.State → Nat → Prop) : Prop extends A64Sem M X W where
  /-- `movn xd, #i, lsl 16h` -/
  movn : ∀ (s : M.State) (d i h : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → i < 2 ^ 16 → h < 4 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.movn d i h) →
    GoesK M X W s (setReg (M.observe s) d (movnV i h))
  /-- `movz xd, #i, lsl 16h` -/
  movzH : ∀ (s : M.State) (d i h : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → i < 2 ^ 16 → h < 4 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.movzH d i h) →
    GoesK M X W s (setReg (M.observe s) d ((UInt64.ofNat i) <<< (16 * h).toUInt64))
  /-- `cbnz xt, f` -/
  cbnz : ∀ (s : M.State) (t : Nat) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → -2 ^ 18 ≤ f → f < 2 ^ 18 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.cbnz t f) →
    GoesK M X W s (jumpTo (M.observe s) (if (M.observe s).register t = 0
      then (M.observe s).programCounter + 4 else (M.observe s).programCounter + 4 * UInt64.ofInt f))
  /-- `ldur xt, [xn, #f]` (the address `a = x[n] + f`, 8-aligned, in RAM) -/
  ldur : ∀ (s : M.State) (t n a : Nat) (f : Int) (v : UInt64), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 →
    -256 ≤ f → f < 256 → (a : Int) = ((M.observe s).register n).toNat + f → a % 8 = 0 →
    M.ramStart ≤ a → a + 8 ≤ M.ramEnd → (∀ k < 8, W s (a + k)) →
    (∀ k < 8, (M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte v k)) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.ldur t n f) →
    GoesK M X W s (setReg (M.observe s) t v)
  /-- `stur xt, [xn, #f]` -/
  stur : ∀ (s : M.State) (t n a : Nat) (f : Int), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 →
    -256 ≤ f → f < 256 → (a : Int) = ((M.observe s).register n).toNat + f → a % 8 = 0 →
    M.ramStart ≤ a → a + 8 ≤ M.ramEnd → (∀ k < 8, W s (a + k)) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.stur t n f) →
    GoesK M X W s (store8 (M.observe s) a ((M.observe s).register t))
  /-- `ldp xt, xu, [xn]` (`t ≠ u`; 8-aligned address in RAM; xt := the cell at x[n], xu := the next cell) -/
  ldp : ∀ (s : M.State) (t u n : Nat) (v1 v2 : UInt64), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → u < 31 → n < 31 →
    t ≠ u → ((M.observe s).register n).toNat % 8 = 0 →
    M.ramStart ≤ ((M.observe s).register n).toNat → ((M.observe s).register n).toNat + 16 ≤ M.ramEnd →
    (∀ k < 16, W s (((M.observe s).register n).toNat + k)) →
    (∀ k < 8, (M.observe s).memory (UInt64.ofNat (((M.observe s).register n).toNat + k)) = some (cbyte v1 k)) →
    (∀ k < 8, (M.observe s).memory (UInt64.ofNat (((M.observe s).register n).toNat + 8 + k)) = some (cbyte v2 k)) →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.ldp t u n) →
    GoesK M X W s (setReg2 (M.observe s) t u v1 v2)
  /-- `ldrb wt, [xn, xm]` (zero-extended) -/
  ldrbR : ∀ (s : M.State) (t n m : Nat) (b : UInt8), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → t < 31 → n < 31 → m < 31 →
    M.ramStart ≤ ((M.observe s).register n).toNat + ((M.observe s).register m).toNat →
    ((M.observe s).register n).toNat + ((M.observe s).register m).toNat < M.ramEnd →
    W s (((M.observe s).register n).toNat + ((M.observe s).register m).toNat) →
    (M.observe s).memory (UInt64.ofNat (((M.observe s).register n).toNat + ((M.observe s).register m).toNat)) = some b →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.ldrbR t n m) →
    GoesK M X W s (setReg (M.observe s) t b.toUInt64)
  /-- `add xd, xn, xm, lsl #3` -/
  addLsl3 : ∀ (s : M.State) (d n m : Nat), M.configured s → PcOK M (M.observe s) → FetchX M X s 4 → d < 31 → n < 31 → m < 31 →
    WordAt (M.observe s) (M.observe s).programCounter.toNat (ArmEnc.addLsl3 d n m) →
    GoesK M X W s (setReg (M.observe s) d ((M.observe s).register n + ((M.observe s).register m <<< 3)))

end JT

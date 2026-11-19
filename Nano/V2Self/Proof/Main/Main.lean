/- Nano/V2Self/Proof/Main/Main: the END-TO-END statement for C's driver `m x = g41 x (o41 (y16 (s10 x)))` (build_self_S.py).
(1) `Sem`: the meaning of ParSpec's resolved program (`List DefA`) on an input, word level, with buffer capacity κ;
(2) `ImplementsC`: bytes `B` loaded as RV64 code (Sail, `Spec/Implements1.lean` conventions) implement `f`, where the run
    may also end in out-of-memory, but only below a per-input work size `space x`;
(3) the stage hypotheses `ParStage` (parser, = `ParInv.ParserSound`), `OwnStage` (O's ownership stage o41 accepts only
    `LinearK` programs) and `GenStage` (codegen + machine bridge, for linear programs); the lexer is proved
    (`LexSpec.s10_sound`);
(4) `compiler_correct`: m x ≠ [] → ∃ ts p, Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ ImplementsC (m x) (Sem κ p).
Notes: Testing/notes/NANO_V2_MAIN.md. -/
import Nano.V2Self.Proof.Main.Sem
import Spec.Implements1

namespace NanoMain
open ParSpec

/-! ## the machine contract -/
open Proven

def a0Ok (y : List UInt8) : BitVec 64 := if y = [] then 1 else 0
def a0Oom : BitVec 64 := BitVec.ofInt 64 (-1)
def a0Cap : BitVec 64 := BitVec.ofInt 64 (-2)

/-- what a finished run shows for the semantic result `r`; `oomOK`: work memory below the bound, so out-of-memory
(a0 = −1, a1 = 0, nothing outside the output block and the work block written) is also allowed -/
def Outcome (s : St) (ra : BitVec 64) (output work : Region) (r : Except Stop (List UInt8)) (oomOK : Prop)
    (s' : St) : Prop :=
  s'.regs.get? .PC = some ra ∧ abiSavedKept s s' ∧ Cfg s' ∧
  ((match r with
    | .ok y => s'.regs.get? .x10 = some (a0Ok y) ∧ s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length) ∧
        bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
        unchangedOutside s s' [⟨output.base, y.length⟩, work]
    | .error .cap => s'.regs.get? .x10 = some a0Cap ∧ s'.regs.get? .x11 = some 0 ∧
        unchangedOutside s s' [output, work]
    | .error .stuck => True) ∨
   (oomOK ∧ s'.regs.get? .x10 = some a0Oom ∧ s'.regs.get? .x11 = some 0 ∧ unchangedOutside s s' [output, work]))

/-- **`B` (bytes, 4 per instruction word, little endian) implements `f`**: calling convention and hosting as
`Proven.Implements1With` (a0 input, a1 length, a2 work base, a3 output, sp = work top, ra), inputs of at most `maxLen`
bytes, output block large enough for an ok result.  There is ONE work-size bound per input (`space`, existential):
with at least `space x` bytes of work memory the run never reports out-of-memory. -/
def ImplementsCW (B : List UInt8) (f : List UInt8 → Except Stop (List UInt8)) (space : List UInt8 → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input output work : Region),
    let codeR : Region := ⟨entry.toNat, B.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 → B.length % 4 = 0 →
    bytesAt s entry.toNat B.length = B.map (some ·.toBitVec) →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → (∀ y, f x = .ok y → y.length ≤ output.len) → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise disjoint →
    Mapped s output → Mapped s work →
    runsTo s (Outcome s ra output work (f x) (work.len < space x))

/-- `ImplementsCW` for some work bound -/
def ImplementsC (B : List UInt8) (f : List UInt8 → Except Stop (List UInt8)) (maxLen : Nat := 2 ^ 20) : Prop :=
  ∃ space : List UInt8 → Nat, ImplementsCW B f space maxLen

/-- codegen (box A: g41's output is the code of the AST; box E: that code runs on Sail as `Sem`): for every parsed
linear program `p`, a non-empty result of Gen on `serialize p` implements `Sem κC p` -/
def GenStage : Prop :=
  ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 → LinearK p →
    C.g41 c (serialize p) ≠ [] → ImplementsC (C.g41 c (serialize p)) (Sem κC p)

/-! ## the end-to-end theorem -/

/-- **C is sound on success**: if the driver emits code for source `x` (at most 2^20 bytes), then `x` lexes (Lex2Spec) and
parses (ParSpec) to a program `p`, and the emitted bytes implement `p`'s meaning on Sail (outcomes: the result, the
capacity trap when `Sem` reports it, out-of-memory only below the work bound). -/
theorem compiler_correct (HP : ParStage) (HO : OwnStage) (HB : BndStage) (HG : GenStage) (x : List UInt8) (hx : x.length ≤ 2 ^ 20)
    (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ ImplementsC (mC x) (Sem κC p) := by
  have hy0 : C.o41 (C.y16 (C.s10 x)) ≠ [] := fun e => h (by simp only [mC, e, g41_nil])
  have hoe := o41_ne _ hy0
  have hy : C.y16 (C.s10 x) ≠ [] := by rw [← hoe]; exact hy0
  by_cases h0 : C.s10 x = []
  · obtain ⟨p, hp, -⟩ := HP _ ⟨[], by rw [h0]; exact ParSpec.TokL.nil⟩ (by simp [h0]) hy
    rw [h0] at hp; simp [ParsesProgram, refParse_nil] at hp
  · have hL := LexSpec.s10_sound x (by omega) _ rfl h0
    have hb := lexes_len hL
    obtain ⟨p, hp, he⟩ := HP _ (lexes_tokWF hL) (by omega) hy
    have hg : C.g41 x (serialize p) ≠ [] := by rw [← he, ← hoe]; exact h
    have hts : (C.s10 x).length < 2 ^ 24 := by omega
    have hbd := HB x _ p hp hts hg
    have hsl : (serialize p).length < 2 ^ 64 := by have := ParSerLen.ser_lt hp hts; omega
    have hlin : LinearK p := HO _ p hp hbd hsl (by rw [← he]; exact hy0)
    refine ⟨_, p, hL, hp, hlin, ?_⟩
    have := HG x _ p hp hts hlin hg
    rw [mC, hoe, he]; exact this

end NanoMain

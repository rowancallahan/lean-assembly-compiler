/- The `XPipe` compiler with the merge sort: pipes containing `List.mergeSort` are compiled through `BStmt`
(`XPipe.progB`, `compileBF` with 7 spill slots, blocks input / output / scratch), all others as before
(`compileXA`).  Theorem: `compileX_ok : compileX p = .ok code →
ImplementsPipeS code p.denote p.space p.sspace (XPipe.stack p)` — `ImplementsPipeLen` plus a scratch block of
`p.sspace |x|` bytes and a stack of `XPipe.stack p` bytes (71 with a sort, else 0). -/
import Compiler.Front.PipeStdB

set_option linter.unusedVariables false

namespace Proven

/-! ## Checking `BStmt.wf` -/

def BExp.vltB (m : Nat) : BExp → Bool
  | .var i => decide (i < m)
  | .const _ => true
  | .bin _ a b => a.vltB m && b.vltB m
  | .ite c a b => c.vltB m && a.vltB m && b.vltB m

theorem BExp.vltB_iff (m : Nat) : ∀ e : BExp, e.vltB m = true ↔ e.vlt m
  | .var i => by simp [BExp.vltB, BExp.vlt]
  | .const _ => by simp [BExp.vltB, BExp.vlt]
  | .bin _ a b => by simp [BExp.vltB, BExp.vlt, BExp.vltB_iff m a, BExp.vltB_iff m b]
  | .ite c a b => by simp [BExp.vltB, BExp.vlt, BExp.vltB_iff m a, BExp.vltB_iff m b, BExp.vltB_iff m c, and_assoc]

def wfErrB (N : Nat) (bv : List Nat) : BStmt → Option String
  | .assign v e =>
    if e.depth < 7 ∧ e.vltB (8 + N) = true ∧ v < 8 + N ∧ v ∉ bv then none
    else some s!"assignment to v{v}: expression needs {e.depth + 1} temporaries (limit 7)"
  | .load v b i =>
    if i.depth < 6 ∧ i.vltB (8 + N) = true ∧ v < 8 + N ∧ v ∉ bv ∧ b < bv.length then none
    else some s!"load into v{v}: index expression needs {i.depth + 2} temporaries (limit 7)"
  | .store b i e =>
    if i.depth < 6 ∧ e.depth < 6 ∧ i.vltB (8 + N) = true ∧ e.vltB (8 + N) = true ∧ b < bv.length then none
    else some s!"store: expression needs {max i.depth e.depth + 2} temporaries (limit 7)"
  | .seq p q => match wfErrB N bv p with
    | some m => some m
    | none => wfErrB N bv q
  | .loop c body =>
    if c.depth < 7 ∧ c.vltB (8 + N) = true ∧ (genB c 0).length + (compileB bv body).length + 2 < 1024 then
      wfErrB N bv body
    else some s!"loop too long: {(genB c 0).length + (compileB bv body).length + 2} words (limit 1023, the reach of beq)"

theorem wfErrB_iff (N : Nat) (bv : List Nat) : ∀ p : BStmt, wfErrB N bv p = none ↔ p.wf N bv
  | .assign v e => by simp only [wfErrB, BStmt.wf, ← BExp.vltB_iff]; split <;> simp_all
  | .load v b i => by simp only [wfErrB, BStmt.wf, ← BExp.vltB_iff]; split <;> simp_all
  | .store b i e => by simp only [wfErrB, BStmt.wf, ← BExp.vltB_iff]; split <;> simp_all
  | .seq p q => by
    simp only [wfErrB, BStmt.wf, ← wfErrB_iff N bv p, ← wfErrB_iff N bv q]
    cases wfErrB N bv p <;> simp
  | .loop c body => by
    simp only [wfErrB, BStmt.wf, ← BExp.vltB_iff, ← wfErrB_iff N bv body]
    split <;> simp_all

/-! ## The compiler -/

/-- pipes with a sort: `BStmt` with 7 slots, blocks `[input, output, scratch]` with bases `a0`, `a3`, `a2` -/
def compileXB (p : XPipe) : Except String (List (BitVec 32)) :=
  match XPipe.chkErr p with
  | some m => .error m
  | none => match wfErrB 7 [0, 3, 2] (XPipe.progB p) with
    | some m => .error m
    | none => .ok (compileBF 7 [0, 3, 2] (XPipe.progB p))

theorem compileXB_inv {p : XPipe} {code : List (BitVec 32)} (h : compileXB p = .ok code) :
    (∀ st ∈ p, st.chk = none) ∧ (XPipe.progB p).wf 7 [0, 3, 2] ∧ code = compileBF 7 [0, 3, 2] (XPipe.progB p) := by
  unfold compileXB at h
  cases hc : XPipe.chkErr p with
  | some m => simp [hc] at h
  | none =>
    cases hw : wfErrB 7 [0, 3, 2] (XPipe.progB p) with
    | some m => simp [hc, hw] at h
    | none =>
      simp only [hc, hw, Except.ok.injEq] at h
      exact ⟨XPipe.chkErr_none hc, (wfErrB_iff _ _ _).1 hw, h.symm⟩

def XPipe.hasSort (p : XPipe) : Bool := p.any XStage.isSort

/-- stack bytes: the frame of `compileBF` with 7 slots (64 bytes) plus up to 7 bytes of alignment -/
def XPipe.stack (p : XPipe) : Nat := if p.hasSort then 71 else 0

/-- **The compiler used by `compile%`**: the merge sort for pipes with `List.mergeSort`, else `compileXA` -/
def compileX (p : XPipe) : Except String (List (BitVec 32)) :=
  if p.hasSort then compileXB p else compileXA p

/-! ## The specification -/

/-- `ImplementsPipeLen` with a scratch block of `sspace |x|` bytes (present in the memory map) and a stack of
`stackLen` bytes below `sp` -/
def ImplementsPipeS (code : List (BitVec 32)) (f : List UInt8 → List UInt8) (space sspace : Nat → Nat)
    (stackLen : Nat) (maxLen : Nat := 2 ^ 20) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input scratch output stack : Region),
    let codeR : Region := ⟨entry.toNat, 4 * code.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 scratch.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (stack.base + stack.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → space x.length ≤ output.len → sspace x.length ≤ scratch.len → stackLen ≤ stack.len →
    (∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM) →
    [input, scratch, output, stack, codeR].Pairwise disjoint →
    (∀ i < space x.length, (s.mem[output.base + i]?).isSome) →
    (∀ i < sspace x.length, (s.mem[scratch.base + i]?).isSome) →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base (f x).length = (f x).map (some ·.toBitVec) ∧
      unchangedOutside s s' [input, scratch, output, stack] ∧ calleeSavedKept s s' ∧ Cfg s' ∧
      s'.regs.get? .x11 = some (BitVec.ofNat 64 (f x).length)

theorem ImplementsPipeLen.toS {code : List (BitVec 32)} {f : List UInt8 → List UInt8} {space : Nat → Nat}
    (h : ImplementsPipeLen code f space) (sspace : Nat → Nat) (stackLen : Nat) :
    ImplementsPipeS code f space sspace stackLen := by
  intro x s entry ra input scratch output stack codeR hmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    hs hk h16 h17 h18 hm
  exact h x s entry ra input scratch output stack hmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18

end Proven

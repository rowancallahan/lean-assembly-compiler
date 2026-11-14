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

/-! ## From a `BStmt` run to the specification -/

theorem implementsS_of_execB {prog : BStmt} (hwf : prog.wf 7 [0, 3, 2]) {f : List UInt8 → List UInt8}
    {space sspace : Nat → Nat}
    (hex : ∀ (xs : List UInt8) (out scr : List (BitVec 8)) (env : BEnv), env 1 = .ofNat 64 xs.length →
      xs.length < 2 ^ 32 → space xs.length ≤ out.length → out.length < 2 ^ 32 →
      sspace xs.length ≤ scr.length → scr.length < 2 ^ 32 →
      ∃ τ' out' scr', BExec prog ⟨env, [tbs xs, out, scr]⟩ τ' ∧ τ'.heap = [tbs xs, out', scr'] ∧
        out'.length = out.length ∧ out'.take (f xs).length = tbs (f xs) ∧ τ'.env 1 = .ofNat 64 (f xs).length) :
    ImplementsPipeS (compileBF 7 [0, 3, 2] prog) f space sspace 71 := by
  intro x s entry ra input scratch output stack codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hsl hstk hram hdis hmap hmapS
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri rs ro rst rc
  unfold disjoint at d12 d13 d14 d15 d23 d24 d25 d34 d35 d45
  simp only [codeR] at d15 d25 d35 d45 rc
  obtain ⟨L, hLe⟩ : ∃ L, L = space x.length := ⟨_, rfl⟩
  obtain ⟨L2, hL2e⟩ : ∃ L2, L2 = sspace x.length := ⟨_, rfl⟩
  rw [← hLe] at hol hmap
  rw [← hL2e] at hsl hmapS
  have hil' : input.len = x.length := hil
  have hxl : (tbs x).length = x.length := by simp
  have hsp : getX s 2 = BitVec.ofNat 64 (stack.base + stack.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = stack.base + stack.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 7 (getX s 2) = (stack.base + stack.len) / 8 * 8 - 64 := by unfold frameBase; rw [hspn]
  have hf : FrOK 7 (frameBase 7 (getX s 2)) := ⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩
  have ho := bytesAt_hosted (s := s) (a := output.base) (n := L) hmap
  have hs := bytesAt_hosted (s := s) (a := scratch.base) (n := L2) hmapS
  generalize hO : (bytesAt s output.base L).map (·.getD 0) = out0 at ho
  generalize hS : (bytesAt s scratch.base L2).map (·.getD 0) = scr0 at hs
  have hout0 : out0.length = L := by rw [← hO]; simp [bytesAt]
  have hscr0 : scr0.length = L2 := by rw [← hS]; simp [bytesAt]
  let R : List Region := [⟨input.base, x.length⟩, ⟨output.base, L⟩, ⟨scratch.base, L2⟩]
  have hR : RegOK R := by
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry (compileBF 7 [0, 3, 2] prog).length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ R, disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r := by
    rw [hfb]; intro r hr
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ (⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region) :: R,
      disjoint ⟨entry.toNat, 4 * (compileBF 7 [0, 3, 2] prog).length⟩ r := by
    rw [hfb]; intro r hr
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  have e1 : envOf s 1 = .ofNat 64 x.length := by simpa [envOf] using getX_of (h.x11.symm.trans h11) rfl
  obtain ⟨τ', out', scr', hexec, hh, hlen, htk, he1⟩ := hex x out0 scr0 (envOf s) e1 (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hheap : HeapRel [0, 3, 2] R ⟨envOf s, [tbs x, out0, scr0]⟩ s :=
    ⟨rfl, rfl, fun b hb => by
        obtain _ | _ | _ | b := b
        · simpa [envOf] using getX_of (h.x10.symm.trans h10) rfl
        · simpa [envOf] using getX_of (h.x13.symm.trans h13) rfl
        · simpa [envOf] using getX_of (h.x12.symm.trans h12) rfl
        · simp [R] at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · simp [R]
        · simpa [R] using hout0
        · simpa [R] using hscr0
        · simp [R] at hb; omega,
      fun b hb => by
        obtain _ | _ | _ | b := b
        · simpa [R, tbs, List.map_map, Function.comp_def] using hx
        · simpa [R] using ho
        · simpa [R] using hs
        · simp [R] at hb; omega⟩
  refine runsTo_mono (compileBF_ok 7 [0, 3, 2] (by decide) hwf hR hexec h hpc (codeAt_of_codeBytes hok hcode) hok
    hf hfd hcd (fun i => by simp [envOf]) (fun j hj => by simp [envOf]; omega) hheap (by rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  have eo := p3.bytes 1 (by simp [R])
  simp only [hh] at eo
  have eo' : bytesAt s' output.base L = out'.map some := by simpa [R] using eo
  have hfl : (f x).length ≤ L := by
    have := congrArg List.length htk
    simp only [List.length_take, List.length_map] at this; omega
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5, ?_⟩
  · rw [← bytesAt_take s' output.base hfl, eo', ← List.map_take, htk]; simp [tbs, List.map_map]
  · intro a ha
    apply p4 a
    intro r hr
    have a1 := ha input (by simp); have a2 := ha scratch (by simp); have a3 := ha output (by simp)
    have a4 := ha stack (by simp)
    simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hfb] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (dsimp only; omega)
  · rw [p5.x11]; show some (getX s' (A8 1)) = _; rw [p2 1]; exact congrArg some he1

/-! ## Correctness -/

theorem compileXB_ok {p : XPipe} {code : List (BitVec 32)} (h : compileXB p = .ok code) :
    ImplementsPipeS code (XPipe.denote p) (XPipe.space p) (XPipe.sspace p) 71 := by
  obtain ⟨hc, hwf, rfl⟩ := compileXB_inv h
  exact implementsS_of_execB hwf fun xs out scr env h1 hx hsp hL hss hL2 =>
    XPipe.progB_exec p hc xs out scr env h1 hx hsp hL hss hL2

/-- **Correctness of the pipe compiler with the merge sort** -/
theorem compileX_ok {p : XPipe} {code : List (BitVec 32)} (h : compileX p = .ok code) :
    ImplementsPipeS code (XPipe.denote p) (XPipe.space p) (XPipe.sspace p) (XPipe.stack p) := by
  unfold compileX at h
  unfold XPipe.stack
  split at h
  · rename_i hs; rw [if_pos hs]; exact compileXB_ok h
  · rename_i hs; rw [if_neg hs]; exact (compileXA_ok h).toS _ _

end Proven

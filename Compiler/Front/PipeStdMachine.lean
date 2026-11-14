/- The `XPipe` compiler on the Sail model: `compileXA p = .ok code → ImplementsPipe code p.denote p.space`
(the same statement as `compileP_ok`, `Compiler/Front/PipeMachine.lean`). -/
import Compiler.Front.PipeStdSrc
import Compiler.Front.PipeMachine

set_option linter.unusedVariables false

namespace Proven

def XPipe.chkErr : XPipe → Option String
  | [] => none
  | st :: r => match st.chk with
    | some m => some m
    | none => XPipe.chkErr r

theorem XPipe.chkErr_none : ∀ {p : XPipe}, XPipe.chkErr p = none → ∀ st ∈ p, st.chk = none
  | [], _, _, h => by simp at h
  | st :: r, h, st', hm => by
    simp only [XPipe.chkErr] at h
    cases hc : st.chk with
    | some m => simp [hc] at h
    | none =>
      simp only [hc] at h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hc
      · exact XPipe.chkErr_none h st' hm

/-- **The extended pipe compiler** (two blocks, no stack): machine code for `p`, or the reason it is rejected -/
def compileXA (p : XPipe) : Except String (List (BitVec 32)) :=
  match XPipe.chkErr p with
  | some m => .error m
  | none => match wfErr [0, 3] (XPipe.prog p) with
    | some m => .error m
    | none => .ok (compileAF [0, 3] (XPipe.prog p))

theorem compileXA_inv {p : XPipe} {code : List (BitVec 32)} (h : compileXA p = .ok code) :
    (∀ st ∈ p, st.chk = none) ∧ (XPipe.prog p).wf [0, 3] ∧ code = compileAF [0, 3] (XPipe.prog p) := by
  unfold compileXA at h
  cases hc : XPipe.chkErr p with
  | some m => simp [hc] at h
  | none =>
    cases hw : wfErr [0, 3] (XPipe.prog p) with
    | some m => simp [hc, hw] at h
    | none =>
      simp only [hc, hw, Except.ok.injEq] at h
      exact ⟨XPipe.chkErr_none hc, (wfErr_iff _ _).1 hw, h.symm⟩

/-- `ImplementsPipe` plus: at the return, `a1` holds the result length `|f x|` (the second ABI return
register; the convention of `Spec/Implements1.lean`), so the result is exactly the first `a1` output bytes;
and memory changes only in the first `space |x|` output bytes (no scratch, no stack). -/
def ImplementsPipeLen (code : List (BitVec 32)) (f : List UInt8 → List UInt8) (space : Nat → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
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
    input.len = x.length → space x.length ≤ output.len →
    (∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM) →
    [input, scratch, output, stack, codeR].Pairwise disjoint →
    (∀ i < space x.length, (s.mem[output.base + i]?).isSome) →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      bytesAt s' output.base (f x).length = (f x).map (some ·.toBitVec) ∧
      unchangedOutside s s' [input, ⟨output.base, space x.length⟩] ∧ calleeSavedKept s s' ∧
      Cfg s' ∧ s'.regs.get? .x11 = some (BitVec.ofNat 64 (f x).length)

theorem unchanged_sub {s s' : St} {rs rs' : List Region} (h : unchangedOutside s s' rs)
    (hs : ∀ a, (∀ r ∈ rs', a < r.base ∨ r.base + r.len ≤ a) → ∀ r ∈ rs, a < r.base ∨ r.base + r.len ≤ a) :
    unchangedOutside s s' rs' := fun a ha => h a (hs a ha)

theorem ImplementsPipeLen.toPipe {code : List (BitVec 32)} {f : List UInt8 → List UInt8} {space : Nat → Nat}
    (h : ImplementsPipeLen code f space) : ImplementsPipe code f space := by
  intro x s entry ra input scratch output stack codeR hmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  exact runsTo_mono (h x s entry ra input scratch output stack hmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18) fun s' ⟨a, b, c, d, e, _⟩ => ⟨a, b, unchanged_sub c (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := ha output (by simp)
      rcases hr with rfl | rfl
      · exact ha _ (by simp)
      · dsimp only; omega), d, e⟩

/-- from a source-level run to the machine-level specification -/
theorem implementsLen_of_exec {prog : AStmt} (hwf : prog.wf [0, 3]) {f : List UInt8 → List UInt8} {space : Nat → Nat}
    (hex : ∀ (xs : List UInt8) (out : List (BitVec 8)) (env : AEnv), env 1 = .ofNat 64 xs.length →
      xs.length < 2 ^ 32 → space xs.length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ' out', AExec prog ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧ out'.length = out.length ∧
        out'.take (f xs).length = tbs (f xs) ∧ σ'.env 1 = .ofNat 64 (f xs).length) :
    ImplementsPipeLen (compileAF [0, 3] prog) f space := by
  intro x s entry ra input scratch output stack codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hram hdis hmap
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d13 d15 d35
  simp only [codeR] at d15 d35
  obtain ⟨L, hLe⟩ : ∃ L, L = space x.length := ⟨_, rfl⟩
  rw [← hLe] at hol hmap
  have hil' : input.len = x.length := hil
  have hol' : L ≤ output.len := hol
  have hxl : (tbs x).length = x.length := by simp
  have hout0 : ((bytesAt s output.base L).map (·.getD 0)).length = L := by simp [bytesAt]
  have ho : bytesAt s output.base L = ((bytesAt s output.base L).map (·.getD 0)).map some := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range, Function.comp]
    have := hmap i (by simpa [bytesAt] using h1)
    cases e : s.mem[output.base + i]? with
    | none => rw [e] at this; simp at this
    | some b => rfl
  generalize (bytesAt s output.base L).map (·.getD 0) = out0 at hout0 ho
  have hR : RegOK [⟨input.base, x.length⟩, ⟨output.base, L⟩] := by
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry (compileAF [0, 3] prog).length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, x.length⟩ : Region), ⟨output.base, L⟩],
      disjoint ⟨entry.toNat, 4 * (compileAF [0, 3] prog).length⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  obtain ⟨σ', out', hexec, hh, hlen, htk, he1⟩ := hex x out0 (fun i => getX s (A8 i))
    (getX_of (h.x11.symm.trans h11) rfl) (by omega) (by rw [← hLe, hout0]; exact Nat.le_refl _) (by omega)
  have hrel : Rel [0, 3] [⟨input.base, x.length⟩, ⟨output.base, L⟩] ⟨fun i => getX s (A8 i), [tbs x, out0]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl,
      fun b hb => by
        obtain _ | _ | b := b
        · exact getX_of (h.x10.symm.trans h10) rfl
        · exact getX_of (h.x13.symm.trans h13) rfl
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | b := b
        · exact hxl
        · exact hout0
        · simp at hb; omega,
      fun b hb => by
        obtain _ | _ | b := b
        · simpa [tbs, List.map_map, Function.comp_def] using hx
        · exact ho
        · simp at hb; omega⟩
  refine runsTo_mono (compileAF_ok [0, 3] hwf hR hexec h hpc (codeAt_of_codeBytes hok hcode) hok hcd hrel
    (by rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e1
  have e1' : bytesAt s' output.base L = out'.map some := by simpa using e1
  have hfl : (f x).length ≤ L := by
    have := congrArg List.length htk
    simp only [List.length_take, List.length_map] at this; omega
  refine ⟨by rw [p1, hra'], ?_, ?_, p5, p4, by rw [p4.x11]; show some (getX s' (A8 1)) = _; rw [p2.env 1, he1]⟩
  · rw [← bytesAt_take s' output.base hfl, e1', ← List.map_take, htk]; simp [tbs, List.map_map]
  · intro a ha
    apply p3 a
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hi := ha input (by simp); have hoo := ha ⟨output.base, space x.length⟩ (by simp)
    rcases hr with rfl | rfl <;> (dsimp only at hoo ⊢; omega)

/-- **Correctness of the extended pipe compiler**: `ImplementsPipe` (the statement of `compileP_ok`) and the
result length in `a1` -/
theorem compileXA_ok {p : XPipe} {code : List (BitVec 32)} (h : compileXA p = .ok code) :
    ImplementsPipeLen code (XPipe.denote p) (XPipe.space p) := by
  obtain ⟨hc, hwf, rfl⟩ := compileXA_inv h
  exact implementsLen_of_exec hwf fun xs out env h1 hx hsp hL => XPipe.prog_exec p hc xs out env h1 hx hsp hL

end Proven

/- `compileP : Pipe → Except String (List (BitVec 32))` and its correctness on the Sail model:
`compileP p = .ok code → ImplementsPipe code p.denote p.space` (`compileP_ok`), and the `ImplementsMapped`
form when the pipe needs no more output space than its result (`compileP_mapped`). -/
import Proven.PipeSrc

set_option linter.unusedVariables false

namespace Proven

/-! ## Checking `AStmt.wf`, with a reason on failure -/

def wfErr (bv : List (Fin 8)) : AStmt → Option String
  | .assign v e =>
    if e.depth < 7 ∧ v ∉ bv then none
    else some s!"assignment to a{v}: expression needs {e.depth + 1} temporaries (limit 7), or a{v} is a block base"
  | .load v b i =>
    if i.depth < 6 ∧ v ∉ bv ∧ b < bv.length then none
    else some s!"load into a{v}: index expression needs {i.depth + 2} temporaries (limit 7)"
  | .store b i e =>
    if i.depth < 6 ∧ e.depth < 6 ∧ b < bv.length then none
    else some s!"store: expression needs {max i.depth e.depth + 2} temporaries (limit 7)"
  | .seq p q => match wfErr bv p with
    | some m => some m
    | none => wfErr bv q
  | .loop c body =>
    if c.depth < 7 ∧ (gen8 c 0).length + (compileA bv body).length + 2 < 1024 then wfErr bv body
    else some s!"loop too long: {(gen8 c 0).length + (compileA bv body).length + 2} words (limit 1023, the reach of beq)"

theorem wfErr_iff (bv : List (Fin 8)) : ∀ p : AStmt, wfErr bv p = none ↔ p.wf bv
  | .assign v e => by simp only [wfErr, AStmt.wf]; split <;> simp [*]
  | .load v b i => by simp only [wfErr, AStmt.wf]; split <;> simp [*]
  | .store b i e => by simp only [wfErr, AStmt.wf]; split <;> simp [*]
  | .seq p q => by
    simp only [wfErr, AStmt.wf, ← wfErr_iff bv p, ← wfErr_iff bv q]
    cases wfErr bv p <;> simp
  | .loop c body => by
    simp only [wfErr, AStmt.wf, ← wfErr_iff bv body]
    split <;> simp_all

/-! ## The compiler -/

def Pipe.chkErr : Pipe → Option String
  | [] => none
  | st :: r => match st.chk with
    | some m => some m
    | none => Pipe.chkErr r

theorem Pipe.chkErr_none : ∀ {p : Pipe}, Pipe.chkErr p = none → ∀ st ∈ p, st.chk = none
  | [], _, _, h => by simp at h
  | st :: r, h, st', hm => by
    simp only [Pipe.chkErr] at h
    cases hc : st.chk with
    | some m => simp [hc] at h
    | none =>
      simp only [hc] at h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hc
      · exact Pipe.chkErr_none h st' hm

/-- **The pipe compiler**: machine code for `p` (calling convention of `Implements`: `a0` = input,
`a1` = length, `a3` = output), or the reason it is rejected (a stage restriction, an expression too deep
for the 7 temporaries, a loop body beyond the `beq` range). -/
def compileP (p : Pipe) : Except String (List (BitVec 32)) :=
  match Pipe.chkErr p with
  | some m => .error m
  | none => match wfErr [0, 3] (Pipe.prog p) with
    | some m => .error m
    | none => .ok (compileAF [0, 3] (Pipe.prog p))

theorem compileP_inv {p : Pipe} {code : List (BitVec 32)} (h : compileP p = .ok code) :
    (∀ st ∈ p, st.chk = none) ∧ (Pipe.prog p).wf [0, 3] ∧ code = compileAF [0, 3] (Pipe.prog p) := by
  unfold compileP at h
  cases hc : Pipe.chkErr p with
  | some m => simp [hc] at h
  | none =>
    cases hw : wfErr [0, 3] (Pipe.prog p) with
    | some m => simp [hc, hw] at h
    | none =>
      simp only [hc, hw, Except.ok.injEq] at h
      exact ⟨Pipe.chkErr_none hc, (wfErr_iff _ _).1 hw, h.symm⟩

/-! ## The specification -/

/-- `ImplementsMapped` (`Proven/SortMachine.lean`) with the output-block hypotheses stated for
`space |x|` bytes instead of `|f x|` bytes: `space x.length ≤ output.len`, and the first `space x.length`
output bytes are present in the memory map.  The scratch-size and stack-size hypotheses are dropped (neither
block is used).  Everything else is the same: code anywhere, `a0..a3`/`sp`/`ra` as in `Implements`,
regions in RAM and pairwise disjoint; the run reaches `ra` with `f x` in the first `|f x|` output bytes,
memory outside the four regions unchanged, callee-saved registers and `Cfg` kept. -/
def ImplementsPipe (code : List (BitVec 32)) (f : List UInt8 → List UInt8) (space : Nat → Nat)
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
      unchangedOutside s s' [input, scratch, output, stack] ∧ calleeSavedKept s s' ∧ Cfg s'

/-- a pipe-implementation that needs no more output space than its result is an `ImplementsMapped` -/
theorem ImplementsPipe.mapped {code : List (BitVec 32)} {f : List UInt8 → List UInt8} {space : Nat → Nat}
    {maxLen : Nat} (h : ImplementsPipe code f space maxLen) (hs : ∀ x : List UInt8, space x.length ≤ (f x).length) :
    ImplementsMapped code f maxLen := by
  intro x s entry ra input scratch output stack codeR hmax hc hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hsl hol hstk hram hdis hmap
  exact h x s entry ra input scratch output stack hmax hc hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil
    (Nat.le_trans (hs x) hol) hram hdis (fun i hi => hmap i (Nat.lt_of_lt_of_le hi (hs x)))

theorem bytesAt_take (s : St) (a : Nat) {k n : Nat} (h : k ≤ n) : (bytesAt s a n).take k = bytesAt s a k := by
  simp [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- from a source-level run to the machine-level specification -/
theorem implements_of_exec {prog : AStmt} (hwf : prog.wf [0, 3]) {f : List UInt8 → List UInt8} {space : Nat → Nat}
    (hex : ∀ (xs : List UInt8) (out : List (BitVec 8)) (env : AEnv), env 1 = .ofNat 64 xs.length →
      xs.length < 2 ^ 32 → space xs.length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ' out', AExec prog ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧ out'.length = out.length ∧
        out'.take (f xs).length = tbs (f xs)) :
    ImplementsPipe (compileAF [0, 3] prog) f space := by
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
  obtain ⟨σ', out', hexec, hh, hlen, htk⟩ := hex x out0 (fun i => getX s (A8 i))
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
  refine ⟨by rw [p1, hra'], ?_, ?_, p5, p4⟩
  · rw [← bytesAt_take s' output.base hfl, e1', ← List.map_take, htk]; simp [tbs, List.map_map]
  · intro a ha
    apply p3 a
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hi := ha input (by simp); have hoo := ha output (by simp)
    rcases hr with rfl | rfl <;> (dsimp only; omega)

/-- **Correctness of the pipe compiler.**  If `compileP p` succeeds, the code implements `p.denote` on the
Sail model, given an output block of `p.space |x|` bytes. -/
theorem compileP_ok {p : Pipe} {code : List (BitVec 32)} (h : compileP p = .ok code) :
    ImplementsPipe code (Pipe.denote p) (Pipe.space p) := by
  obtain ⟨hc, hwf, rfl⟩ := compileP_inv h
  exact implements_of_exec hwf fun xs out env h1 hx hsp hL => Pipe.prog_exec p hc xs out env h1 hx hsp hL

/-- the `ImplementsMapped` form, for pipes whose intermediate results are no longer than the result -/
theorem compileP_mapped {p : Pipe} {code : List (BitVec 32)} (h : compileP p = .ok code)
    (hs : ∀ n, Pipe.space p n ≤ Pipe.len p n) : ImplementsMapped code (Pipe.denote p) :=
  (compileP_ok h).mapped fun x => by rw [Pipe.denote_len]; exact hs _

end Proven

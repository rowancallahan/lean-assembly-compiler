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

/-- **Correctness of the extended pipe compiler** (statement of `compileP_ok`) -/
theorem compileXA_ok {p : XPipe} {code : List (BitVec 32)} (h : compileXA p = .ok code) :
    ImplementsPipe code (XPipe.denote p) (XPipe.space p) := by
  obtain ⟨hc, hwf, rfl⟩ := compileXA_inv h
  exact implements_of_exec hwf fun xs out env h1 hx hsp hL => XPipe.prog_exec p hc xs out env h1 hx hsp hL

end Proven

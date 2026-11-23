/- Nano/Expr/SelfSrc: **C's own text, machine-independent** (no RISC-V model imported, so the ARM packages can use it).
`hsrc_CE` is SelfC's `hsrc_C` again (C's text `SrcGen.X0` lexes, desugars to itself and parses to the certified AST
`Cert.PC.all`, whose numerals pass NumSpec), kept here because SelfC imports the RISC-V top. With `Cert.sem_C` (the AST
means `mC`) and `C_expr`, on any machine with `CompileCorrect` / `CompileCorrectLoaded`: C's compiled code writes `mC a`
and `mC a` is the value `Ev` of the Expr nano emits for C (`self_expr`, `self_expr_loaded`). -/
import Nano.Expr.MachExpr
import Nano.Expr.CExpr
import Nano.SelfHost.Cert.All
import Nano.SelfHost.SrcLink.Top
import Nano.Lexer.MainTokWF
import Nano.Lexer.DsTok
namespace ExprSpec
open NanoMain ParSpec Proven.Top Proven.Top.Alloc

set_option maxRecDepth 200000 in
theorem noMatch_CE : DsSpec.matchTok ∉ SrcGen.T0 := by decide +kernel
set_option maxRecDepth 200000 in
theorem noNil_CE : DsSpec.noNilLet (SrcGen.W0.length + 1) SrcGen.W0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem len_CE : SrcGen.W0.length < 2 ^ 24 := by decide +kernel
set_option maxRecDepth 200000 in
theorem num_CE : NumSpec.numOkP Cert.PC.all = true := by decide +kernel

/-- C's text denotes its certified AST -/
theorem pOf_C : pOf SrcGen.X0 = some Cert.PC.all := by
  obtain ⟨hl, hp⟩ := SrcGen.link_pc
  have ht := tokL_of_tokens (lexes_tokWF hl) SrcGen.tk0
  exact pOf_eq ⟨_, hl, DsSpec.ds_id ht noMatch_CE len_CE noNil_CE⟩ hp num_CE

/-- the inputs on which C's meaning does not hit the capacity (as SelfLink's `SelfIn`) -/
def SelfInE : Type := {inp : List UInt8 // inp.length < 2 ^ 64 ∧ Sem κC Cert.PC.all inp ≠ .error .cap}

theorem sem_CE (a : SelfInE) : Sem κC Cert.PC.all a.1 = .ok (mC a.1) := by
  rcases Cert.sem_C a.1 a.2.1 with h | h
  · exact absurd h a.2.2
  · exact h

/-- C's text computes `mC` on `SelfInE` -/
theorem self_computesE : Computes (⟨SrcGen.X0⟩ : SrcC) (fun a : SelfInE => mC a.1) Subtype.val id := by
  unfold Computes
  intro a
  rw [show Program.run (⟨SrcGen.X0⟩ : SrcC) a.val = srcRun ⟨SrcGen.X0⟩ a.val from rfl, id]
  simp only [srcRun, pOf_C, Option.bind_some, sem_CE a, Except.toOption]

/-- **C on a machine**: C's code for its own text writes `mC a`, and `mC a` is `Ev` of the Expr nano emits for C -/
def SelfExpr (machine : Machine) (compile : SrcC → Option CompiledA) : Prop :=
  ∀ (compiled : CompiledA) (a : SelfInE) (startState : machine.State) (call : Call),
    compile ⟨SrcGen.X0⟩ = some compiled → StartCorrect machine startState call compiled.code a.1 →
    (mC a.1).length ≤ call.outputLength → memoryNeeded compiled a.1 ≤ call.workLength →
    ∃ finishState, Runs machine startState finishState ∧
      readMemory (machine.observe finishState) call.outputAddress (mC a.1).length = some (mC a.1) ∧
      Ev (progOf oC) [.l a.1] mainX (.l (mC a.1))

/-- `SelfExpr` for start states that also meet a loader contract -/
def SelfExprLoaded (machine : Machine) (Xp Wp : machine.State → Nat → Prop) (compile : SrcC → Option CompiledA) : Prop :=
  ∀ (compiled : CompiledA) (a : SelfInE) (startState : machine.State) (call : Call),
    compile ⟨SrcGen.X0⟩ = some compiled → StartCorrect machine startState call compiled.code a.1 →
    LoaderMaps Xp Wp startState call compiled.code →
    (mC a.1).length ≤ call.outputLength → memoryNeeded compiled a.1 ≤ call.workLength →
    ∃ finishState, Runs machine startState finishState ∧
      readMemory (machine.observe finishState) call.outputAddress (mC a.1).length = some (mC a.1) ∧
      Ev (progOf oC) [.l a.1] mainX (.l (mC a.1))

theorem self_expr {machine : Machine} {compile : SrcC → Option CompiledA} (H : CompileCorrect machine compile) :
    SelfExpr machine compile := by
  intro compiled a startState call compiles startsRight outputFits enough
  obtain ⟨fs, hrun, -, -, hmem, -⟩ := H (β := List UInt8) ⟨SrcGen.X0⟩ compiled (fun a : SelfInE => mC a.1)
    Subtype.val id a startState call compiles self_computesE startsRight (by simp only [id]; exact outputFits) enough
  simp only [id] at hrun hmem
  exact ⟨fs, hrun, hmem, C_expr a.1 a.2.1 (sem_CE a)⟩

theorem self_expr_loaded {machine : Machine} {Xp Wp : machine.State → Nat → Prop} {compile : SrcC → Option CompiledA}
    (H : CompileCorrectLoaded machine Xp Wp compile) : SelfExprLoaded machine Xp Wp compile := by
  intro compiled a startState call compiles startsRight loaded outputFits enough
  obtain ⟨fs, hrun, -, -, hmem, -⟩ := H (β := List UInt8) ⟨SrcGen.X0⟩ compiled (fun a : SelfInE => mC a.1)
    Subtype.val id a startState call compiles self_computesE startsRight loaded (by simp only [id]; exact outputFits) enough
  simp only [id] at hrun hmem
  exact ⟨fs, hrun, hmem, C_expr a.1 a.2.1 (sem_CE a)⟩

end ExprSpec

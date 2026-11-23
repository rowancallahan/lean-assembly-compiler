/- Nano/Expr/MachExpr: **machine code computes the value of the emitted Expr**, for every accepted program, on any
machine whose compile theorem has the owner's `CompileCorrect` (or `CompileCorrectLoaded`) form. `eval_emit` (the
program's meaning `Sem` is the big-step value `Ev` of its emitted Expr) composed with the compile theorem (the machine
code writes the meaning). The program: a source text `x` that denotes the AST `p` (`pOf`) and an emitter output `o` of
`p` (`emitAll` with the AST's numeral classes, any headers / side flags with which it succeeds). Instances:
Nano/Expr/RvExpr.lean (RISC-V, Sail), Arm/apc/Blocks/ExprDM.lean (native ARM, DeepMind),
Arm/sail/ArmSail/ExprSail.lean (native ARM, Sail). -/
import Nano.Expr.Correct
import Nano.Main.Compile
import Spec.Loader
namespace ExprSpec
open NanoMain ParSpec Proven.Top Proven.Top.Alloc

/-- `m`'s emitted Expr applied to the input -/
abbrev mainX : X := .app (.c "m" []) (.bv 0)

/-- **any accepted program**: whatever its text computes (`Computes`), the value is `Ev` of its emitted Expr -/
theorem computes_expr {α : Type} {x : List UInt8} {p : List DefA} {ds : List DefI} {st : Sd}
    {o : List (String × X × X)} {dm : DefI} {f : α → List UInt8} {encodeInput : α → List UInt8}
    (hc : Computes (⟨x⟩ : SrcC) f encodeInput id) (hp : pOf x = some p)
    (he : emitAll ds (p.map (·.kind)) (p.map (·.nres)) 0 p st = some o) (hnd : (o.map (·.1)).Nodup)
    (hm : ds[p.length - 1]? = some dm) (hmn : dm.name = [109]) (hmp : dm.params = [.inp]) (hmr : dm.res = .ls)
    (a : α) (hin : (encodeInput a).length < 2 ^ 64) :
    Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a)) := by
  have h : srcRun ⟨x⟩ (encodeInput a) = some (f a) := hc a
  simp only [srcRun, hp, Option.bind_some] at h
  exact eval_emit he hnd hin hm hmn hmp hmr (toOption_some h)

/-- **the machine code computes the value of the emitted Expr**, for every accepted program: if `compile` accepts the
text `x` (denoting the AST `p`, emitted as `o`) and the text computes `f`, the code writes `f a`, and `f a` is the
value `Ev` of `o`'s `m` applied to the input -/
def ExprCorrect (machine : Machine) (compile : SrcC → Option CompiledA) : Prop :=
  ∀ {α : Type} {x : List UInt8} {p : List DefA} {ds : List DefI} {st : Sd} {o : List (String × X × X)} {dm : DefI}
    {f : α → List UInt8} {encodeInput : α → List UInt8} (compiled : CompiledA) (a : α) (startState : machine.State)
    (call : Call), compile ⟨x⟩ = some compiled → Computes (⟨x⟩ : SrcC) f encodeInput id →
    StartCorrect machine startState call compiled.code (encodeInput a) → (f a).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput a) ≤ call.workLength →
    pOf x = some p → emitAll ds (p.map (·.kind)) (p.map (·.nres)) 0 p st = some o → (o.map (·.1)).Nodup →
    ds[p.length - 1]? = some dm → dm.name = [109] → dm.params = [.inp] → dm.res = .ls →
    (encodeInput a).length < 2 ^ 64 →
    ∃ finishState, Runs machine startState finishState ∧
      readMemory (machine.observe finishState) call.outputAddress (f a).length = some (f a) ∧
      Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a))

/-- `ExprCorrect` for start states that also meet a loader contract (`LoaderMaps`) -/
def ExprCorrectLoaded (machine : Machine) (Xp Wp : machine.State → Nat → Prop) (compile : SrcC → Option CompiledA) :
    Prop :=
  ∀ {α : Type} {x : List UInt8} {p : List DefA} {ds : List DefI} {st : Sd} {o : List (String × X × X)} {dm : DefI}
    {f : α → List UInt8} {encodeInput : α → List UInt8} (compiled : CompiledA) (a : α) (startState : machine.State)
    (call : Call), compile ⟨x⟩ = some compiled → Computes (⟨x⟩ : SrcC) f encodeInput id →
    StartCorrect machine startState call compiled.code (encodeInput a) →
    LoaderMaps Xp Wp startState call compiled.code → (f a).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput a) ≤ call.workLength →
    pOf x = some p → emitAll ds (p.map (·.kind)) (p.map (·.nres)) 0 p st = some o → (o.map (·.1)).Nodup →
    ds[p.length - 1]? = some dm → dm.name = [109] → dm.params = [.inp] → dm.res = .ls →
    (encodeInput a).length < 2 ^ 64 →
    ∃ finishState, Runs machine startState finishState ∧
      readMemory (machine.observe finishState) call.outputAddress (f a).length = some (f a) ∧
      Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a))

theorem correct_expr {machine : Machine} {compile : SrcC → Option CompiledA} (H : CompileCorrect machine compile) :
    ExprCorrect machine compile := by
  intro α x p ds st o dm f encodeInput compiled a startState call compiles hc startsRight outputFits enough
    hp he hnd hm hmn hmp hmr hin
  obtain ⟨fs, hrun, -, -, hmem, -⟩ :=
    H (β := List UInt8) ⟨x⟩ compiled f encodeInput id a startState call compiles hc startsRight outputFits enough
  exact ⟨fs, hrun, hmem, computes_expr hc hp he hnd hm hmn hmp hmr a hin⟩

theorem correct_expr_loaded {machine : Machine} {Xp Wp : machine.State → Nat → Prop}
    {compile : SrcC → Option CompiledA} (H : CompileCorrectLoaded machine Xp Wp compile) :
    ExprCorrectLoaded machine Xp Wp compile := by
  intro α x p ds st o dm f encodeInput compiled a startState call compiles hc startsRight loaded outputFits enough
    hp he hnd hm hmn hmp hmr hin
  obtain ⟨fs, hrun, -, -, hmem, -⟩ :=
    H (β := List UInt8) ⟨x⟩ compiled f encodeInput id a startState call compiles hc startsRight loaded outputFits enough
  exact ⟨fs, hrun, hmem, computes_expr hc hp he hnd hm hmn hmp hmr a hin⟩

end ExprSpec

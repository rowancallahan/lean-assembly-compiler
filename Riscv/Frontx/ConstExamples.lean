/- Compile-time constants of con-leche and the self-hoster folded and emitted as data (`frontx_const`, NOTES section 36).
con-leche @6810492c1, verbatim (file:line before each block; generated from the depth-2 probe's source by
`Testing/conleche-depth2`-style extraction; docstrings dropped).  The 40 `Name` constants of `ConLecheBlk.lean` are
folded here too (as data, beside their run-time `cst` route).  Self-hoster: `Ir.R0`, `Ir.R1`, `Ir.RLim`
(`Compiler/Ir/Emit.lean`, `Reg = Fin 15`, one byte each). -/
import Riscv.Frontx.ConstCmd
import Riscv.Frontx.ConLecheBlk
import Compiler.Ir.Emit

set_option linter.unusedVariables false

-- ConLeche/Kernel/Basis/Builder.lean:39
section
namespace ConLeche.BasisDSL
def bn (s : String) : Name := .str .anonymous s
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:42
section
namespace ConLeche.BasisDSL
def uN : Name := bn "u"
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:45
section
namespace ConLeche.BasisDSL
def u : Level := .param uN
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:48
section
namespace ConLeche.BasisDSL
def vN : Name := bn "v"
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:51
section
namespace ConLeche.BasisDSL
def v : Level := .param vN
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:55
section
namespace ConLeche.BasisDSL
def u1N : Name := bn "u_1"
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:58
section
namespace ConLeche.BasisDSL
def u1 : Level := .param u1N
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:61
section
namespace ConLeche.BasisDSL
def bv (i : Nat) : Expr := .bvar i
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:64
section
namespace ConLeche.BasisDSL
def srt (u : Level) : Expr := .sort u
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:67
section
namespace ConLeche.BasisDSL
def prop : Expr := .sort .zero
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:70
section
namespace ConLeche.BasisDSL
def type1 : Expr := .sort (.succ .zero)
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:73
section
namespace ConLeche.BasisDSL
def cnst (n : Name) (us : List Level := []) : Expr := .const n us
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:84
section
namespace ConLeche.BasisDSL
def pi (_x : String) (ty body : Expr) : Expr :=
  .forallE ty body
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:89
section
namespace ConLeche.BasisDSL
def piI (_x : String) (ty body : Expr) : Expr :=
  .forallE ty body
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:93
section
namespace ConLeche.BasisDSL
def piA (ty body : Expr) : Expr :=
  .forallE ty body
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:97
section
namespace ConLeche.BasisDSL
def lm (_x : String) (ty body : Expr) : Expr :=
  .lam ty body
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:102
section
namespace ConLeche.BasisDSL
def lmI (_x : String) (ty body : Expr) : Expr :=
  .lam ty body
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:106
section
namespace ConLeche.BasisDSL
def ap2 (f a b : Expr) : Expr := .app (.app f a) b
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:109
section
namespace ConLeche.BasisDSL
def ap3 (f a b c : Expr) : Expr := .app (.app (.app f a) b) c
end ConLeche.BasisDSL
end

-- ConLeche/Kernel/Basis/Builder.lean:112
section
namespace ConLeche.BasisDSL
def ap4 (f a b c d : Expr) : Expr := .app (.app (.app (.app f a) b) c) d
end ConLeche.BasisDSL
end

-- ConLeche/Cached/StateC.lean:312
section
namespace ConLeche.Cached
open ConLeche
def instCCapC : Nat := 32000000
end ConLeche.Cached
end

-- ConLeche/Cached/StateC.lean:163
section
namespace ConLeche.Cached
open ConLeche
def natCountMax : Nat := 4294967295
end ConLeche.Cached
end

-- ConLeche/Cached/StateC.lean:322
section
namespace ConLeche.Cached
open ConLeche
def peelFuel : Nat := 16777216
end ConLeche.Cached
end

-- ConLeche/Kernel/Name.lean:155
section
namespace ConLeche
def Display.maxLen : Nat := 512
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:1339
section
namespace ConLeche.Expr
def bvarPoolSize : Nat := 4096
end ConLeche.Expr
end

-- ConLeche/Kernel/Level.lean:142
section
namespace ConLeche.Level
def defaultFuel : Nat := 10000
end ConLeche.Level
end

-- ConLeche/Kernel/Basis/And.lean:40
section
namespace ConLeche
open BasisDSL
def andIntroName : Name := andName.str "intro"
end ConLeche
end

-- ConLeche/Kernel/Basis/And.lean:68
section
namespace ConLeche
open BasisDSL
def andRecMinor : Expr :=
  pi "left" (bv 2) <|
  pi "right" (bv 2) <|
  .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))
end ConLeche
end

-- ConLeche/Kernel/Basis/And.lean:62
section
namespace ConLeche
open BasisDSL
def andRecMotive : Expr :=
  pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)
end ConLeche
end

-- ConLeche/Kernel/Basis/And.lean:43
section
namespace ConLeche
open BasisDSL
def andRecName : Name := andName.str "rec"
end ConLeche
end

-- ConLeche/Kernel/Core.lean:1460
section
namespace ConLeche
@[irreducible, noinline] def bindersFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

-- ConLeche/Kernel/Core.lean:1918
section
namespace ConLeche
@[irreducible, noinline] def checkFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:37
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def choiceName : Name := (anonymous |>.str "Classical") |>.str "choice"
end ConLeche
end

-- ConLeche/Kernel/Core.lean:1661
section
namespace ConLeche
@[irreducible, noinline] def defeqLoopFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

-- ConLeche/Kernel/Basis/Eq.lean:38
section
namespace ConLeche
open BasisDSL
def eqRecMotive : Expr :=
  pi "b" (bv 1) <|
  pi "t" (ap3 (cnst eqName [u]) (bv 2) (bv 1) (bv 0)) (srt u1)
end ConLeche
end

-- ConLeche/Kernel/Inductives/Positivity.lean:300
section
namespace ConLeche
def fuelSlack : Nat := 1024
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:40
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def iffName : Name := anonymous |>.str "Iff"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:43
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def iffIntroName : Name := iffName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:46
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def iffRecName : Name := iffName |>.str "rec"
end ConLeche
end

-- ConLeche/Kernel/Basis/Nat.lean:22
section
namespace ConLeche
open BasisDSL
def natT : Expr := cnst natName
end ConLeche
end

-- ConLeche/Kernel/Basis/Nat.lean:37
section
namespace ConLeche
open BasisDSL
def natRecMotive : Expr := pi "t" natT (srt u)
end ConLeche
end

-- ConLeche/Kernel/Basis/Nat.lean:41
section
namespace ConLeche
open BasisDSL
def natRecSucc : Expr :=
  pi "n" natT <|
  pi "n_ih" (.app (bv 2) (bv 0)) <|
  .app (bv 3) (.app (cnst natSuccName) (bv 1))
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:49
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def nonemptyName : Name := anonymous |>.str "Nonempty"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:52
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def nonemptyIntroName : Name := nonemptyName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:55
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def nonemptyRecName : Name := nonemptyName |>.str "rec"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:68
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def ofReduceBoolName : Name := (anonymous |>.str "Lean") |>.str "ofReduceBool"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:65
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def ofReduceNatName : Name := (anonymous |>.str "Lean") |>.str "ofReduceNat"
end ConLeche
end

-- ConLeche/Kernel/StdAxioms.lean:34
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def propextName : Name := anonymous |>.str "propext"
end ConLeche
end

-- ConLeche/Kernel/Basis/Quot.lean:82
section
namespace ConLeche
open BasisDSL
def quotIndMk : Expr :=
  pi "a" (bv 2) <|
  .app (bv 1) (ap3 (cnst quotMkName [u]) (bv 3) (bv 2) (bv 0))
end ConLeche
end

-- ConLeche/Kernel/Basis/Quot.lean:77
section
namespace ConLeche
open BasisDSL
def quotIndMotive : Expr :=
  pi "a" (ap2 (cnst quotName [u]) (bv 1) (bv 0)) prop
end ConLeche
end

-- ConLeche/Kernel/Basis/Quot.lean:46
section
namespace ConLeche
open BasisDSL
def quotLiftF : Expr := pi "a" (bv 2) (bv 1)
end ConLeche
end

-- ConLeche/Kernel/Basis/Quot.lean:50
section
namespace ConLeche
open BasisDSL
def quotLiftH : Expr :=
  pi "a" (bv 3) <|
  pi "b" (bv 4) <|
  pi "a" (ap2 (bv 4) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [v]) (bv 4) (.app (bv 3) (bv 2)) (.app (bv 3) (bv 1))
end ConLeche
end

-- ConLeche/Kernel/Basis/Quot.lean:29
section
namespace ConLeche
open BasisDSL
def quotRel : Expr := piA (bv 0) (piA (bv 1) prop)
end ConLeche
end

-- ConLeche/Kernel/TrustPins.lean:43
section
namespace ConLeche
open BasisDSL
def reduceBoolDeclPin : Expr := lm "b" (cnst (bn "Bool")) (bv 0)
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:62
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def reduceBoolName : Name := (anonymous |>.str "Lean") |>.str "reduceBool"
end ConLeche
end

-- ConLeche/Kernel/TrustPins.lean:46
section
namespace ConLeche
open BasisDSL
def reduceNatDeclPin : Expr := lm "n" (cnst (bn "Nat")) (bv 0)
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:50
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def trueName : Name := anonymous |>.str "True"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:53
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def trueIntroName : Name := trueName |>.str "intro"
end ConLeche
end

-- ConLeche/Kernel/TrustAxioms.lean:56
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
def trustCompilerName : Name := (anonymous |>.str "Lean") |>.str "trustCompiler"
end ConLeche
end

-- ConLeche/Kernel/Core.lean:450
section
namespace ConLeche
@[irreducible, noinline] def unitLikeFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

-- ConLeche/Kernel/Core.lean:1092
section
namespace ConLeche
@[irreducible, noinline] def whnfCoreLoopFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

-- ConLeche/Kernel/Core.lean:1116
section
namespace ConLeche
@[irreducible, noinline] def whnfLoopFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
end

namespace Proven.Frontx.ExprEx

frontx_const ConLeche.natName on TExpr
frontx_const ConLeche.natPredName on TExpr
frontx_const ConLeche.natAddName on TExpr
frontx_const ConLeche.natSubName on TExpr
frontx_const ConLeche.natMulName on TExpr
frontx_const ConLeche.natPowName on TExpr
frontx_const ConLeche.natBeqName on TExpr
frontx_const ConLeche.natBleName on TExpr
frontx_const ConLeche.natDivName on TExpr
frontx_const ConLeche.natModName on TExpr
frontx_const ConLeche.natGcdName on TExpr
frontx_const ConLeche.natLandName on TExpr
frontx_const ConLeche.natLorName on TExpr
frontx_const ConLeche.natXorName on TExpr
frontx_const ConLeche.natShiftLeftName on TExpr
frontx_const ConLeche.natShiftRightName on TExpr
frontx_const ConLeche.natZeroName on TExpr
frontx_const ConLeche.natSuccName on TExpr
frontx_const ConLeche.stringName on TExpr
frontx_const ConLeche.stringOfListName on TExpr
frontx_const ConLeche.listName on TExpr
frontx_const ConLeche.listNilName on TExpr
frontx_const ConLeche.listConsName on TExpr
frontx_const ConLeche.charName on TExpr
frontx_const ConLeche.charOfNatName on TExpr
frontx_const ConLeche.eqName on TExpr
frontx_const ConLeche.eqReflName on TExpr
frontx_const ConLeche.emptyName on TExpr
frontx_const ConLeche.falseName on TExpr
frontx_const ConLeche.quotName on TExpr
frontx_const ConLeche.quotMkName on TExpr
frontx_const ConLeche.quotLiftName on TExpr
frontx_const ConLeche.quotIndName on TExpr
frontx_const ConLeche.quotSoundName on TExpr
frontx_const ConLeche.andName on TExpr
frontx_const ConLeche.sorryAxName on TExpr
frontx_const ConLeche.boolName on TExpr
frontx_const ConLeche.eagerReduceName on TExpr
frontx_const ConLeche.boolTrueName on TExpr
frontx_const ConLeche.boolFalseName on TExpr
frontx_const ConLeche.BasisDSL.prop on TExpr
frontx_const ConLeche.BasisDSL.type1 on TExpr
frontx_const ConLeche.Cached.instCCapC on TExpr
frontx_const ConLeche.Cached.natCountMax on TExpr
frontx_const ConLeche.Cached.peelFuel on TExpr
frontx_const ConLeche.Display.maxLen on TExpr
frontx_const ConLeche.Expr.bvarPoolSize on TExpr
frontx_const ConLeche.Level.defaultFuel on TExpr
frontx_const ConLeche.andIntroName on TExpr
frontx_const ConLeche.andRecMinor on TExpr
frontx_const ConLeche.andRecMotive on TExpr
frontx_const ConLeche.andRecName on TExpr
frontx_const ConLeche.bindersFuel on TExpr
frontx_const ConLeche.checkFuel on TExpr
frontx_const ConLeche.choiceName on TExpr
frontx_const ConLeche.defeqLoopFuel on TExpr
frontx_const ConLeche.eqRecMotive on TExpr
frontx_const ConLeche.fuelSlack on TExpr
frontx_const ConLeche.iffName on TExpr
frontx_const ConLeche.iffIntroName on TExpr
frontx_const ConLeche.iffRecName on TExpr
frontx_const ConLeche.natT on TExpr
frontx_const ConLeche.natRecMotive on TExpr
frontx_const ConLeche.natRecSucc on TExpr
frontx_const ConLeche.nonemptyName on TExpr
frontx_const ConLeche.nonemptyIntroName on TExpr
frontx_const ConLeche.nonemptyRecName on TExpr
frontx_const ConLeche.ofReduceBoolName on TExpr
frontx_const ConLeche.ofReduceNatName on TExpr
frontx_const ConLeche.propextName on TExpr
frontx_const ConLeche.quotIndMk on TExpr
frontx_const ConLeche.quotIndMotive on TExpr
frontx_const ConLeche.quotLiftF on TExpr
frontx_const ConLeche.quotLiftH on TExpr
frontx_const ConLeche.quotRel on TExpr
frontx_const ConLeche.reduceBoolDeclPin on TExpr
frontx_const ConLeche.reduceBoolName on TExpr
frontx_const ConLeche.reduceNatDeclPin on TExpr
frontx_const ConLeche.satRange on TExpr
frontx_const ConLeche.trueName on TExpr
frontx_const ConLeche.trueIntroName on TExpr
frontx_const ConLeche.trustCompilerName on TExpr
frontx_const ConLeche.unitLikeFuel on TExpr
frontx_const ConLeche.whnfCoreLoopFuel on TExpr
frontx_const ConLeche.whnfLoopFuel on TExpr

end Proven.Frontx.ExprEx

frontx_const Proven.Ir.R0
frontx_const Proven.Ir.R1
frontx_const Proven.Ir.RLim

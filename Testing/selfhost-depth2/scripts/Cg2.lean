import Lean
import Riscv.Back.IrTop
import Riscv.Back.Top
import Riscv.Back.Wide
import Riscv.Back.IrTarget
import Compiler.Ir.Emit
import Compiler.Ir.IndLow
import Compiler.Ir.IndLowMain
import Compiler.Ir.Lin
import Compiler.Ir.Rename
import Compiler.Ir.Struct
import Compiler.Ir.Syntax
import Compiler.Ir.Target
import Compiler.Opt.Alloc
import Compiler.Opt.BFn
import Compiler.Opt.BSel
import Compiler.Opt.Color
import Compiler.Opt.Flow
import Compiler.Opt.Hoist
import Compiler.Opt.IR
import Compiler.Opt.Live
import Compiler.Opt.Lower
import Compiler.Opt.Peep
import Compiler.Opt.SR
import Compiler.Opt.Sel
import Compiler.Opt.Stmt
import Compiler.Opt.Fn
import Compiler.Opt.Exp
import Compiler.Opt.Arr
import Spec.Code
open Lean Meta

-- roots: every non-Prop, non-type definition of the listed modules (plus the top compile)
def inRootMod (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Compiler.Ir." && !(s.startsWith "Compiler.Ir.Examples") && !(s.startsWith "Compiler.Ir.Sim")
  || s.startsWith "Compiler.Opt." || s == "Riscv.Back.IrTop" || s == "Riscv.Back.IrTarget" || s == "Riscv.Back.Wide" || s == "Spec.Code"

def keep (env : Environment) (n : Name) : Bool :=
  let s := n.toString
  !(s.startsWith "_") && !(s.splitOn ".").any (fun p =>
     p.startsWith "match_" || p.startsWith "proof_" || p.startsWith "_" || p == "rec" || p == "recOn" || p == "casesOn"
     || p == "noConfusion" || p == "noConfusionType" || p == "below" || p == "brecOn" || p == "binductionOn" || p.startsWith "eq_"
     || p == "sizeOf_spec" || p == "ctorIdx" || p == "inj" || p == "injEq")
  && (match env.getModuleIdxFor? n with
      | some i => let m := env.header.moduleNames[i.toNat]!
                  m.getRoot ∈ [`Spec, `Compiler, `Riscv, `Arm, `Proven]
      | none => false)

def uses (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | some (.defnInfo d) => d.value.getUsedConstants.toList.filter (keep env) |>.eraseDups
  | _ => []

-- value-level definition (not a proof, not a type former)
def isValueDef (ci : ConstantInfo) : MetaM Bool := do
  let .defnInfo _ := ci | return false
  forallTelescope ci.type fun _ body => do
    let b ← whnf body
    if b.isSort then return false
    return !(← isProp b)

def rootsM : MetaM (List Name) := do
  let env ← getEnv
  let mut rs : Array Name := #[]
  for h : i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if !inRootMod m then continue
    for n in env.header.moduleData[i]!.constNames do
      if !keep env n then continue
      let some ci := env.find? n | continue
      if (← isValueDef ci) then rs := rs.push n
  return rs.toList ++ [`Proven.Top.compile]

def cg : MetaM Unit := do
  let env ← getEnv
  let roots ← rootsM
  IO.eprintln s!"roots {roots.length}"
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  let mut out := #[]
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | out := out.push s!"MISSING\t{n}\t\t\t"; continue
      let kind := match ci with | .defnInfo _ => "def" | .thmInfo _ => "thm" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .opaqueInfo _ => "opaque" | _ => "other"
      if kind == "thm" then continue
      let m := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD `none
      let u := uses env n
      let line := match declRangeExt.find? env n with | some r => r.range.pos.line | none => 0
      let core := match ci with
        | .defnInfo d => (d.value.getUsedConstants.toList.filter (fun c => !(keep env c)) |>.eraseDups)
        | _ => []
      let ty ← ppExpr ci.type
      let tys := (toString ty).replace "\n" " "
      out := out.push s!"{kind}\t{n}\t{m}\t{line}\t{",".intercalate (u.map toString)}\t{tys}\t{",".intercalate (core.map toString)}"
      todo := todo ++ u
  IO.println ("\n".intercalate out.toList)

#eval cg

import Lean
import LeanSvg
open Lean
def isAux (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s.startsWith "match_" || s.startsWith "_lambda" || s.startsWith "proof_" || s.startsWith "_private" || s.startsWith "_spec" || s.startsWith "_boxed" || s.startsWith "_closed" || s.startsWith "_unsafe_rec" || s.startsWith "_sunfold" || s.startsWith "eq_" || s.startsWith "_cstage" || s.startsWith "_elambda" || s.startsWith "_redArg" || s.startsWith "_rarg" || s == "rec" || s == "brecOn" || s == "below" || s == "binductionOn" || s == "casesOn" || s == "recOn" || s == "noConfusion" || s == "noConfusionType" || s.startsWith "_override" || s.startsWith "_jp" || s.startsWith "_f" && false
    | _ => false
def isPriv (n : Name) : Bool := n.isInternal
-- strip private prefix, map aux to its root def
partial def root (env : Environment) (n : Name) : Name :=
  let n' := (privateToUserName? n).getD n
  let rec go (n : Name) : Name :=
    if isAux n && !n.isAnonymous then go n.getPrefix else n
  go n'
def inSvg (n : Name) : Bool := (n.getRoot == `LeanSvg)
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `LeanSvg}] {} 
  -- all LeanSvg-defined constants
  let mut graph : Std.HashMap Name (Std.HashSet Name) := {}
  let mut tys : Std.HashMap Name String := {}
  for (n, ci) in env.constants.map₁.toList do
    unless inSvg (root env n) || inSvg n do continue
    let r := root env n
    unless inSvg r do continue
    let used := ci.getUsedConstantsAsSet.toList
    let mut s := graph.getD r {}
    for u in used do
      let ur := root env u
      if inSvg ur && ur != r then s := s.insert ur
    graph := graph.insert r s
    if n == r || n == (privateToUserName? n).getD n then pure ()
    if !tys.contains r || n == r then
      tys := tys.insert r (toString (← (Meta.MetaM.toIO (Meta.ppExpr ci.type) {fileName:="",fileMap:=default} {env}).map (·.1)))
  for (r, s) in graph.toList do
    let loc := match declRangeExt.find? env r with
      | some d => s!"{(env.getModuleIdxFor? r).map (env.header.moduleNames[·]!)}:{d.range.pos.line}"
      | none => "?"
    IO.println s!"{r}\t{(s.toList.map toString)}\t{(tys.getD r "").replace "\n" " "}\t{loc}"

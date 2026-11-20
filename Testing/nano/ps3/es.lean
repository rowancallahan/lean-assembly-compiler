import Lean
import Legacy.Nano.ParseS3
open Lean Meta Elab Command in
elab "#find_symm " n:ident : command => do
  let env ← getEnv
  for (nm, ci) in env.constants.toList do
    unless n.getId.isPrefixOf nm do continue
    let e := match ci with | .thmInfo t => t.type | .defnInfo d => d.value | _ => default
    if (e.find? (fun x => x.isConstOf ``Eq.symm)).isSome then logInfo m!"{nm}: has Eq.symm"
#find_symm Nano.PS
#find_symm Nano.PB.st0
#find_symm Nano.PB.findD
#find_symm Nano.PB.lookS

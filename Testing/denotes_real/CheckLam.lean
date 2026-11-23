import Bridge.Real.LamDemo
import Bridge.Main
open ConLeche ConLeche.Frontend Bridge.Real Bridge.Real.LamDemo

def mainLam : IO Unit := do
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinylam.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  let has (n : String) (t : Expr) := ds.any fun | .thmDecl cv _ => cv == ⟨AddOne.nm n, [], t⟩ | _ => false
  IO.println s!"(Λ1) g_eq declared as gEqTy: {has "g_eq" gEqTy}; ne12 declared as neTy: {has "ne12" neTy}; natPin = {Bridge.natPin ds}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(Λ2) accepted"
  | .error _ => IO.println "(Λ2) REJECTED"
#eval mainLam

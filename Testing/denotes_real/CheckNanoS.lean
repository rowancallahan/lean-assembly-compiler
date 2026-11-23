/- #eval checks for growth step `-` (Bridge.nano_sub); run from bridge/: `lake env lean ../Testing/denotes_real/CheckNanoS.lean`.
Needs `tinys.ndjson` = `lean4export TinyS -- <all names in NanoSDen.thmsS / defHeads / defHeadsL>` (lean4export v4.35.0-rc3),
which is NOT in the repo yet (S6 could not build lean4export). NOT proofs. -/
import Bridge.Main
open ConLeche ConLeche.Frontend Bridge.Real

def mainS : IO Unit := do
  IO.println s!"(S1) emitXs srcS = oS: {(ExprSpec.emitXs NanoS.srcS).toOption == some NanoS.oS}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinys.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(S2) recsOkS = {NanoSDen.recsOkS ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(S3) accepted"
  | .error _ => IO.println "(S3) REJECTED"
#eval mainS

/- #eval checks for Bridge.Main (run from bridge/: `lake env lean ../Testing/denotes_real/CheckNano.lean`).
NOT proofs: (1) nano's emitter on srcM gives oM; (2) dsM = con-leche's parse of tinym.ndjson;
(3) the fold accepts dsM; (4) H_natLit and H_indTypes hold of the accepted env. -/
import Bridge.Main
open ConLeche ConLeche.Frontend Bridge.Real

def indOk (env : Env) : Bool :=
  NanoDen.indHeads.all fun p => match env.find? p.1 with
    | some ci => ci.toConstantVal.levelParams == p.2.ps &&
        ci.toConstantVal.type.resetMeta == (Engine.piV p.2.Ts p.2.B).resetMeta
    | none => false

def main' : IO Unit := do
  IO.println s!"(1) emitXs srcM = oM: {(ExprSpec.emitXs NanoTiny.srcM).toOption == some NanoTiny.oM}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinym.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  IO.println s!"(2) parse = dsM: {preparePrelude pre r.decls == dsM}"
  match Cached.checkDecls .verified natOpPinSets dsM with
  | .ok env => IO.println s!"(3) accepted; (4) natLitSupported = {natLitSupported env}, IndStored = {indOk env}"
  | .error _ => IO.println "(3) REJECTED"
#eval main'

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

/-! the input-dependent program (Bridge.nano_input) -/
def mainR : IO Unit := do
  IO.println s!"(R1) emitXs srcR = oR: {(ExprSpec.emitXs NanoR.srcR).toOption == some NanoR.oR}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyr.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(R2) recsOkR = {NanoRDen.recsOkR ds}, natPin = {Bridge.natPin ds}, indOkBlocks = {IndHeads.indOkBlocks ds}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok env => IO.println s!"(R3) accepted; IndStored = {indOk env}"
  | .error _ => IO.println "(R3) REJECTED"
#eval mainR

/-! growth step `ite` (Bridge.nano_ite) -/
def mainL : IO Unit := do
  IO.println s!"(L1) emitXs srcL = oL: {(ExprSpec.emitXs NanoL.srcL).toOption == some NanoL.oL}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyl.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(L2) recsOkL = {NanoLDen.recsOkL ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(L3) accepted"
  | .error _ => IO.println "(L3) REJECTED"
#eval mainL

/-! growth step `u64 ops` (Bridge.nano_arith) -/
def mainA : IO Unit := do
  IO.println s!"(A1) emitXs srcA = oA: {(ExprSpec.emitXs NanoA.srcA).toOption == some NanoA.oA}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinya.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(A2) recsOkA = {NanoADen.recsOkA ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(A3) accepted"
  | .error _ => IO.println "(A3) REJECTED"
#eval mainA

/-! growth step `calls` (Bridge.nano_calls) -/
def mainC : IO Unit := do
  IO.println s!"(C1) emitXs srcC = oC: {(ExprSpec.emitXs NanoC.srcC).toOption == some NanoC.oC}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyc.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(C2) recsOkC = {NanoCDen.recsOkC ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(C3) accepted"
  | .error _ => IO.println "(C3) REJECTED"
#eval mainC

/-! growth step `len` (Bridge.nano_len) -/
def mainN : IO Unit := do
  IO.println s!"(N1) emitXs srcN = oN: {(ExprSpec.emitXs NanoN.srcN).toOption == some NanoN.oN}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyn.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(N2) recsOkN = {NanoNDen.recsOkN ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(N3) accepted"
  | .error _ => IO.println "(N3) REJECTED"
#eval mainN

/-! growth step `let` (Bridge.nano_let) -/
def mainT : IO Unit := do
  IO.println s!"(T1) emitXs srcT = oT: {(ExprSpec.emitXs NanoLet.srcT).toOption == some NanoLet.oT}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyt.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(T2) recsOkT = {NanoLetDen.recsOkT ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(T3) accepted"
  | .error _ => IO.println "(T3) REJECTED"
#eval mainT

/-! growth step `fuel loop` (Bridge.nano_loop) -/
def mainF : IO Unit := do
  IO.println s!"(F1) emitXs srcF = oF: {(ExprSpec.emitXs NanoF.srcF).toOption == some NanoF.oF}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyf.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(F2) recsOkF = {NanoFDen.recsOkF ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(F3) accepted"
  | .error _ => IO.println "(F3) REJECTED"
#eval mainF

/-! growth step `pairs` (Bridge.nano_pair) -/
def mainP : IO Unit := do
  IO.println s!"(P1) emitXs srcP = oP: {(ExprSpec.emitXs NanoP.srcP).toOption == some NanoP.oP}"
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tinyp.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  IO.println s!"(P2) recsOkT = {NanoLetDen.recsOkT ds}, natPin = {Bridge.natPin ds}, blocksOk = {IndHeads.blocksOk ds NanoLDen.blocksL}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok _ => IO.println "(P3) accepted"
  | .error _ => IO.println "(P3) REJECTED"
#eval mainP

import Bridge.Real.AddOne
open ConLeche ConLeche.Frontend Bridge.Real

def cvOf : Declaration → Option ConstantVal
  | .defnDecl cv _ _ => some cv | .thmDecl cv _ => some cv | _ => none
def isDef : Declaration → Bool | .defnDecl .. => true | _ => false

def expected : List (Bool × ConstantVal) :=
  let N := AddOne.nm
  [ (true, ⟨N "f", [], Tiny.fTy⟩), (false, ⟨N "f_eq", [], Tiny.fEqTy (N "f")⟩),
    (true, ⟨AddOne.hAddN, [AddOne.lu, AddOne.lv, AddOne.lw], AddOne.piV AddOne.hAddTs (.bvar 3)⟩),
    (true, ⟨AddOne.instHAddN, [AddOne.li], AddOne.piV AddOne.instHAddTs AddOne.instHAddB⟩),
    (true, ⟨AddOne.instAddNatN, [], AddOne.piV [] AddOne.instAddNatB⟩),
    (true, ⟨AddOne.ofNatN, [AddOne.lu], AddOne.piV AddOne.ofNatTs (.bvar 2)⟩),
    (true, ⟨AddOne.instOfNatNatN, [], AddOne.piV [Tiny.natC] AddOne.instOfNatNatB⟩),
    (true, ⟨AddOne.outParamN, [AddOne.lu], AddOne.piV [.sort AddOne.pu] (.sort AddOne.pu)⟩),
    (false, ⟨N "f_body", [], AddOne.piV [Tiny.natC] (AddOne.e1B (N "f"))⟩),
    (false, ⟨N "add_one", [], AddOne.piV [Tiny.natC] AddOne.e2B⟩),
    (false, ⟨N "outParam_eq", [], AddOne.piV [] AddOne.e3B⟩) ]

def main' : IO Unit := do
  let bytes ← IO.FS.readBinFile "../Testing/denotes_real/tiny.ndjson"
  let .ok r := parseChunks [bytes] | throw (IO.userError "parse failed")
  let .ok pre := builtinPreludeE | throw (IO.userError "prelude failed")
  let ds := preparePrelude pre r.decls
  for (d, cv) in expected do
    let hit := r.decls.any fun pd => isDef pd == d && cvOf pd == some cv
    IO.println s!"{repr cv.name}: record present exactly = {hit}"
    if !hit then
      for pd in r.decls do
        if (cvOf pd).map (·.name) == some cv.name then IO.println s!"  parsed: {repr (cvOf pd)}"
  match Cached.checkDecls .verified natOpPinSets ds with
  | .ok env => IO.println s!"checkDecls: ok, {env.consts.length} consts; natLitSupported = {natLitSupported env}"
  | .error _ => IO.println "checkDecls: ERROR"

#eval main'

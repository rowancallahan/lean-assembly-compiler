import LeanRV64D
open Lean
-- normalized dump: mdata stripped, binder names erased, let nonDep flag erased,
-- `assert` -> `sail_assert`, references to auxiliary constants replaced by their normalized value hash
def isAux (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes || match n with
  | .str _ s => s.startsWith "match_" || s.startsWith "_sparseCasesOn" || s.startsWith "proof_" || s == "_f"
               || s.startsWith "eq_" || s == "_unary" || s == "_binary"
  | _ => false
def ren (n : Name) : Name := match n with
  | .str p "assert" => .str p "sail_assert" | _ => n
partial def norm (env : Environment) (memo : IO.Ref (Std.HashMap Name UInt64)) (e : Expr) : IO Expr := do
  match e with
  | .mdata _ b => norm env memo b
  | .lam _ t b bi => return .lam `_ (← norm env memo t) (← norm env memo b) bi
  | .forallE _ t b bi => return .forallE `_ (← norm env memo t) (← norm env memo b) bi
  | .letE _ t v b _ => return .letE `_ (← norm env memo t) (← norm env memo v) (← norm env memo b) false
  | .app f a => return .app (← norm env memo f) (← norm env memo a)
  | .proj s i b => return .proj s i (← norm env memo b)
  | .const n ls =>
    if isAux n && (`LeanRV64D).isPrefixOf (n.components.filter (fun c => c != `_private) |>.foldl (· ++ ·) .anonymous) then
      if let some h := (← memo.get)[n]? then return .const (.num `AUX h.toNat) ls
      memo.modify (·.insert n 0)  -- cycle guard
      let h ← match env.find? n with
        | some ci => do pure (mixHash (← norm env memo ci.type).hash (← match ci.value? (allowOpaque := true) with
                        | some v => do pure (← norm env memo v).hash | none => pure 0))
        | none => pure 0
      memo.modify (·.insert n h); return .const (.num `AUX h.toNat) ls
    else return .const (ren n) ls
  | _ => return e
def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
#eval show CoreM Unit from do
  let env ← getEnv
  let memo ← IO.mkRef ({} : Std.HashMap Name UInt64)
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[idx.toNat]!
    unless (`LeanRV64D).isPrefixOf mn do continue
    if isAux n then continue
    let t ← norm env memo ci.type
    let v ← match ci with
      | .recInfo r => do pure (mkNatLit (hash (← r.rules.mapM (fun x => do pure (← norm env memo x.rhs).hash))).toNat)
      | .inductInfo i => pure (mkNatLit (hash (i.ctors.map (·.toString))).toNat)
      | _ => match ci.value? (allowOpaque := true) with | some v => norm env memo v | none => pure (mkNatLit 0)
    rows := rows.push s!"{ren n}\t{mn}\t{kindOf ci}\t{t.hash}\t{v.hash}"
  for r in rows.qsort (· < ·) do IO.println r

/- Statement fingerprints for the headline theorems (a cheap stand-in for `comparator`'s "same statement" check).

Usage (repo root):  lake env lean --run Testing/scripts/stmt_hash.lean <Mod1,Mod2,..> <thm1> <thm2> ...

For each theorem prints one line
  <name> stmt=<hash of the pretty-printed statement> closure=<hash of the dependency closure> consts=<n> local=<m>
where the closure is every constant reachable from the statement (NOT the proof): for a definition its type and
body, for a theorem only its type (proofs are irrelevant), for an inductive its type and constructors, for an opaque
or axiom its type.  The closure hash combines (name, Expr.hash of type [and body]) over the sorted closure, so
changing (e.g. weakening) any definition the statement depends on changes `closure=` even if the theorem's text
is unchanged.  `local` counts closure constants defined in this project (modules `Spec.*`, `Compiler.*`, `Riscv.*`);
with `--list` their names are printed too (for the audit). -/
import Lean
open Lean Meta

def isLocalMod (m : Name) : Bool :=
  [`Spec, `Compiler, `Riscv].any fun p => p.isPrefixOf m

/-- constants a constant's hashed part refers to -/
def deps (c : ConstantInfo) : Array Name :=
  let fromE (e : Expr) : Array Name := e.getUsedConstants
  match c with
  | .defnInfo d => fromE d.type ++ fromE d.value
  | .thmInfo t => fromE t.type
  | .opaqueInfo o => fromE o.type
  | .inductInfo i => fromE i.type ++ i.ctors.toArray
  | .ctorInfo k => fromE k.type ++ #[k.induct]
  | .recInfo r => fromE r.type ++ r.all.toArray
  | .quotInfo q => fromE q.type
  | .axiomInfo a => fromE a.type

def constHash (c : ConstantInfo) : UInt64 :=
  let base := mixHash (hash c.name) (mixHash (hash c.levelParams) c.type.hash)
  match c with
  | .defnInfo d => mixHash base d.value.hash
  | .inductInfo i => mixHash base (hash (i.ctors.map toString))
  | _ => base

partial def closure (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some c := env.find? n then
      for d in deps c do
        unless seen.contains d do todo := todo.push d
  return seen

def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  let args := args.filter (· != "--list")
  let mods :: thms := args | IO.eprintln "usage: stmt_hash <Mod1,Mod2> <thm>..."; return 2
  initSearchPath (← findSysroot)
  let imports := (mods.splitOn ",").map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports.toArray {} (trustLevel := 1024)
  let mut rc : UInt32 := 0
  for t in thms do
    let n := t.toName
    let some c := env.find? n | IO.eprintln s!"unknown theorem {t}"; rc := 1; continue
    let ctx : Core.Context := { fileName := "<stmt_hash>", fileMap := default, maxHeartbeats := 0,
      options := ({} : Options).setNat `format.width 100 }
    let (fmt, _) ← (MetaM.run' (ppExpr c.type)).toIO ctx { env }
    let stmt := toString fmt
    -- the closure of the statement: the constants in the type of `n` (not its proof)
    let cl := closure env (c.type.getUsedConstants)
    let names := cl.toArray.qsort (fun a b => a.toString < b.toString)
    let mut h : UInt64 := 7
    let mut loc : Array Name := #[]
    for m in names do
      if let some ci := env.find? m then
        h := mixHash h (constHash ci)
        if let some idx := env.getModuleIdxFor? m then
          if isLocalMod (env.header.moduleNames[idx.toNat]!) then loc := loc.push m
    IO.println s!"{t} stmt={hash stmt} closure={h} consts={names.size} local={loc.size}"
    if list then
      IO.println s!"  statement: {stmt.replace "\n" " "}"
      IO.println s!"  local defs: {loc.toList}"
  return rc

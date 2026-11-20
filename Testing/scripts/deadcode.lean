/- Dead-code finder for Nano/V2Self.  usage:
     lake build Nano.V2Self.REVIEW && lake env lean Testing/scripts/deadcode.lean > report.txt
   Roots: the theorems of REVIEW.lean (C_correctLO, sem_C, the SelfC theorems, C_runs / C_runsO / self_runs_C,
   shiftInv, Msp_le / spaceC_le), SrcGen.link_pc, and every declaration of a Proof/Tests module.  Computes every constant
   reachable from the roots (types and values, transitively), then, per `Nano.V2Self.*` module in REVIEW's import
   closure: declarations total / reachable.  Lines starting with:
     MOD-LIVE  module name, reachable / total user declarations
     MOD-DEAD  module in the closure with NO reachable declaration (imported, but nothing it defines is used)
     DECL-DEAD an unreachable theorem/def in a live module (`name line`; auxiliary `_`-names and instances skipped)
   Modules of Nano/V2Self outside REVIEW's closure are listed by deadcode.sh (filesystem minus closure). -/
import Nano.V2Self.REVIEW
import Nano.V2Self.Proof.Tests.AuditWitness
import Nano.V2Self.Proof.Tests.OwnNV
open Lean Meta

/-- files whose identifiers are roots (tactic dispatch tables, certificate / source-link generators) -/
def nameFiles : List String := ["Nano/V2Self/Proof/Cert/Tac.lean", "Testing/nano/v2self/cert/gen_cert.py",
  "Testing/nano/v2self/cert/dump_pc.lean", "Testing/nano/v2self/srclink/gen.lean"]

def roots : List Name := [``NanoMain.C_correctLO, ``Cert.sem_C, ``NanoMain.self_meaning_C, ``NanoMain.self_computes_C,
  ``NanoMain.self_correct_C, ``SrcGen.link_pc, ``NanoMain.C_runs, ``NanoMain.C_runsO, ``NanoMain.self_runs_C,
  ``NanoMain.shiftInv, ``NanoMain.Msp_le, ``NanoMain.spaceC_le]

#eval show CoreM Unit from do
  let env ← getEnv
  -- reachability
  let mut seen : NameHashSet := {}
  for r in roots do assert! env.contains r
  -- every declaration of a Tests/ module is a root too (the owner keeps the non-vacuity tests)
  let mods0 := env.allImportedModuleNames
  let tests := env.constants.map₁.toList.filterMap fun (n, _) => do
    let i ← env.getModuleIdxFor? n
    if (`Nano.V2Self.Proof.Tests).isPrefixOf mods0[i.toNat]! then some n else none
  -- names that tactics, generators and scripts refer to BY NAME (they never appear in a proof term of the roots, but
  -- certificates of other programs need them): every identifier token of these files that resolves to a constant,
  -- as written or under the namespaces the files open
  let mut named : Array Name := #[]
  for f in (if (← IO.getEnv "DEADCODE_NONAMED").isSome then [] else nameFiles) do
    let txt ← IO.FS.readFile f
    let toks := (txt.split fun c => !(c.isAlphanum || c == '_' || c == '.' || c == '\'')).filter (·.length > 1)
    for t in toks do
      let n := t.toName
      for pre in [Name.anonymous, `Cert, `NanoMain, `Templates, `SrcGen, `SrcLink, `ParSpec] do
        let m := pre ++ n
        if env.contains m && !named.contains m then named := named.push m
  IO.println s!"NAMED-ROOTS {named.size}"
  let mut todo : Array Name := roots.toArray ++ tests.toArray ++ named
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    for m in ci.getUsedConstantsAsSet do
      if !seen.contains m then todo := todo.push m
    -- an inductive's constructors / a structure's projections are part of it
    if let .inductInfo ii := ci then
      for c in ii.ctors do if !seen.contains c then todo := todo.push c
  -- per module
  let mods := env.allImportedModuleNames
  let mut tot : Std.HashMap Nat Nat := {}
  let mut live : Std.HashMap Nat Nat := {}
  let mut dead : Std.HashMap Nat (Array Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? n | continue
    let mn := mods[i.toNat]!
    unless (`Nano.V2Self).isPrefixOf mn do continue
    if n.isInternal || n.hasMacroScopes then continue
    let s := n.toString
    if (s.splitOn ".match_").length > 1 || (s.splitOn ".proof_").length > 1 || (s.splitOn ".eq_").length > 1 ||
       (s.splitOn "._").length > 1 || s.endsWith ".rec" || s.endsWith ".recOn" || s.endsWith ".casesOn" ||
       s.endsWith ".noConfusion" || s.endsWith ".noConfusionType" || s.endsWith ".below" || s.endsWith ".brecOn" ||
       s.endsWith ".binductionOn" || s.endsWith ".ibelow" || s.endsWith ".sizeOf_spec" || s.endsWith ".mk.injEq" ||
       s.endsWith ".mk.inj" || s.endsWith ".injEq" || s.endsWith ".inj" || s.endsWith ".eq_def" ||
       (s.splitOn ".eq_").length > 1 || (s.splitOn "_sunfold").length > 1 || s.endsWith ".induct" ||
       (s.splitOn "inst").length > 1 || s.endsWith ".ctorIdx" || s.endsWith ".toCtorIdx" || s.endsWith ".ctorElim" ||
       s.endsWith ".ctorElimType" || s.endsWith ".ofNat" || s.endsWith ".ofNat_ctorIdx" || s.endsWith ".elim" ||
       s.endsWith ".rec_1" || s.endsWith ".rec_2" || ci matches .ctorInfo _ then continue
    tot := tot.insert i.toNat (tot.getD i.toNat 0 + 1)
    if seen.contains n then live := live.insert i.toNat (live.getD i.toNat 0 + 1)
    else dead := dead.insert i.toNat ((dead.getD i.toNat #[]).push n)
  let idxs := (tot.toList.map (·.1)).toArray.qsort (fun a b => mods[a]!.toString < mods[b]!.toString)
  for i in idxs do
    let t := tot.getD i 0; let l := live.getD i 0
    IO.println s!"{if l == 0 then "MOD-DEAD" else "MOD-LIVE"} {mods[i]!} {l} / {t}"
  for i in idxs do
    if live.getD i 0 == 0 then continue
    for n in (dead.getD i #[]).qsort (·.toString < ·.toString) do
      let ln := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
      IO.println s!"DECL-DEAD {mods[i]!} {n} {ln}"
  IO.println s!"REACHABLE {seen.size} constants"
  -- DEADCODE_DUMP=file: write every reachable constant (sorted), to diff two runs
  if let some f ← IO.getEnv "DEADCODE_DUMP" then
    IO.FS.writeFile f ("\n".intercalate ((seen.toList.map toString).toArray.qsort (· < ·)).toList)

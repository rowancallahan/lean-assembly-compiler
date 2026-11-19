/- Dead-code finder for Nano/V2Self.  usage:
     lake build Nano.V2Self.REVIEW && lake env lean Testing/scripts/deadcode.lean > report.txt
   Roots: the theorems of REVIEW.lean (C_correctLO, sem_C, the SelfC theorems) and SrcGen.link_pc.  Computes every constant
   reachable from the roots (types and values, transitively), then, per `Nano.V2Self.*` module in REVIEW's import
   closure: declarations total / reachable.  Lines starting with:
     MOD-LIVE  module name, reachable / total user declarations
     MOD-DEAD  module in the closure with NO reachable declaration (imported, but nothing it defines is used)
     DECL-DEAD an unreachable theorem/def in a live module (`name line`; auxiliary `_`-names and instances skipped)
   Modules of Nano/V2Self outside REVIEW's closure are listed by deadcode.sh (filesystem minus closure). -/
import Nano.V2Self.REVIEW
open Lean Meta

def roots : List Name := [``NanoMain.C_correctLO, ``Cert.sem_C, ``NanoMain.self_meaning_C, ``NanoMain.self_computes_C,
  ``NanoMain.self_correct_C, ``SrcGen.link_pc]

#eval show CoreM Unit from do
  let env ← getEnv
  -- reachability
  let mut seen : NameHashSet := {}
  let mut todo : Array Name := roots.toArray
  for r in roots do assert! env.contains r
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

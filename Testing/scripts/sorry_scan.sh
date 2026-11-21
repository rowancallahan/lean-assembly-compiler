#!/usr/bin/env bash
# sorryAx scan: every constant DEFINED in the given lake libraries' modules (default: the default targets, plus Chain434
# and Nano.Main.REVIEW) whose type or value reaches `sorryAx`, transitively through any constant (also outside the
# libraries).  `#print axioms` checks only named theorems; this catches a module that admitted goals during error
# recovery, an auxiliary definition, or a `decreasing_by` that fell back to `sorry`.  Also lists every `axiom`
# declaration the modules reach (expected: the RISC-V model's platform/float opaques only).
# usage: Testing/scripts/sorry_scan.sh [LIB ...]   (after the libraries are built; prints, exits 1 if any sorryAx)
#   SCAN_ONLY / SCAN_EXCLUDE: Python regexes on module names.  Modules that cannot be imported together (Cert and
#   CertArm both define `Cert.*`) are scanned in two runs:  SCAN_EXCLUDE=CertArm …  then  SCAN_ONLY=CertArm …
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH=$HOME/.elan/bin:$PATH
T=$(mktemp -d)
python3 - "$T/mods.txt" "$@" <<'PY'
import sys, tomllib, glob, os
out, libs = sys.argv[1], sys.argv[2:]
cfg = tomllib.load(open("lakefile.toml", "rb"))
L = {l["name"]: l for l in cfg["lean_lib"]}
libs = libs or cfg["defaultTargets"] + ["Chain434"]
mods = {"Nano.Main.REVIEW"} if not sys.argv[2:] else set()
files = {f[:-5].replace("/", "."): f for f in glob.glob("**/*.lean", recursive=True) if not f.startswith((".lake/", "Testing/", "Arm/"))}
files["Arm.CompilerArm"] = "Arm/CompilerArm.lean"
for n in libs:
    l = L[n]
    for r in l.get("roots", []): mods.add(r)
    for g in l.get("globs", []):
        if g.endswith(".+"): mods |= {m for m in files if m == g[:-2] or m.startswith(g[:-2] + ".")}
        else: mods.add(g)
import re
if os.environ.get("SCAN_ONLY"): mods = {m for m in mods if re.search(os.environ["SCAN_ONLY"], m)}
if os.environ.get("SCAN_EXCLUDE"): mods = {m for m in mods if not re.search(os.environ["SCAN_EXCLUDE"], m)}
assert mods, "no module selected"
missing = [m for m in mods if m not in files]
assert not missing, missing
open(out, "w").write("\n".join(sorted(mods)) + "\n")
print(len(mods), "modules from", libs, file=sys.stderr)
PY
{ sed 's/^/import /' "$T/mods.txt"; cat <<'LEAN'
open Lean in
run_cmd do
  let env ← getEnv
  let mods : Std.HashSet Name := (← IO.FS.lines (← IO.getEnv "SCAN_MODS").get!).foldl (fun s l => s.insert l.toName) {}
  -- bad n: n's type or value reaches sorryAx (memoized, iterative post-order)
  let mut memo : Std.HashMap Name Bool := {}
  let deps (n : Name) : Array Name := match env.find? n with
    | some ci => (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[])
    | none => #[]
  let mut axs : Std.HashSet Name := {}
  let mut hits : Array (Name × Name) := #[]
  let mut total := 0
  for (n, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[i.toNat]!
    unless mods.contains m do continue
    total := total + 1
    let mut stack : Array (Name × Bool) := #[(n, false)]
    while h : stack.size > 0 do
      let (x, done) := stack[stack.size - 1]; stack := stack.pop
      if memo.contains x then continue
      if done then
        memo := memo.insert x (x == ``sorryAx || (deps x).any (memo.getD · false))
        if let some (.axiomInfo _) := env.find? x then axs := axs.insert x
      else
        stack := stack.push (x, true)
        for d in deps x do unless memo.contains d do stack := stack.push (d, false)
    if memo.getD n false then hits := hits.push (m, n)
  IO.println s!"SCANNED {total} constants defined in {mods.size} modules"
  for (m, n) in hits do IO.println s!"SORRYAX {m} {n}"
  IO.println s!"AXIOMS reached: {(axs.toList.map toString).toArray.qsort (· < ·)}"
  IO.println s!"RESULT {if hits.isEmpty then "no sorryAx" else s!"{hits.size} constants reach sorryAx"}"
LEAN
} > "$T/Scan.lean"
SCAN_MODS=$T/mods.txt lake env lean "$T/Scan.lean" | tee "$T/out.txt"
! grep -q '^SORRYAX' "$T/out.txt"

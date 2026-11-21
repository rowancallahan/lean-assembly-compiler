#!/usr/bin/env bash
# Rename Nano/V2Self -> Nano/{Lexer,Parser,Ownership,Codegen,Run,SelfHost,Main,Tests}: git mv + rewrite every module path
# (imports, lakefiles incl. Chain434 roots, Arm/apc + Arm/sail lakefiles, scripts, docs). Idempotent; run from any checkout of
# a branch based on main (after rebase). Fails loudly if a mapped file is missing or an old path survives.
# usage: Testing/scripts/stages/apply.sh   (then commit; map.tsv = the move list for the base tree)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
D=Testing/scripts/stages
git diff --quiet && git diff --cached --quiet || { echo "dirty tree: commit or stash first" >&2; exit 1; }
if [ -d Nano/V2Self ] && find Nano/V2Self -name '*.lean' | grep -q .; then
  # every file of map.tsv must exist (so the script is not run on a tree it was not made for)
  while IFS=$'\t' read -r old new; do test -e "$old" || { echo "missing mapped file $old" >&2; exit 1; }; done < $D/map.tsv
fi
python3 $D/rewrite.py apply
find Nano/V2Self -type d -empty -delete 2>/dev/null || true
while IFS=$'\t' read -r old new; do test -e "$new" && ! test -e "$old" || { echo "map.tsv entry not applied: $old -> $new" >&2; exit 1; }; done < $D/map.tsv
echo "stages rename applied: $(wc -l < $D/map.tsv) files from map.tsv"

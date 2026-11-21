#!/usr/bin/env bash
# Big-machine verification kit (32-64 GB box). One command: verify.sh COMMIT. Prints a PASS/FAIL/SKIP table.
# README.md (same folder) explains every step, the layout and what each result means. Testing/notes/MODEL_PROVENANCE.md
# is the source of the pins this script asserts.
#
# Layout (WORK, default ~/bigbox). The repo's lakefiles reach their dependencies by RELATIVE paths, so the checkout
# must sit next to them:
#   WORK/repo                 clone of the repo, detached at COMMIT (lakefile.toml: ../deps/sail-riscv-lean)
#   WORK/deps/sail-riscv-lean the regenerated RISC-V model: this repo's branch deps-rv-regen434 @ 4cf120c8, built on 4.34.1
#   WORK/deps/code-verification  google-deepmind/code-verification @ b0f729a (Arm/apc: ../../../deps/...)
#   WORK/regen-work, WORK/regen/armv9   step 2 (Sail + sail-arm checkouts, regenerated model)
#   WORK/armv9-unsplit        step 3: the committed Arm/model, built as is (no partition)
#   WORK/armv9-lean -> armv9-unsplit    the path Arm/sail's lakefile and the check.sh scripts use (ARMV9)
#   WORK/armv9-nosve          step 3b: the model generated WITHOUT the SVE if-chain split (optional)
#   WORK/armv9-part           step 5: Arm/gen/partition.py of the committed model, built
#   WORK/results/<commit>/    logs, rss tables, dumps, status files, summary.txt
# Resumable: a step whose WORK/results/<commit>/status/<step> exists is skipped; delete that file to rerun it.
# Never pushes anything; oleans stay under WORK.
#
# Conventions (fail visibly): every step runs in a subshell with `set -euo pipefail`; a failing command fails the
# step (FAIL, log named in the table) and later steps that need its output are SKIPped with the reason. Axiom
# checks: every "'X' depends on axioms: [...]" line in a step's log must list only propext, Classical.choice,
# Quot.sound, and at least one such line must exist (step 6 RISC-V: the pinned list, review_axioms.sh instead).
#
# Knobs: WORK, JOBS (concurrent lean processes for model builds; default = GB of RAM / 14, at least 1),
# NOSVE=0|1 (step 3b; default 1 if RAM >= 48 GB), STEPS (default "1 2 3 3b 4 5 6a 6b"), REPO_URL.
set -euo pipefail
[ $# -eq 1 ] || { echo "usage: $0 COMMIT" >&2; exit 2; }
COMMIT=$1
WORK=${WORK:-$HOME/bigbox}
REPO_URL=${REPO_URL:-https://github.com/rowancallahan/lean-assembly-compiler.git}
MEM_GB=$(awk '/MemTotal/ {print int($2/1048576)}' /proc/meminfo)
JOBS=${JOBS:-$(( MEM_GB / 14 > 0 ? MEM_GB / 14 : 1 ))}
NOSVE=${NOSVE:-$([ "$MEM_GB" -ge 48 ] && echo 1 || echo 0)}
# pins (asserted against MODEL_PROVENANCE.md / the repo's scripts in step 1)
RV_BRANCH=deps-rv-regen434; RV_REV=4cf120c8ea5cccd46b488b00f7a0335d17e43c51   # MODEL_PROVENANCE.md §4 (release-434)
CV_REPO=https://github.com/google-deepmind/code-verification; CV_REV=b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b
export PATH=$HOME/.elan/bin:$PATH
export OPAMSWITCH=${OPAMSWITCH:-bigbox-sail} OPAMYES=1
STD="propext, Classical.choice, Quot.sound"

mkdir -p "$WORK/deps" "$WORK/results"
R=$WORK/repo
[ -d "$R/.git" ] || git clone -q "$REPO_URL" "$R"
git -C "$R" fetch -q origin
git -C "$R" checkout -q --detach "$COMMIT"
[ -z "$(git -C "$R" status --porcelain --untracked-files=no)" ] || { echo "repo checkout $R has local changes" >&2; exit 1; }
C=$(git -C "$R" rev-parse --short=10 HEAD)
OUT=$WORK/results/$C; mkdir -p "$OUT/status"
K=$R/Testing/scripts/bigbox; G=$R/Arm/gen
echo "commit $C ($(git -C "$R" log -1 --format=%s | cut -c1-80)); WORK=$WORK; RAM ${MEM_GB} GB; JOBS=$JOBS; NOSVE=$NOSVE"

# run STEP TITLE FUNC: skip if done; else run FUNC in a strict subshell with its log; record PASS/FAIL + note.
# FUNC writes an optional one-line note to $NOTE; a FUNC that decides to skip writes "SKIP <reason>" to $NOTE.
run() {
  local s=$1 title=$2 f=$3
  [[ " ${STEPS:-1 2 3 3b 4 5 6a 6b} " == *" $s "* ]] || return 0
  if [ -f "$OUT/status/$s" ]; then echo "== $s $title: done earlier ($(cut -d' ' -f1 "$OUT/status/$s"))"; return; fi
  echo "== $s $title (log $OUT/$s.log)"
  export NOTE=$OUT/$s.note; rm -f "$NOTE"
  local t0=$(date +%s) rc=0
  ( set -euo pipefail; $f ) > "$OUT/$s.log" 2>&1 || rc=$?
  local dt=$(( $(date +%s) - t0 )) note=""; [ -f "$NOTE" ] && note=$(cat "$NOTE")
  if [[ $note == SKIP* ]]; then echo "SKIP ${dt}s $title: ${note#SKIP }" > "$OUT/status/$s"
  elif [ $rc -ne 0 ]; then echo "FAIL ${dt}s $title: exit $rc, see $s.log. $note" > "$OUT/status/$s"
  else echo "PASS ${dt}s $title: $note" > "$OUT/status/$s"; fi
  tail -1 "$OUT/$s.log" | cut -c1-200; cat "$OUT/status/$s"
}
ok() { [ -f "$OUT/status/$1" ] && [ "$(cut -d' ' -f1 "$OUT/status/$1")" = PASS ]; }
need() { for s in "$@"; do ok "$s" || { echo "SKIP needs step $s to PASS" > "$NOTE"; return 1; }; done; }
axioms() { python3 "$K/axioms.py" "$@"; }   # axioms.py LOG...: FAIL unless every printed axiom set is standard

# ---- 1. toolchains, dependency checkouts, pin assertions
s1() {
  command -v elan || { curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none; }
  elan toolchain install leanprover/lean4:v4.34.1
  # pins: regen.sh is the single source of the ARM ones; MODEL_PROVENANCE.md must name the same commits
  local P=$R/Testing/notes/MODEL_PROVENANCE.md
  SAIL_REV=$(sed -n 's/^SAIL_REV=\([0-9a-f]*\).*/\1/p' "$G/regen.sh"); ARM_REV=$(sed -n 's/^ARM_REV=\([0-9a-f]*\).*/\1/p' "$G/regen.sh")
  for h in "$SAIL_REV" "$ARM_REV" "$RV_REV" "$CV_REV"; do grep -q "${h:0:7}" "$P" || { echo "pin $h not in MODEL_PROVENANCE.md"; exit 1; }; done
  grep -q "${CV_REV:0:7}" "$R/Arm/apc/check.sh"
  [ "$(cat "$R/lean-toolchain")" = leanprover/lean4:v4.34.1 ]; [ "$(cat "$R/Arm/model/lean-toolchain")" = leanprover/lean4:v4.34.1 ]
  # opam switch for Sail (OCaml from opam; Sail's own deps are installed by regen.sh)
  command -v opam || { echo "install opam, z3, libgmp-dev, pkg-config, build-essential first (README)"; exit 1; }
  command -v z3
  [ -d "$HOME/.opam" ] || opam init --bare --disable-sandboxing -n
  opam switch list -s | grep -qx "$OPAMSWITCH" || opam switch create "$OPAMSWITCH" "${OCAML:-ocaml-base-compiler.4.14.2}"
  # dependency checkouts at their pins (full clones; the checkout is verified, not trusted)
  [ -e "$WORK/deps/sail-riscv-lean/.git" ] || git clone -q -b "$RV_BRANCH" --single-branch "$REPO_URL" "$WORK/deps/sail-riscv-lean"
  git -C "$WORK/deps/sail-riscv-lean" checkout -q "$RV_REV"
  [ -d "$WORK/deps/code-verification/.git" ] || git clone -q --filter=blob:none "$CV_REPO" "$WORK/deps/code-verification"
  git -C "$WORK/deps/code-verification" checkout -q "$CV_REV"
  for d in sail-riscv-lean code-verification; do [ -z "$(git -C "$WORK/deps/$d" status --porcelain --untracked-files=no)" ]; done
  echo "Sail $SAIL_REV, sail-arm $ARM_REV, RISC-V $RV_REV, arm64 $CV_REV; OCaml $(opam exec -- ocaml -version | grep -o '[0-9.]*$')" > "$NOTE"
}

# ---- 2. regenerate the Sail ARM model with the pinned Sail + patch 0001 + flags; byte-compare with Arm/model
s2() {
  need 1
  rm -rf "$WORK/regen-work" "$WORK/regen"; mkdir -p "$WORK/regen"
  eval "$(opam env)"
  W=$WORK/regen-work OUT=$WORK/regen/armv9 sh "$G/regen.sh"
  local A=$WORK/regen/armv9 B=$R/Arm/model
  for f in $( (cd "$B" && find Armv9.lean Armv9 -name '*.lean'; cd "$A" && find Armv9.lean Armv9 -name '*.lean') | sort -u); do
    cmp -s "$A/$f" "$B/$f" || echo "DIFFERS: $f"
  done
  git diff --no-index --stat "$B/Armv9" "$A/Armv9" > "$OUT/regen.diffstat" || true
  local h=$("$R/Testing/scripts/model_hash.sh" "$A" | cut -c1-16)
  if cmp -s <(cd "$A" && find Armv9.lean Armv9 -name '*.lean' | sort | xargs sha256sum) \
            <(cd "$B" && find Armv9.lean Armv9 -name '*.lean' | sort | xargs sha256sum); then
    echo "regenerated model byte-identical to Arm/model (sha ${h}…)" > "$NOTE"
  else echo "NOT identical: $(tail -1 "$OUT/regen.diffstat"); see regen.diffstat" > "$NOTE"; exit 1; fi
}

# build a model lake project in DIR (all 34+ modules: Armv9.lean does not import them all), peak RSS per module
build_model() {
  local D=$1 tag=$2
  local mods=$(cd "$D" && find Armv9 Armv9Core -name '*.lean' 2>/dev/null | sed 's|\.lean$||; s|/|.|g' | sort)
  python3 "$G/rssmon.py" "$OUT/rss-$tag.txt" & local M=$!
  ( cd "$D" && LEAN_NUM_THREADS=$JOBS lake build Armv9 $mods ) || { kill $M; exit 1; }
  kill $M; sort -rn "$OUT/rss-$tag.txt" | head -5
}

# ---- 3. build the committed model UNSPLIT (no partition), time and peak RSS per module
s3() {
  need 1
  mkdir -p "$WORK/armv9-unsplit"
  rsync -a --delete --exclude .lake "$R/Arm/model/" "$WORK/armv9-unsplit/"
  local t0=$(date +%s); build_model "$WORK/armv9-unsplit" unsplit
  ln -sfn "$WORK/armv9-unsplit" "$WORK/armv9-lean"
  echo "built in $(( $(date +%s) - t0 )) s; max peak RSS $(sort -rn "$OUT/rss-unsplit.txt" | head -1 | cut -d' ' -f1) MB ($(sort -rn "$OUT/rss-unsplit.txt" | head -1 | cut -d' ' -f3 | xargs basename)); rss-unsplit.txt" > "$NOTE"
}

# ---- 3b. variant: generator patch with the SVE if-chain split disabled (if_chain_min = max_int); rebuild what changes
s3b() {
  [ "$NOSVE" = 1 ] || { echo "SKIP NOSVE=0 (needs > 27 GB for __DecodeA64_SVE, DIFFS.md)" > "$NOTE"; return; }
  need 2 3
  # a copy of Arm/gen whose patch differs in one constant; regen.sh's last step needs ../proofs/Arm beside it
  local N=$WORK/gen-nosve/Arm; rm -rf "$WORK/gen-nosve" "$WORK/regen-nosve-work" "$WORK/regen-nosve"
  mkdir -p "$N"; cp -r "$G" "$N/gen"; ln -s "$R/Arm/proofs" "$N/proofs"; ln -s "$R/Testing" "$WORK/gen-nosve/Testing"
  sed -i 's/^+let if_chain_min = 1000$/+let if_chain_min = max_int/' "$N/gen/patches/sail/0001-lean-backend-fixes.patch"
  grep -q '^+let if_chain_min = max_int$' "$N/gen/patches/sail/0001-lean-backend-fixes.patch"
  eval "$(opam env)"
  # NOTE: reinstalls Sail into the same opam switch (step 2 is done, so nothing else needs the split build)
  mkdir -p "$WORK/regen-nosve"; W=$WORK/regen-nosve-work OUT=$WORK/regen-nosve/armv9 sh "$N/gen/regen.sh"
  local changed=$(cd "$WORK/regen-nosve/armv9" && for f in $(find Armv9 -name '*.lean'); do cmp -s "$f" "$WORK/regen/armv9/$f" || echo "$f"; done)
  echo "files changed by disabling the split: $changed"
  rm -rf "$WORK/armv9-nosve"; cp -a "$WORK/armv9-unsplit" "$WORK/armv9-nosve"   # keep .lake: only changed modules rebuild
  for f in $changed; do cp "$WORK/regen-nosve/armv9/$f" "$WORK/armv9-nosve/$f"; done
  local t0=$(date +%s); build_model "$WORK/armv9-nosve" nosve
  ( cd "$WORK/armv9-nosve" && DUMP_OUT=$OUT/dump-nosve.txt lake env lean "$G/dump_hashes.lean" )
  echo "changed: $(echo $changed); rebuilt in $(( $(date +%s) - t0 )) s; max peak RSS $(sort -rn "$OUT/rss-nosve.txt" | head -1 | cut -d' ' -f1) MB; dump-nosve.txt" > "$NOTE"
}

# ---- 4. proofs against the UNSPLIT model, unchanged: Arm/proofs/check.sh, Arm/apc bridges, Arm/sail top if present
s4() {
  need 1 3
  export ARMV9=$WORK/armv9-lean CV=$WORK/deps/code-verification
  "$R/Arm/proofs/check.sh" 2>&1 | tee "$OUT/s4-proofs.log"
  SKIP_ARM=1 "$R/Arm/apc/check.sh" 2>&1 | tee "$OUT/s4-apc.log"
  local logs="$OUT/s4-proofs.log $OUT/s4-apc.log" top="Arm/sail absent at this commit: C_correct_armSail NOT checked"
  if [ -d "$R/Arm/sail" ]; then
    ( cd "$R/Arm/sail" && lake build ArmSail ArmSail.Axioms ) 2>&1 | tee "$OUT/s4-sail.log"
    ( cd "$R/Arm/sail" && lake env lean ArmSail/Axioms.lean ) 2>&1 | tee -a "$OUT/s4-sail.log"
    grep -q "C_correct_armSail' depends on axioms" "$OUT/s4-sail.log"; logs="$logs $OUT/s4-sail.log"; top="C_correct_armSail / C_runs_armSail checked"
  fi
  axioms $logs
  echo "$(axioms --count $logs) axiom lines, all standard; $top" > "$NOTE"
}

# ---- 5. definition fingerprints: unsplit vs partitioned build of the same committed model
s5() {
  need 3
  rm -rf "$WORK/armv9-part"
  python3 "$G/partition.py" "$R/Arm/model" "$WORK/armv9-part" "$R/Arm/proofs/Arm"
  cp "$R/Arm/model/lake-manifest.json" "$WORK/armv9-part/"
  build_model "$WORK/armv9-part" part
  ( cd "$WORK/armv9-unsplit" && DUMP_OUT=$OUT/dump-unsplit.txt lake env lean "$G/dump_hashes.lean" )
  ( cd "$WORK/armv9-part" && DUMP_OUT=$OUT/dump-part.txt lake env lean "$G/dump_hashes.lean" )
  local nu=$(wc -l < "$OUT/dump-unsplit.txt") np=$(wc -l < "$OUT/dump-part.txt") hp=$(sha256sum < "$OUT/dump-part.txt" | cut -c1-8)
  diff "$OUT/dump-unsplit.txt" "$OUT/dump-part.txt" > "$OUT/dump.diff" || true
  local nd=$(grep -c '^[<>]' "$OUT/dump.diff" || true)
  local ref="partitioned dump sha256 $hp… (ARM_FAST.md §9 recorded 45,241 rows, 76a23330…)"
  [ "$nd" = 0 ] || { echo "$nd differing rows (dump.diff); unsplit $nu rows, partitioned $np; $ref" > "$NOTE"; exit 1; }
  echo "identical: $nu constants; $ref" > "$NOTE"
}

# ---- 6. cheap: DeepMind ArmDMTop axioms, RISC-V REVIEW axioms against the pinned list (all Lean 4.34.1)
s6a() {
  need 1
  ( cd "$WORK/deps/code-verification/arm64-semantics/Arm64" && lake build -q )
  ( cd "$R/Arm/apc" && lake build Blocks.ArmDMTop Blocks.AxiomsDM ) 2>&1 | tee "$OUT/s6a-dm.log"
  grep -q "C_correct_armDM' depends on axioms" "$OUT/s6a-dm.log"
  axioms "$OUT/s6a-dm.log"; echo "C_correct_armDM / C_runs_armDM: $STD" > "$NOTE"
}
s6b() {
  need 1
  [ -z "${RV_CACHE:-}" ] || { echo "RV_CACHE is gone: build-cache holds Lean 4.29 oleans of the old model"; exit 1; }
  [ "$(git -C "$WORK/deps/sail-riscv-lean" rev-parse HEAD)" = "$RV_REV" ]
  ( cd "$WORK/deps/sail-riscv-lean" && lake build )            # the regenerated model, from source
  ( cd "$R" && lake build $(cd "$R" && find Nano/Lexer Nano/Parser Nano/Ownership Nano/Codegen Nano/Run Nano/SelfHost Nano/Main Nano/Tests -name '*.lean' | sed 's|/|.|g; s|\.lean$||') )
  ( cd "$R" && Testing/scripts/review_axioms.sh ) | tee "$OUT/s6b-review.log"
  grep -q '^OK:' "$OUT/s6b-review.log"; echo "$(grep '^OK:' "$OUT/s6b-review.log") (model $(Testing/scripts/model_hash.sh "$WORK/deps/sail-riscv-lean" | cut -c1-8)…)" > "$NOTE"
}

run 1   "toolchains + pins"                 s1
run 6a  "DeepMind ArmDMTop axioms (4.34.1)" s6a
run 6b  "RISC-V review_axioms (4.34.1)"     s6b
run 2   "ARM model regeneration, byte-compare" s2
run 3   "unsplit ARM model build (time/RSS)"  s3
run 3b  "variant without SVE split"         s3b
run 4   "ARM proofs on the unsplit model"   s4
run 5   "fingerprints unsplit vs partitioned" s5

echo; echo "== results for $C ($OUT)" | tee "$OUT/summary.txt"
for s in 1 2 3 3b 4 5 6a 6b; do printf '%-3s %s\n' "$s" "$(cat "$OUT/status/$s" 2>/dev/null || echo 'NOT RUN')"; done | tee -a "$OUT/summary.txt"
! grep -q '^[^ ]* FAIL' "$OUT/summary.txt"

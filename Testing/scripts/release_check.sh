#!/usr/bin/env bash
# One-command release check of THIS checkout on Lean 4.34.1: runs every gate, prints a PASS/FAIL/SKIP table.
#   Testing/scripts/release_check.sh            run all gates (resumable)
# Style and conventions as Testing/scripts/bigbox/verify.sh: each gate runs in a strict subshell (set -euo pipefail),
# logs go to WORK/results/<commit>/<gate>.log, a gate with a status file is skipped on rerun (delete
# WORK/results/<commit>/status/<gate> to redo it). A gate whose tool or model path is missing is SKIP with the reason;
# SKIP is NOT a pass: the release is checked only when the table has no SKIP and no FAIL.
# Exit: 0 all PASS, 1 any FAIL, 2 no FAIL but some SKIP.  Nothing is pushed, no tracked file is changed (a gate that
# regenerates tracked files must leave them identical, or it FAILs). Reuses existing scripts; reimplements none.
#
# Gates (ids): toolchain spec words build review dm sail hashes fix23 fix1 examples cross
# Knobs: WORK (default ~/relcheck), GATES="spec words ..." (subset), DRY=1 (list gates and commands, run nothing),
#   TC (expected toolchain, default leanprover/lean4:v4.34.1), CV (DeepMind code-verification @ b0f729a, default
#   /home/user/deps/code-verification), ARMV9 (partitioned Sail ARM model, default /home/user/armv9-lean; Arm/sail's
#   lakefile reaches it as ../../../armv9-lean), RV_MODEL (default ../deps/sail-riscv-lean, the lakefile's path),
#   NANORUN=1 / QEMU use for examples (auto: QEMU if qemu-riscv64 exists), SEM=1 (examples also against semrun).
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); cd "$R"
WORK=${WORK:-$HOME/relcheck}
TC=${TC:-leanprover/lean4:v4.34.1}
CV=${CV:-/home/user/deps/code-verification}
ARMV9=${ARMV9:-/home/user/armv9-lean}
RV_MODEL=${RV_MODEL:-$R/../deps/sail-riscv-lean}
export PATH=$HOME/.elan/bin:$PATH
C=$(git rev-parse --short=10 HEAD)
DIRTY=$(git status --porcelain --untracked-files=no | wc -l)
OUT=$WORK/results/$C; mkdir -p "$OUT/status"
ALL="toolchain spec words build review dm sail hashes fix23 fix1 examples cross"
V=$R/Testing/nano/v2self
echo "commit $C ($(git log -1 --format=%s | cut -c1-70)); tracked changes: $DIRTY; WORK=$WORK; expected toolchain $TC"

# run ID TITLE FUNC: skip if done; else run FUNC in a strict subshell with its log; record PASS/FAIL/SKIP + note.
# FUNC writes a one-line note to $NOTE; "SKIP <reason>" there marks the gate skipped.
run() {
  local s=$1 title=$2 f=$3
  [[ " ${GATES:-$ALL} " == *" $s "* ]] || return 0
  if [ -n "${DRY:-}" ]; then echo "== $s $title -> function $f (dry run)"; echo "SKIP 0s $title: dry run" > "$OUT/status/dry.$s"; return; fi
  if [ -f "$OUT/status/$s" ]; then echo "== $s $title: done earlier ($(cut -d' ' -f1 "$OUT/status/$s"))"; return; fi
  echo "== $s $title (log $OUT/$s.log)"
  export NOTE=$OUT/$s.note; rm -f "$NOTE"
  local t0=$(date +%s) rc=0
  ( set -euo pipefail; $f ) > "$OUT/$s.log" 2>&1 || rc=$?
  local dt=$(( $(date +%s) - t0 )) note=""; [ -f "$NOTE" ] && note=$(cat "$NOTE")
  if [ $rc -ne 0 ]; then echo "FAIL ${dt}s $title: exit $rc, see $s.log. $note" > "$OUT/status/$s"
  elif [[ $note == SKIP* ]]; then echo "SKIP ${dt}s $title: ${note#SKIP }" > "$OUT/status/$s"
  else echo "PASS ${dt}s $title: $note" > "$OUT/status/$s"; fi
  tail -1 "$OUT/$s.log" | cut -c1-200; cat "$OUT/status/$s"
}
skip() { echo "SKIP $*" > "$NOTE"; exit 0; }                       # inside a gate: skip with a reason
miss() { for t in "$@"; do command -v "$t" > /dev/null || MISSING="${MISSING:-} $t"; done; [ -z "${MISSING:-}" ] || skip "missing tools:$MISSING"; }
axioms() { python3 "$R/Testing/scripts/bigbox/axioms.py" "$@"; }   # LOG...: FAIL unless every axiom set is standard

g_toolchain() {   # every lake project that is part of the release names the expected toolchain
  for f in lean-toolchain Arm/apc/lean-toolchain Arm/sail/lean-toolchain Arm/model/lean-toolchain; do
    [ "$(cat "$f")" = "$TC" ] || { echo "$f: $(cat "$f"), expected $TC"; exit 1; }
  done
  echo "4 lean-toolchain files = $TC" > "$NOTE"
}
g_spec() { Testing/scripts/spec_check.sh; echo "Spec/ = FROZEN.sha256 ($(wc -l < Spec/FROZEN.sha256) files)" > "$NOTE"; }
g_words() {       # sorry / admit / native_decide / bv_decide / sorryAx / axiom, comments and strings ignored
  local files; files=$(git ls-files 'Spec/*.lean' 'Arm/CompilerArm.lean' 'Arm/proofs/*.lean' \
    'Arm/shrink/*.lean' 'Arm/apc/*.lean' 'Arm/sail/*.lean' 'Nano/*.lean')   # Legacy/ is reference only, not scanned
  local bad; bad=$(echo "$files" | xargs python3 Testing/scripts/nocomment.py)
  [ -z "$bad" ] || { echo "$bad"; exit 1; }
  echo "$(echo "$files" | wc -l) files, none" > "$NOTE"
}
need_rv() { [ -d "$RV_MODEL" ] || skip "RISC-V model $RV_MODEL missing (lakefile path ../deps/sail-riscv-lean)"; }
g_build() { miss lake; need_rv; lake build; echo "lake build (default targets) ok" > "$NOTE"; }
g_review() {      # REVIEW theorems C_correctLO / C_runsO: build + pinned axioms
  miss lake; need_rv
  Testing/scripts/review_axioms.sh | tee "$OUT/review.out"; grep '^OK:' "$OUT/review.out" > "$NOTE"
}
g_dm() {          # C_correct_armDM / C_runs_armDM, standard axioms
  miss lake; [ -d "$CV" ] || skip "DeepMind checkout $CV missing"
  [ "$(git -C "$CV" rev-parse --short=7 HEAD)" = b0f729a ] || { echo "$CV is not at b0f729a"; exit 1; }
  ( cd "$CV/arm64-semantics/Arm64" && lake build -q )
  ( cd Arm/apc && lake build Blocks.ArmDMTop Blocks.AxiomsDM ) | tee "$OUT/dm-axioms.log"
  for t in C_correct_armDM C_runs_armDM; do grep -q "'$t' depends on axioms" "$OUT/dm-axioms.log"; done
  axioms "$OUT/dm-axioms.log"; echo "C_correct_armDM / C_runs_armDM: standard 3 axioms" > "$NOTE"
}
g_sail() {        # C_correct_armSail / C_runs_armSail, standard axioms (Reduce__1 opaque, as documented)
  miss lake; local M=$R/Arm/sail/../../../armv9-lean
  [ -d "$M/.lake/packages/Sail" ] || skip "partitioned Sail ARM model missing: $M (build it: Arm/sail/NOTES.md)"
  ( cd Arm/sail && lake build ArmSail ArmSail.Axioms && lake env lean ArmSail/Axioms.lean ) | tee "$OUT/sail-axioms.log"
  for t in C_correct_armSail C_runs_armSail; do grep -q "'$t' depends on axioms" "$OUT/sail-axioms.log"; done
  axioms "$OUT/sail-axioms.log"; echo "C_correct_armSail / C_runs_armSail: standard 3 axioms" > "$NOTE"
}
g_hashes() {      # Testing/scripts/model_hash.sh of each model present must appear in MODEL_PROVENANCE.md
  local P=Testing/notes/MODEL_PROVENANCE.md n=0 bad=0 sk=""
  for e in "RISC-V:$RV_MODEL" "ARM-model:$R/Arm/model" "ARM-partitioned:$ARMV9" "DeepMind-arm64:$CV/arm64-semantics/Arm64"; do
    local name=${e%%:*} dir=${e#*:}
    [ -d "$dir" ] || { sk="$sk $name"; echo "$name: $dir missing, not checked"; continue; }
    local h; h=$(Testing/scripts/model_hash.sh "$dir"); echo "$name $dir: $h"
    if grep -q "${h%% *}" "$P"; then n=$((n+1)); else echo "  NOT in $P"; bad=1; fi
  done
  [ $bad = 0 ] || exit 1
  [ $n -gt 0 ] || { echo "no model present"; exit 1; }
  if [ -n "$sk" ]; then echo "SKIP $n model(s) match MODEL_PROVENANCE.md; not checked (dir missing):$sk" > "$NOTE"
  else echo "$n models match MODEL_PROVENANCE.md" > "$NOTE"; fi
}
g_fix23() {       # B2 -> B3 by the interpreter nanorun, B2.sha256, checked-in B3 (no Lean, no QEMU needed)
  miss cc sha256sum; local T=$OUT/fix23; mkdir -p "$T"
  cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
  [ "$(sha256sum "$V/B2.bin" | cut -d' ' -f1)" = "$(cat "$V/B2.sha256")" ]
  "$T/nanorun" "$V/B2.bin" "$V/self_S_input.txt" "$T/B3.bin"
  cmp "$T/B3.bin" "$V/B2.bin"; cmp "$V/B3.bin" "$V/B2.bin"
  echo "B3 == B2 == checked-in B3, sha256 $(cut -c1-8 "$V/B2.sha256")..., $(stat -c %s "$V/B2.bin") B" > "$NOTE"
}
g_fix1() {        # B1 (Lean-compiled, trusted) -> B2 -> B3 on QEMU: boot/fixpoint.sh; B2 must equal the checked-in B2.bin
  miss lean leanc qemu-system-riscv64 python3
  Testing/nano/v2self/boot/fixpoint.sh "$OUT/fixpoint"
  cmp "$OUT/fixpoint/B2.bin" "$V/B2.bin"
  git diff --exit-code -- Testing/nano/v2self   # the script regenerates tracked files: they must come out identical
  echo "B1 -> B2 == checked-in B2.bin, B3 == B2, regenerated files identical" > "$NOTE"
}
g_examples() {    # compile each example with the checked-in B2 and run it; compare with its expect line
  miss cc
  local mode=QEMU; command -v qemu-riscv64 > /dev/null || command -v qemu-riscv64-static > /dev/null || mode=NANORUN
  if [ $mode = NANORUN ]; then export NANORUN=1; else miss riscv64-linux-gnu-gcc; fi
  [ -n "${SEM:-}" ] || export NOSEM=1
  Testing/nano/v2self/examples/run_examples.sh
  echo "$(ls Testing/nano/v2self/examples/*.lean | wc -l) examples via $mode$([ -n "${NOSEM:-}" ] && echo ', semrun not run (SEM=1)')" > "$NOTE"
}
g_cross() {       # RISC-V and ARM compilers build each other under QEMU (8 checks)
  miss qemu-aarch64 aarch64-linux-gnu-gcc riscv64-linux-gnu-gcc qemu-riscv64
  Testing/nano/v2self/arm/cross_check.sh | tee "$OUT/cross.out"
  [ "$(grep -c '^OK' "$OUT/cross.out")" = 8 ] && ! grep -q '^FAIL' "$OUT/cross.out"
  echo "cross_check.sh 8/8" > "$NOTE"
}
# cross_check.sh and run_examples.sh accept qemu-X or qemu-X-static; the gates' tool check wants the plain name
for q in qemu-aarch64 qemu-riscv64; do
  if ! command -v $q > /dev/null && command -v $q-static > /dev/null; then mkdir -p "$OUT/bin"; ln -sf "$(command -v $q-static)" "$OUT/bin/$q"; fi
done
[ ! -d "$OUT/bin" ] || export PATH=$OUT/bin:$PATH

run toolchain "toolchain files = $TC"            g_toolchain
run spec      "Spec/ vs FROZEN.sha256"           g_spec
run words     "no sorry/admit/native_decide/bv_decide" g_words
run build     "lake build (default targets)"     g_build
run review    "REVIEW + review_axioms.sh"        g_review
run dm        "ArmDMTop + axioms"                g_dm
run sail      "Arm/sail ArmSail + Axioms"        g_sail
run hashes    "model hashes vs MODEL_PROVENANCE" g_hashes
run fix23     "fixpoint B2 -> B3 (nanorun), B2.sha256" g_fix23
run fix1      "fixpoint B1 -> B2 -> B3 (boot/fixpoint.sh)" g_fix1
run examples  "examples"                         g_examples
run cross     "cross_check.sh (8 checks)"        g_cross

[ -z "${DRY:-}" ] || { echo "dry run: $(ls "$OUT/status" | grep -c '^dry\.') gates listed, nothing executed"; rm -f "$OUT"/status/dry.*; exit 0; }
echo; echo "== release check for $C ($OUT)" | tee "$OUT/summary.txt"
for s in $ALL; do [[ " ${GATES:-$ALL} " == *" $s "* ]] || continue
  printf '%-9s %s\n' "$s" "$(cat "$OUT/status/$s" 2>/dev/null || echo 'NOT RUN')"; done | tee -a "$OUT/summary.txt"
[ "$DIRTY" = 0 ] || echo "WARNING: $DIRTY tracked file(s) modified; the result is for the working tree, not for $C" | tee -a "$OUT/summary.txt"
! grep -q ' FAIL \|NOT RUN' "$OUT/summary.txt" || { echo "RELEASE CHECK FAILED" | tee -a "$OUT/summary.txt"; exit 1; }
! grep -q ' SKIP ' "$OUT/summary.txt" || { echo "INCOMPLETE: skipped gates are not checked" | tee -a "$OUT/summary.txt"; exit 2; }
echo "ALL GATES PASSED" | tee -a "$OUT/summary.txt"

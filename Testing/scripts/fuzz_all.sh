#!/bin/bash
# Continuous differential fuzzing: all generators, fresh seeds each round, results appended to Testing/notes/FUZZLOG.md.
# usage: Testing/scripts/fuzz_all.sh [ROUNDS]     env: SCALE (default 1: size knob), JOBS (parallel runners, default 4)
# A round: generate with seed S, run each generator's cases on QEMU + Sail (+ AArch64 QEMU for expressions), log one line.
# On a mismatch: the case file is saved to Testing/asm/fuzz-repro/<gen>_<seed>.txt, the generator is added to
# Testing/asm/work/disabled (skipped from then on), the line says MISMATCH and the script exits 1 after the round.
set -u
R=$(cd "$(dirname "$0")/../.." && pwd); cd "$R"; export PATH=$HOME/.elan/bin:$PATH
ROUNDS=${1:-1000000}; SCALE=${SCALE:-1}; JOBS=${JOBS:-4}
W=Testing/asm/work; mkdir -p $W Testing/asm/fuzz-repro; LOG=Testing/notes/FUZZLOG.md
[ -f $W/seed ] || echo 1000 > $W/seed
touch $W/disabled
[ -f $LOG ] || cat > $LOG <<'H'
# Fuzz log

One line per round of `Testing/scripts/fuzz_all.sh`: numbers are checked inputs / pairs (all agree unless the last column says otherwise).
Generators: `exp` = expressions (std RV64 + AArch64, 4-way), `fast` = expressions, unproved fast backends (4-way), `pipe` = random `Pipe`s
through `compileP`, `loop` = random terminating `Stmt` programs, `arr` = random `AStmt` programs with in-bounds loads/stores, `sort` = merge/insertion sort
machine code on adversarial inputs. Checks: Lean meaning == RV64 QEMU == Sail C emulator (== AArch64 QEMU for exp/fast).

| date (UTC) | commit | seed | exp | fast | pipe | loop | arr | sort | minutes | result |
|---|---|---|---|---|---|---|---|---|---|---|
H
dis() { grep -qx "$1" $W/disabled; }
LP="$(lake env printenv LEAN_PATH):$R/$W/lib"
[ -f $W/lib/CompilerArmFast.olean ] || bash Testing/asm/fast/build.sh
for ((r = 0; r < ROUNDS; r++)); do
  seed=$(cat $W/seed); echo $((seed + 1)) > $W/seed; T=$W/round_$seed; mkdir -p $T; t0=$(date +%s)
  declare -A N; bad=""
  for g in exp fast pipe loop arr sort; do N[$g]="-"; done
  run_gen() {  # name, generator command (writes $T/name.txt), runner command, count command
    local g=$1; dis $g && { N[$g]="off"; return; }
    if ! eval "$2" > $T/$g.txt 2> $T/$g.gen.err; then bad="$bad $g(gen-failed)"; return; fi
    local out; out=$(eval "$3" 2>&1); local rc=$?
    if [ $rc -ne 0 ]; then bad="$bad $g"; echo "$out" | head -5 > $T/$g.fail; cp $T/$g.txt Testing/asm/fuzz-repro/${g}_$seed.txt; echo $g >> $W/disabled; N[$g]="FAIL"
    else N[$g]=$(eval "$4"); fi
  }
  NE=$((300 * SCALE))
  run_gen exp  "LEAN_PATH=$LP SEED=$seed NCASES=$NE K=100 lake env lean Testing/asm/fuzz_exp.lean" "python3 Testing/asm/fuzzpar.py $T/exp.txt $JOBS" "grep -c '^t ' $T/exp.txt"
  run_gen fast "LEAN_PATH=$LP BACKEND=fast SEED=$seed NCASES=$NE K=100 lake env lean Testing/asm/fuzz_exp.lean" "python3 Testing/asm/fuzzpar.py $T/fast.txt $JOBS" "grep -c '^t ' $T/fast.txt"
  run_gen pipe "SEED=$seed NPROG=$((60 * SCALE)) K=24 lake env lean Testing/asm/gen_pipe.lean" "python3 Testing/asm/fuzz_run.py $T/pipe.txt $JOBS" "grep -c '^in ' $T/pipe.txt"
  run_gen loop "SEED=$seed NPROG=$((100 * SCALE)) K=16 lake env lean Testing/asm/gen_loop.lean" "python3 Testing/asm/fuzz_run.py $T/loop.txt $JOBS" "grep -c '^in ' $T/loop.txt"
  run_gen arr  "SEED=$seed NPROG=$((100 * SCALE)) K=8 lake env lean Testing/asm/gen_arr.lean" "python3 Testing/asm/fuzz_run.py $T/arr.txt $JOBS" "grep -c '^in ' $T/arr.txt"
  run_gen sort "python3 Testing/asm/gen_sort.py $seed $T/sort.txt --exhaustive 40 --random $((60 * SCALE)) 3000" "python3 Testing/asm/fuzz_run.py $T/sort.txt $JOBS" "grep -c '^in ' $T/sort.txt"
  mins=$(( ($(date +%s) - t0) / 60 ))
  res=ok; [ -n "$bad" ] && res="MISMATCH/FAIL:$bad"
  echo "| $(date -u +%F\ %H:%M) | $(git rev-parse --short HEAD) | $seed | ${N[exp]} | ${N[fast]} | ${N[pipe]} | ${N[loop]} | ${N[arr]} | ${N[sort]} | $mins | $res |" >> $LOG
  [ -z "$bad" ] && rm -rf $T
  unset N
  [ -n "$bad" ] && { echo "round $seed: $res (see $T/*.fail, Testing/asm/fuzz-repro/)"; exit 1; }
done

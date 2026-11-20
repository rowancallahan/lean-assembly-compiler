#!/usr/bin/env bash
# Exact RISC-V instruction counts (run/nanorun.c, a deterministic interpreter: one count per executed instruction).
# Self-compile (B2 compiles self_S_input.txt) and the 8 examples: compile with B2, then run the program on 4 inputs.
# usage: run_bench.sh [WORKDIR]     WORKDIR default: a new mktemp directory.   Output: bench/results/riscv.csv
# Needs a C compiler only. Takes about 2-3 minutes on the 2026 build box.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$(cd "$D/../../nano/v2self" && pwd)              # V = Testing/nano/v2self
W=${1:-$(mktemp -d)}; mkdir -p "$W" "$D/results"
cc -O2 "$V/run/nanorun.c" -o "$W/nanorun"
python3 "$D/make_inputs.py" "$W"
OUT="$D/results/riscv.csv"; echo "program,input,src_bytes,compile_instr,code_bytes,run_status,run_instr,out_bytes" > "$OUT"
# nr BINARY IN OUT -> sets NSTAT (a0 value), NINS (instructions), NOUT (output bytes); exits on trap (exit code 3)
nr() {
  local line; set +e; line=$("$W/nanorun" "$1" "$2" "$3" 2>&1 >/dev/null); local rc=$?; set -e
  [ $rc -eq 0 ] || [ $rc -eq 1 ] || { echo "trap: $line" >&2; exit 1; }
  NSTAT=$(sed -n 's/.*a0 = \(-\?[0-9]*\).*/\1/p' <<<"$line")
  NINS=$(sed -n 's/.*, \([0-9]*\) instructions.*/\1/p' <<<"$line")
  NOUT=$(sed -n 's/.*a1 = \([0-9]*\) output bytes.*/\1/p' <<<"$line")
}
# one compile: SRC -> $W/NAME.bin ; then runs on each input
bench_one() {   # bench_one NAME SRCFILE
  local n=$1 src=$2
  nr "$V/B2.bin" "$src" "$W/$n.bin"; local cinstr=$NINS cstat=$NSTAT
  [ "$cstat" = 0 ] || [ "$cstat" = 1 ] || { echo "$n: compile status $cstat" >&2; exit 1; }
  local cb; cb=$(stat -c %s "$W/$n.bin")
  if [ "$n" = self_S ]; then
    echo "$n,-,$(stat -c %s "$src"),$cinstr,$cb,-,-,$cb" >> "$OUT"
    echo "$n: compile $cinstr, code $cb bytes" >&2; return
  fi
  for s in 10 1k 100k 1m; do
    nr "$W/$n.bin" "$W/in_$s.bin" "$W/$n.$s.out"
    echo "$n,$s,$(stat -c %s "$src"),$cinstr,$cb,$NSTAT,$NINS,$NOUT" >> "$OUT"
    echo "$n $s: compile $cinstr, run $NINS, status $NSTAT, out $NOUT" >&2
  done
}
bench_one self_S "$V/self_S_input.txt"
for p in "$V"/examples/*.lean; do
  n=$(basename "$p" .lean); grep -v '^--' "$p" > "$W/$n.src"
  bench_one "$n" "$W/$n.src"
done
# self_S: the compiler on its own source (no program to run)
# synthetic programs: compile cost against source size (compile only)
python3 "$D/synth_scaling.py" "$W"
SC="$D/results/scaling.csv"; echo "program,src_bytes,compile_instr,code_bytes,compile_status" > "$SC"
for p in "$W"/chain_*.lean "$W"/expr_*.lean; do
  n=$(basename "$p" .lean); grep -v '^--' "$p" > "$W/$n.src"
  nr "$V/B2.bin" "$W/$n.src" "$W/$n.bin"
  echo "$n,$(stat -c %s "$W/$n.src"),$NINS,$(stat -c %s "$W/$n.bin"),$NSTAT" >> "$SC"
done
echo "wrote $OUT and $SC" >&2

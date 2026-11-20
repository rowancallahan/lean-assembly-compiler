#!/bin/sh
# run_loop.sh SELF_DIR WORK_DIR : endless differential fuzzing in 600 s segments (new seed each), stress.py every 5th.
# Logs: WORK_DIR/log/fuzz.log, WORK_DIR/log/stress.log. Mismatches: WORK_DIR/found/. Stop: kill the loop.
set -u
V=$(cd "$1" && pwd); W=$2; D=$(cd "$(dirname "$0")" && pwd); mkdir -p "$W/log"
n=0
while :; do
  n=$((n + 1))
  python3 "$D/fuzz.py" "$V" "$W" 600 "$(date +%s)$n" >> "$W/log/fuzz.log" 2>&1
  if [ $((n % 5)) -eq 0 ]; then
    echo "== stress round $n $(date -u +%H:%M:%S)" >> "$W/log/stress.log"
    python3 "$D/stress.py" "$V" "$W" >> "$W/log/stress.log" 2>&1
  fi
done

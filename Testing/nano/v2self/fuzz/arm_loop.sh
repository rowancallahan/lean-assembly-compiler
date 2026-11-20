#!/usr/bin/env bash
# Continuous ARM fuzzing: runs armfuzz.py for seeds FIRST, FIRST+1, ... alternating plain and far-address (BIG=1) mode.
# usage: arm_loop.sh WORKROOT [FIRST=100] [N=200] [ROUNDS=0 (0 = forever)]
# Each round writes WORKROOT/round_<seed>/summary.txt and appends a timestamped line to WORKROOT/log.txt.
set -u
ROOT=$1; FIRST=${2:-100}; N=${3:-200}; ROUNDS=${4:-0}
D=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$ROOT"; s=$FIRST; r=0
while [ "$ROUNDS" -eq 0 ] || [ "$r" -lt "$ROUNDS" ]; do
  big=$(( s % 2 )); w="$ROOT/round_$s"
  BIG=$big python3 "$D/armfuzz.py" "$s" "$N" "$w" > "$ROOT/out_$s.txt" 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) seed=$s big=$big rc=$rc $(grep -o 'mismatches=[0-9]*' "$w/summary.txt" 2>/dev/null)" >> "$ROOT/log.txt"
  s=$((s + 1)); r=$((r + 1))
done

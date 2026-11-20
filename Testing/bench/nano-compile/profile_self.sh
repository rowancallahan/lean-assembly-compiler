#!/usr/bin/env bash
# Per-function profile of the self-compile (B2 compiles self_S_input.txt) with bench/nanorun_prof.c (NANORUN_PROF).
# Writes results/self_S_regions.txt (top 25 function regions). usage: profile_self.sh [WORKDIR]   (about 15 s)
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$(cd "$D/../../nano/v2self" && pwd)
W=${1:-$(mktemp -d)}; mkdir -p "$W" "$D/results"
cc -O2 "$D/nanorun_prof.c" -o "$W/nanorun_prof"
NANORUN_PROF="$W/self_S.prof" "$W/nanorun_prof" "$V/B2.bin" "$V/self_S_input.txt" "$W/B2_again.bin"
cmp "$W/B2_again.bin" "$V/B2.bin"                  # the profiled run still reproduces B2 byte for byte
python3 "$D/profile_regions.py" "$V/B2.bin" "$W/self_S.prof" 25 > "$D/results/self_S_regions.txt"
cat "$D/results/self_S_regions.txt"

#!/bin/sh -e
# Build the partitioned model written by partition.py, recording peak RSS and time per module.
# usage: build_part.sh DIR [JOBS]   (DIR = partition.py's OUT; JOBS = concurrent lean processes, default 3)
# LEAN_NUM_THREADS bounds lake's concurrent jobs. 3 fits a 15 GB box: the largest part measured so far is listed in
# ARM_FAST.md §9. The core alone is `lake build Armv9Core`.
D=$1; J=${2:-3}; G=$(cd "$(dirname "$0")" && pwd)
export PATH=$HOME/.elan/bin:$PATH
cd "$D"
python3 "$G/rssmon.py" "$D/rss.txt" & M=$!
S=$(date +%s)
LEAN_NUM_THREADS=$J lake build Armv9Core Armv9 || { kill $M; exit 1; }
echo "full model built in $(( $(date +%s) - S )) s; peak MB / s / file in $D/rss.txt"
kill $M

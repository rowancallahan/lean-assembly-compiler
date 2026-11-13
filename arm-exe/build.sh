#!/bin/sh
# usage: build.sh <Module>...  ; builds each by name, logs wall time and peak RSS (sum of lean processes, sampled every 5 s)
export PATH=$HOME/.elan/bin:$PATH
H=$(cd "$(dirname "$0")"; pwd); cd "${D:-$H/../arm-exe-gen/armv9}"
L=$H/logs${D:+100}; mkdir -p $L
for m in "$@"; do
  ( peak=0; while sleep 5; do
      r=$(ps -eo rss,comm | awk '$2=="lean"||$2=="clang"||$2=="leanc"{s+=$1} END{print s+0}')
      [ $r -gt $peak ] && peak=$r && echo $peak > $L/$m.peak_kb
    done ) & S=$!
  t0=$(date +%s)
  lake build $m > $L/$m.log 2>&1; rc=$?
  kill $S
  echo "$m rc=$rc wall=$(( $(date +%s)-t0 ))s peak_kb=$(cat $L/$m.peak_kb)" | tee -a $L/summary.txt
done

#!/bin/bash
# usage: runall.sh MODE ARGS...   MODE: seed2 | big | sail
cd "$(dirname "$0")/.."; export WSUF=$1; export PATH=$(ls -d /tmp/leandl/x/*/bin):$PATH
FNS="bt_count bt_mirror bt_graftleft pos_tonat pos_plus nontail_sum_ln tail_sum_ln tail_reverse_ln list_append_ln level_hasparam level_isneverzero"
for f in $FNS; do
  case $1 in
    seed2) python3 fuzz5/fuzz5.py $f 2 300 qemu 2>&1 | tail -1 | cut -c1-400;;
    big) python3 fuzz5/fuzz5.py $f 3 0 qemu big 2>&1 | tail -1 | cut -c1-600;;
    sail) python3 fuzz5/fuzz5.py $f 4 25 sail 2>&1 | tail -1 | cut -c1-600;;
  esac
done

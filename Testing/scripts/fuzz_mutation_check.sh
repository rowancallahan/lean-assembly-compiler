#!/bin/bash
# Mutation sanity: for every generator, a deliberately wrong code word and a deliberately wrong expected value must be caught.
set -u
R=$(cd "$(dirname "$0")/../.." && pwd); cd "$R"; export PATH=$HOME/.elan/bin:$PATH
T=Testing/asm/work/mut; mkdir -p $T; LP="$(lake env printenv LEAN_PATH):$R/Testing/asm/work/lib"
SEED=${SEED:-77}
export FUZZ_TMO=15 TIMEOUT_NOTE=1
LEAN_PATH=$LP SEED=$SEED NCASES=20 K=20 lake env lean Testing/asm/fuzz_exp.lean > $T/exp.txt
LEAN_PATH=$LP BACKEND=fast SEED=$SEED NCASES=20 K=20 lake env lean Testing/asm/fuzz_exp.lean > $T/fast.txt
SEED=$SEED NPROG=6 K=8 lake env lean Testing/asm/gen_pipe.lean > $T/pipe.txt
SEED=$SEED NPROG=6 K=8 lake env lean Testing/asm/gen_loop.lean > $T/loop.txt
SEED=$SEED NPROG=6 K=8 lake env lean Testing/asm/gen_arr.lean > $T/arr.txt
python3 Testing/asm/gen_sort.py $SEED $T/sort.txt --exhaustive 12 --random 6 100
for g in exp fast pipe loop arr sort; do
  for m in word exp; do
    python3 Testing/scripts/fuzz_mutate.py $m $T/$g.txt $T/$g.$m.txt
    case $g in exp|fast) run="python3 Testing/asm/fuzzpar.py $T/$g.$m.txt 2";; *) run="python3 Testing/asm/fuzz_run.py $T/$g.$m.txt 2";; esac
    # the unmutated file must pass, the mutated one must fail
    if $run > $T/$g.$m.out 2>&1; then echo "$g/$m: NOT CAUGHT (mutated file passed)"; else echo "$g/$m: caught ($(grep -m1 -o 'MISMATCH.*\|AssertionError.*' $T/$g.$m.out | cut -c1-110))"; fi
  done
  case $g in exp|fast) run="python3 Testing/asm/fuzzpar.py $T/$g.txt 2";; *) run="python3 Testing/asm/fuzz_run.py $T/$g.txt 2";; esac
  $run > $T/$g.base.out 2>&1 && echo "$g/unmutated: passes" || echo "$g/unmutated: FAILS (unexpected)"
done

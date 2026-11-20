#!/bin/bash
# Self-run step 1: build of the `Nano.selfHosted` closure, heavy modules one at a time (ParseS3BStage ~8 GB,
# ParseS3BAllocB ~7.6 GB; lake 5 has no -j). Per step: /usr/bin/time -v + timeout; system memory sampled every 2 s
# (MemTotal - MemAvailable + swap used). Log: $OUT (default build.log next to this script).
set -e
cd "$(dirname "$0")/../../.."
export PATH=$HOME/.elan/bin:$PATH
OUT=${OUT:-Testing/nano/selfrun/build.log}; MEM=${OUT%.log}.mem
: > $OUT; : > $MEM
( while true; do awk '/MemTotal/{t=$2}/MemAvailable/{a=$2}/SwapTotal/{st=$2}/SwapFree/{sf=$2}END{print (t-a+st-sf)/1048576}' /proc/meminfo >> $MEM; sleep 2; done ) &
SAMPLER=$!; trap "kill $SAMPLER" EXIT
T0=$(date +%s)
step() {  # step <timeout> <target>
  echo "== $2" >> $OUT
  /usr/bin/time -v timeout $1 lake build $2 > >(grep -E "error|✖|Build completed" >> $OUT) 2> >(grep -E "Elapsed|Maximum resident|Exit status" >> $OUT)
}
# dependencies of the first heavy module (light modules, lake's default parallelism)
step 40m "Legacy.Nano.ParseS3B Legacy.Compiler.S3.Front Legacy.Nano.S3Stage Legacy.Nano.TokS3Enc"
step 10m Legacy.Nano.ParseS3BSelf
step 10m Legacy.Nano.ParseS3BAllocA
step 10m Legacy.Nano.ParseS3BAllocB
step 10m Legacy.Nano.ParseS3BStage
step 40m "Legacy.Nano.LexS3 Legacy.Nano.InlS3"
step 10m Legacy.Nano.LexS3Self
step 10m Legacy.Nano.LexS3Stage
step 10m Legacy.Nano.InlS3Self
step 10m Legacy.Nano.InlS3Stage
step 40m Legacy.Nano.ExpandMSelf
step 40m Legacy.Nano.ParseBSelfHost
step 40m Legacy.Nano.LeanLimits
step 10m Legacy.Nano.SelfHostFinal
echo "TOTAL wall $(( $(date +%s) - T0 )) s; peak system memory (RAM+swap used, GB): $(sort -g $MEM | tail -1)" >> $OUT

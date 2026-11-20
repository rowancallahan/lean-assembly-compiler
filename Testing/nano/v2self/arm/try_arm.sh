#!/usr/bin/env bash
# try_arm.sh: compile nano Lean programs ON ARM and run them in shim_arm. UNPROVEN glue (see README.md).
#   ./try_arm.sh                     self-check + every example (checks the "-- expect (hex)" line)
#   ./try_arm.sh prog.lean [input]   compile prog.lean, run it on the input file (default: empty), print output as hex and text
# Apple Silicon Mac: runs natively. Linux x86-64: needs aarch64-linux-gnu-gcc + qemu-aarch64 (static build).
set -euo pipefail
cd "$(dirname "$0")"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
case $(uname -m) in
  arm64|aarch64) cc -O2 ../run/shim/shim_arm.c -o shim_arm; Q="" ;;
  *) aarch64-linux-gnu-gcc -O2 -static ../run/shim/shim_arm.c -o shim_arm
     Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64) ;;
esac
run() { $Q ./shim_arm "$@" 2> "$T/err"; }                       # shim_arm CODE < in > out
hex() { od -An -tx1 | tr -s ' \n' ' ' | sed 's/^ //; s/ $//'; }
unhex() { printf "$(sed 's/\([0-9a-fA-F][0-9a-fA-F]\)/\\x\1/g; s/ //g')"; }
compile() {                                                      # compile $1 (Lean) -> $2 (ARM code)
  grep -v '^--' "$1" > "$T/src"                                  # the compiler accepts no comments
  run B2_arm.bin < "$T/src" > "$T/rv"                            # the compiler itself runs on ARM
  [ -s "$T/rv" ] || { echo "REJECTED by the compiler: $1"; return 1; }
  ./rv2arm.sh "$T/rv" > "$2"                                     # RISC-V -> ARM (nano translator, on ARM)
}

if [ $# -ge 1 ]; then                                            # one program
  compile "$1" "$T/prog"
  run "$T/prog" < "${2:-/dev/null}" > "$T/out"; cat "$T/err" >&2
  echo "hex:  $(hex < "$T/out")"
  echo "text: $(LC_ALL=C tr -c '\11\12\15\40-\176\200-\377' '.' < "$T/out")"   # raw bytes as text, control bytes shown as .
  exit 0
fi

h=$(run B2_arm.bin < ../self_S_input.txt | shasum -a 256 2>/dev/null || run B2_arm.bin < ../self_S_input.txt | sha256sum)
[ "${h%% *}" = "$(cut -d' ' -f1 ../B2.sha256)" ] && echo "OK   compiler on ARM compiles itself to B2.bin" \
  || { echo "FAIL self-compile"; exit 1; }
fail=0
for p in ../examples/*.lean; do
  n=$(basename "$p" .lean)
  compile "$p" "$T/$n" || { fail=1; continue; }
  paste <(sed -n 's/^-- input  (hex): *//p' "$p") <(sed -n 's/^-- expect (hex): *//p' "$p") |
  while IFS=$'\t' read -r i e; do
    got=$(echo "$i" | unhex | run "$T/$n" | hex)
    [ "$got" = "$e" ] && echo "OK   $n  in: $i  out: $got" || { echo "FAIL $n  in: $i  want: $e  got: $got"; exit 1; }
  done || fail=1
done
exit $fail

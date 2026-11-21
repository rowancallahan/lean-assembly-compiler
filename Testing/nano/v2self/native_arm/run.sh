#!/usr/bin/env bash
# run.sh prog.lean|prog.a64 input output : run a program as native AArch64 code (prog.lean is compiled first).
# The shim's status line (0 ok, 1 ok + empty, -1 out of work memory, -2 buffer capacity) goes to stderr. UNPROVEN glue.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
[ $# -eq 3 ] || { echo "usage: run.sh prog.lean|prog.a64 input output" >&2; exit 2; }
P=$1
case $P in *.lean) "$D/compile.sh" "$P" > "$T/prog"; P=$T/prog ;; esac
case $(uname -m) in arm64|aarch64) Q="" ;; *) Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64) ;; esac
$Q "$D/shim_arm" "$P" < "$2" > "$3"

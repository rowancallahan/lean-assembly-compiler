#!/usr/bin/env bash
# Content hash of a Lean model directory, independent of the working directory, the locale and any build output:
# sha256 of the `sha256sum` listing of every `.lean` file under DIR (paths relative to DIR, "./..."), excluding
# DIR/.lake (lake's packages and build), in byte order.  usage: model_hash.sh DIR   (prints "HASH FILES")
set -euo pipefail
cd "$1"
L=$(find . -path ./.lake -prune -o -type f -name '*.lean' -print | LC_ALL=C sort)
echo "$(printf '%s\n' "$L" | xargs sha256sum | sha256sum | cut -d' ' -f1) $(printf '%s\n' "$L" | wc -l)"

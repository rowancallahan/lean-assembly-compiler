#!/usr/bin/env bash
# Dead-code report for Nano/<stages>: runs deadcode.lean (constant reachability from REVIEW's roots) and adds the
# modules of Nano/<stages> outside REVIEW's import closure.  usage: Testing/scripts/deadcode.sh > report.txt
set -euo pipefail
lake build Nano.Main.REVIEW > /dev/null
T=$(mktemp -d)
lake env lean Testing/scripts/deadcode.lean > "$T/dc.txt"
cat "$T/dc.txt"
grep -E "^MOD-" "$T/dc.txt" | awk '{print $2}' | sort > "$T/closure"
find Nano/Lexer Nano/Parser Nano/Ownership Nano/Codegen Nano/Run Nano/SelfHost Nano/Main Nano/Tests -name "*.lean" | sed 's|/|.|g; s|\.lean$||' | sort > "$T/fs"
comm -23 "$T/fs" "$T/closure" | sed 's/^/MOD-OUTSIDE /'

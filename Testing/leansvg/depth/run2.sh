#!/bin/bash
export PATH=/tmp/claude-0/tc/lean-4.29.0-linux/bin:$PATH
cd /home/user/lean-assembly-compiler
export LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/claude-0/svg429/.lake/build/lib/lean
f=$1
timeout 240 lean --tstack=4000000 /tmp/claude-0/scr/one/$f.lean > /tmp/claude-0/scr/one/$f.out 2>&1; echo "EXIT $?" >> /tmp/claude-0/scr/one/$f.out

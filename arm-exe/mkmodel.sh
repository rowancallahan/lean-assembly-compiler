#!/bin/sh -e
# ArmRun/Model.lean = generated Armv9.lean minus its last 2 lines (the `def main`), so Run.lean can define its own main.
cd "$(dirname "$0")"; G=../arm-exe-gen/armv9/Armv9.lean
tail -n 2 $G | head -n 1 | grep -qx 'def main (_ : List String) : IO UInt32 := do'
head -n -2 $G > ArmRun/Model.lean

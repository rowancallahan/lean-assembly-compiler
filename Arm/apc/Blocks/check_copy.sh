#!/bin/sh -e
# Blocks/ArmBlockDefs.lean must be the two definition sections of Testing/nano/v2self/arm/ArmBlock.lean, unchanged.
cd "$(dirname "$0")"; S=../../../Testing/nano/v2self/arm/ArmBlock.lean
{ sed -n '/^\/-! ## register map/,/^\/-! ## J with link width W/p' $S | sed '$d'
  sed -n "/^\/-- the J step's memory accesses hit D/,/^\/-- \*\*Block correctness\*\*/p" $S | sed '$d'; } > /tmp/abd.$$
sed -n '/^\/-! ## register map/,/^end ArmBlock/p' ArmBlockDefs.lean | sed '$d' | diff - /tmp/abd.$$ && echo "ArmBlockDefs: verbatim"
rm -f /tmp/abd.$$
# Blocks/A64Defs.lean: wbyte/cbyte of Target.lean and A64Sem.lean's helper definitions, unchanged
N=../../../Nano/V2Self/Proof/Machine
{ sed -n '/^\/-- byte `k` (0..3) of a 32-bit word/,/^def cbyte/p' $N/Target.lean; echo
  sed -n '/^\/-- the 32-bit word `w` is stored/,/^\/-- \*\*the A64 step facts/p' $N/A64Sem.lean | sed '$d'; } > /tmp/a64.$$
sed -n '/^\/-- byte `k` (0..3) of a 32-bit word/,/^end JT/p' A64Defs.lean | sed '$d' | diff - /tmp/a64.$$ && echo "A64Defs: verbatim"
rm -f /tmp/a64.$$

#!/bin/sh -e
# Blocks/ArmBlockDefs.lean must be the two definition sections of Testing/nano/v2self/arm/ArmBlock.lean, unchanged.
cd "$(dirname "$0")"; S=../../../Testing/nano/v2self/arm/ArmBlock.lean
{ sed -n '/^\/-! ## register map/,/^\/-! ## J with link width W/p' $S | sed '$d'
  sed -n "/^\/-- the J step's memory accesses hit D/,/^\/-- \*\*Block correctness\*\*/p" $S | sed '$d'; } > /tmp/abd.$$
sed -n '/^\/-! ## register map/,/^end ArmBlock/p' ArmBlockDefs.lean | sed '$d' | diff - /tmp/abd.$$ && echo "ArmBlockDefs: verbatim"
rm -f /tmp/abd.$$

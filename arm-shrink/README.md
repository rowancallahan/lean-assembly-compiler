# Short equivalent definitions for the generated ARM model (hand-written, not generated)

Check a file: `cd armv9-lean && lake env lean --tstack=400000 ../arm-shrink/<file>` (after building the model).

| File | Original | Short version | Statement | Check time |
|---|---|---|---|---|
| `SysregFamily.lean` | 16 defs `DBGBCR_SysRegWrite32_*`, 1344 lines | 1 def `DBGBCR_write n`, 84 lines + 16 one-line theorems | each original = `DBGBCR_write k`, whole function, all inputs | ~2 s |
| `AddWithCarry.lean` | `AddWithCarry`, 18 lines | `x + y + c.zeroExtend _` | result component only, any width > 0; the 4 flag bits are NOT covered | ~1 s |

Axioms used: `propext`, `Classical.choice`, `Quot.sound` only.
Decoder fragment: not done.

## Repetition measurement (crude)

33,905 definitions, 577,055 lines. Replacing numerals, string literals and
capitalised identifiers by placeholders gives 14,529 distinct shapes; 299,213
lines (52%) are in shapes that occur more than once; one copy per shape would be
317,832 lines (55%). This is an upper bound on what parameterising alone saves:
identical shape does not guarantee the family is expressible as one function.
Largest families: 5,796 bitfield getters and 5,796 bitfield updaters (3 lines each).

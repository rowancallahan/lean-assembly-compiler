# lean-zip inflate: what each blocked function needs, and what landed since the probe

Input: `Testing/notes/LEANZIP_DEPTH.md`, `Testing/leanzip-depth/` (probe at `74263ff`, lean-zip @7e10583, lean-zip-common @6b7d018).
Compiler state: main `7c460cf`, read from `Testing/notes/frontx/NOTES.md` §16–§24. Text only: nothing was built or run.

## 0. Read first

**The probe's base already had §16–§21.** Its merge-base with main is `ce989e1` (2026-11-15). Features from §16 (`Except` with payloads, `do`/`throw`, `ByteArray` fields), §17 and §21 (user inductives), §20 (arrays) were on that base. The probe's first messages came from bare `frontx_compile` calls on each function.

**Probe rows that §16 already covers (inference, not re-run).** §16 lists verbatim entries at the base for `BitReader.readBit` (`:17`), `readBits` with `go` (`:29`), `alignToByte` (`:39`), `readUInt16LE` (`:44`) and `Zip.Native.readBitsFast` (`Inflate.lean:28`). The probe marks `readBit`/`readBits`/`readUInt16LE` as BAF/EXC. Its `readBit` message is the obligation `br.bitOff + 1 ≥ 8`, which §16 discharges with a human `requires br.bitOff < 8`. So for these three the blocker is probably a missing author `requires`, not BAF or EXC. `readBytes` (BAO result) is not covered.

**Landed on main after the probe base (52 commits).**

| section | commits | what | rows it touches |
|---|---|---|---|
| §22 `feat-muldiv` | `e485495` and the `mop` commits | `*`, `/`, `%` by variables (`mop`), guarded `>>>`, `Nat.gcd` | ARR: `countLengthsFast`, `kraftSumFast`, `nextCodesFast` (+ `.go`) are compiled verbatim on the `wa` path through entries `kraftE` and `nextCodesE`. **Possibly unblocked now**, but only on `wa`; the list path (`frontx_compile`) was not re-run. `copyLoopGo` has `k % distance`, which now translates, but it is still BAO-blocked. |
| §23 `speed-ind` | `a27045c`, `232525b` | `if h : c then … else` (`dite`), `=`/`==` through `DecidableEq`, `Decidable`-valued functions, `String` fields and `String` call arguments | STR: `DecodeTable.entryAt/lenAt/symAt` have `if h :` bodies, now allowed. The structure parameter still blocks them. No other row changes. |
| §24 `mem-spec` | `533dc01`…`cd14c5a` | run-time memory (`CompileRuns`, `CompileCorrect`) | **Inductive path only** (`IndMem.lean`). Does not address BAO (output growth). No row changes. |

Not touched by §22–§24, so the probe's status stands: USZ, MAT, INV, WF, TUP, PRFARG, BAO, and FOLD on the list path.

**Caveats on every "needs" figure (probe §1 and this document).**
- Each figure is an upper bound: the translator stops at the first unsupported construct, so bodies behind a rejected signature are untested.
- "Needs only X" is the transitive closure over `decode_callgraph.json`. A row is therefore a function whose whole subtree needs only X.

## Method (inferences marked)

- **Per node features (inferred):** the probe's first-failure class (from `decode_first_failures.tsv`) plus the `(+Y)` extras of probe §2's call tree. Probe classes `OK`, `CONST`, `DATA` count as supported.
- **Closure (inferred):** a node's need-set is its own features plus the need-sets of its callees, taken from `decode_callgraph.json`.
- **Line counts:** non-blank lines of the verbatim block in `DecodeOrig.lean`, not the source-file span. Nested `where` helpers (`.go`) carry their parent block's count and are marked.
- **Locations:** `file:line@rev`, rev `7e10583` (lean-zip) unless it says `6b7d018` (lean-zip-common). Taken from the block headers in `DecodeOrig.lean`.
- **Ordering:** smallest first by line count, then by name.

## 1. Functions by blocking feature

Features the user listed, in order. A feature with no row alone shows its two-feature nodes instead. Names are probe nodes (110 in the probe). Status is from §22–§24 and §16, with the rule in §0.

### ARR — `Array` as parameter/result of an inner function

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Crc32.Native.table` | 1 | Zip/Native/Crc32.lean:14@7e10583 | ARR | still blocked as a frontx unit; its table sits inside `crc32`/`updateBytes`, which `WaLeanZip` compiles via `wa` (probe §1) |
| 2 | `Zip.Native.Inflate.fixedDistCount` | 1 | Zip/Native/InflateTreeFree.lean:535@7e10583 | ARR | still blocked (no §22-24 change) |
| 3 | `Zip.Native.Inflate.fixedLitCount` | 1 | Zip/Native/InflateTreeFree.lean:532@7e10583 | ARR | still blocked (no §22-24 change) |
| 4 | `Crc32.Spec.mkTable` | 4 | Zip/Spec/Crc32.lean:78@7e10583 | ARR | still blocked as a frontx unit; its table sits inside `crc32`/`updateBytes`, which `WaLeanZip` compiles via `wa` (probe §1) |
| 5 | `Huffman.Spec.countLengths` | 5 | Zip/Spec/Huffman.lean:74@7e10583 | ARR | still blocked (no §22-24 change) |
| 6 | `Zip.Native.HuffTree.fillSlots` | 5 | Zip/Native/Inflate.lean:398@7e10583 | ARR | still blocked (no §22-24 change) |
| 7 | `Crc32.Spec.crcByteTable` | 6 | Zip/Spec/Crc32.lean:84@7e10583 | ARR | still blocked as a frontx unit; its table sits inside `crc32`/`updateBytes`, which `WaLeanZip` compiles via `wa` (probe §1) |
| 8 | `Zip.Native.HuffTree.countLongCodes` | 7 | Zip/Native/InflateTreeFree.lean:94@7e10583 | ARR | still blocked (no §22-24 change) |
| 9 | `Zip.Native.HuffTree.countLongCodes.go` (nested `where`; lines of parent) | 7 | Zip/Native/InflateTreeFree.lean:94@7e10583 | ARR | still blocked (no §22-24 change) |
| 10 | `Zip.Native.HuffTree.hasLongCode` | 8 | Zip/Native/InflateTreeFree.lean:176@7e10583 | ARR | still blocked (no §22-24 change) |
| 11 | `Zip.Native.HuffTree.hasLongCode.go` (nested `where`; lines of parent) | 8 | Zip/Native/InflateTreeFree.lean:176@7e10583 | ARR | still blocked (no §22-24 change) |
| 12 | `Zip.Native.HuffTree.kraftSumFast` | 8 | Zip/Native/Inflate.lean:555@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 13 | `Zip.Native.HuffTree.kraftSumFast.go` (nested `where`; lines of parent) | 8 | Zip/Native/Inflate.lean:555@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 14 | `Zip.Native.HuffTree.nextCodesFast` | 9 | Zip/Native/Inflate.lean:587@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 15 | `Zip.Native.HuffTree.nextCodesFast.go` (nested `where`; lines of parent) | 9 | Zip/Native/Inflate.lean:587@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 16 | `Huffman.Spec.nextCodes` | 10 | Zip/Spec/Huffman.lean:83@7e10583 | ARR | still blocked (no §22-24 change) |
| 17 | `Huffman.Spec.nextCodes.go` (nested `where`; lines of parent) | 10 | Zip/Spec/Huffman.lean:83@7e10583 | ARR | still blocked (no §22-24 change) |
| 18 | `Zip.Native.HuffTree.countLengthsFast` | 10 | Zip/Native/Inflate.lean:536@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 19 | `Zip.Native.HuffTree.countLengthsFast.go` (nested `where`; lines of parent) | 10 | Zip/Native/Inflate.lean:536@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |

Two-feature nodes containing ARR (after the single-feature rows above):

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 2 | `Crc32.Native.updateBytes` | ARR+FOLD | Zip/Native/Crc32.lean:17@7e10583 |
| 4 | `Crc32.Native.crc32` | ARR+FOLD | Zip/Native/Crc32.lean:22@7e10583 |
| 5 | `Zip.Native.Inflate.fillEntries` | ARR+TUP | Zip/Native/Inflate.lean:757@7e10583 |
| 6 | `Zip.Native.HuffTree.fromLengthsTree` | ARR+IND | Zip/Native/Inflate.lean:91@7e10583 |
| 8 | `Zip.Native.HuffTree.validateLengths` | ARR+EXC | Zip/Native/Inflate.lean:575@7e10583 |
| 14 | `Zip.Native.HuffTree.fillSlotsU` | ARR+PRFARG | Zip/Native/Inflate.lean:414@7e10583 |
| 16 | `Zip.Native.HuffTree.insertLoop` | ARR+IND | Zip/Native/Inflate.lean:72@7e10583 |

### EXC — `Except String β` result, `do`/`throw`

No node needs only this feature.


Two-feature nodes (EXC plus one other), smallest first:

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 6 | `Zip.Native.InflateBuf.takeBitsU` | EXC+USZ | Zip/Native/InflateFast.lean:126@7e10583 |
| 6 | `ZipCommon.BitReader.readBytes` | BAF+EXC | ZipCommon/BitReader.lean:54@6b7d018 |
| 7 | `Zip.Native.HuffTree.decodeSymCanon` | EXC+STR | Zip/Native/InflateTreeFree.lean:294@7e10583 |
| 8 | `Zip.Native.HuffTree.validateLengths` | ARR+EXC | Zip/Native/Inflate.lean:575@7e10583 |
| 8 | `ZipCommon.BitReader.readBits` | BAF+EXC | ZipCommon/BitReader.lean:29@6b7d018 |
| 8 | `ZipCommon.BitReader.readBits.go` | BAF+EXC | ZipCommon/BitReader.lean:29@6b7d018 |
| 8 | `ZipCommon.BitReader.readUInt16LE` | BAF+EXC | ZipCommon/BitReader.lean:44@6b7d018 |
| 10 | `Zip.Native.Inflate.decodeStored` | BAF+EXC | Zip/Native/Inflate.lean:848@7e10583 |
| … | 2 more, see the probe analysis | | |

### IND — user inductive `HuffTree`

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Zip.Native.HuffTree.insert` | 15 | Zip/Native/Inflate.lean:53@7e10583 | IND | still blocked (probe); §17/§21 inductive work at base, not checked against `HuffTree` |
| 2 | `Zip.Native.HuffTree.insert.go` (nested `where`; lines of parent) | 15 | Zip/Native/Inflate.lean:53@7e10583 | IND | still blocked (probe); §17/§21 inductive work at base, not checked against `HuffTree` |

Two-feature nodes containing IND (after the single-feature rows above):

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 6 | `Zip.Native.HuffTree.fromLengthsTree` | ARR+IND | Zip/Native/Inflate.lean:91@7e10583 |
| 16 | `Zip.Native.HuffTree.insertLoop` | ARR+IND | Zip/Native/Inflate.lean:72@7e10583 |

### STR — structure with array/USize fields as parameter/result

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Zip.Native.HuffTree.DecodeTable.entryAt` | 2 | Zip/Native/Inflate.lean:260@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 2 | `Zip.Native.HuffTree.DecodeTable.lenAt` | 2 | Zip/Native/Inflate.lean:228@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 3 | `Zip.Native.HuffTree.DecodeTable.symAt` | 2 | Zip/Native/Inflate.lean:234@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |

Two-feature nodes containing STR (after the single-feature rows above):

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 7 | `Zip.Native.HuffTree.decodeSymCanon` | EXC+STR | Zip/Native/InflateTreeFree.lean:294@7e10583 |
| 17 | `Zip.Native.HuffTree.subLookup` | EXC+STR | Zip/Native/InflateTreeFree.lean:272@7e10583 |

### TUP — tuple result holding arrays/structures

No node needs only this feature.


Two-feature nodes (TUP plus one other), smallest first:

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 5 | `Zip.Native.Inflate.fillEntries` | ARR+TUP | Zip/Native/Inflate.lean:757@7e10583 |

### BAF — `ByteArray` field of a structure

No node needs only this feature.


Two-feature nodes (BAF plus one other), smallest first:

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 6 | `ZipCommon.BitReader.readBytes` | BAF+EXC | ZipCommon/BitReader.lean:54@6b7d018 |
| 8 | `ZipCommon.BitReader.readBits` | BAF+EXC | ZipCommon/BitReader.lean:29@6b7d018 |
| 8 | `ZipCommon.BitReader.readBits.go` | BAF+EXC | ZipCommon/BitReader.lean:29@6b7d018 |
| 8 | `ZipCommon.BitReader.readUInt16LE` | BAF+EXC | ZipCommon/BitReader.lean:44@6b7d018 |
| 10 | `Zip.Native.Inflate.decodeStored` | BAF+EXC | Zip/Native/Inflate.lean:848@7e10583 |
| 10 | `ZipCommon.BitReader.readBit` | BAF+EXC | ZipCommon/BitReader.lean:17@6b7d018 |

### WF — recursion needing `from … measure`

No node needs only this feature.


### BAO — `ByteArray` result (output growth)

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `ByteArray.copyWithin` | 3 | Zip/Native/CopyWithin.lean:37@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 2 | `ByteArray.extendWithin` | 3 | Zip/Native/ExtendWithin.lean:63@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 3 | `ByteArray.copyWithinAt` | 4 | Zip/Native/InflateFast.lean:83@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 4 | `ByteArray.copyWithinAtGo` | 6 | Zip/Native/InflateFast.lean:62@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 5 | `Zip.Native.InflateBuf.storedCopyLoop` | 6 | Zip/Native/InflateFast.lean:596@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 6 | `ByteArray.fillDouble` | 7 | Zip/Native/ExtendWithin.lean:48@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched |

Two-feature nodes containing BAO (after the single-feature rows above):

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 3 | `ByteArray.copyWithinAtU` | BAO+USZ | Zip/Native/InflateFast.lean:91@7e10583 |
| 9 | `Zip.Native.Inflate.copyLoop` | BAO+PRFARG | Zip/Native/Inflate.lean:738@7e10583 |
| 10 | `Zip.Native.Inflate.copyLoopGo` | BAO+PRFARG | Zip/Native/Inflate.lean:710@7e10583 |

### PRFARG — proof arguments / `autoParam` in signatures

No node needs only this feature.


Two-feature nodes (PRFARG plus one other), smallest first:

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 9 | `Zip.Native.Inflate.copyLoop` | BAO+PRFARG | Zip/Native/Inflate.lean:738@7e10583 |
| 10 | `Zip.Native.Inflate.copyLoopGo` | BAO+PRFARG | Zip/Native/Inflate.lean:710@7e10583 |
| 11 | `ByteArray.ugetUInt64LE` | PRFARG+USZ | Zip/Native/Wide.lean:64@7e10583 |
| 14 | `Zip.Native.HuffTree.fillSlotsU` | ARR+PRFARG | Zip/Native/Inflate.lean:414@7e10583 |

### USZ — `USize` parameter

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Zip.Native.InflateBuf.trimBitBufU` | 2 | Zip/Native/InflateFast.lean:442@7e10583 | USZ | still blocked (no §22-24 change) |

Two-feature nodes containing USZ (after the single-feature rows above):

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 3 | `ByteArray.copyWithinAtU` | BAO+USZ | Zip/Native/InflateFast.lean:91@7e10583 |
| 6 | `Zip.Native.InflateBuf.takeBitsU` | EXC+USZ | Zip/Native/InflateFast.lean:126@7e10583 |
| 11 | `ByteArray.ugetUInt64LE` | PRFARG+USZ | Zip/Native/Wide.lean:64@7e10583 |

### MAT — two-argument `match` with a `succ` pattern

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Zip.Native.HuffTree.bitReverse` | 3 | Zip/Native/Inflate.lean:390@7e10583 | MAT | still blocked (no §22-24 change) |

### INV — `Nat %` by a non-power-of-2 constant

| # | function (probe name) | lines | file:line@rev | probe class | status |
|---|---|---:|---|---|---|
| 1 | `Adler32.Native.updateBytes` | 2 | Zip/Native/Adler32.lean:13@7e10583 | INV | still blocked (needs author `requires`; §22-24 do not change it) |
| 2 | `Adler32.Native.adler32` | 4 | Zip/Native/Adler32.lean:17@7e10583 | INV | still blocked (needs author `requires`; §22-24 do not change it) |
| 3 | `Adler32.Spec.updateByte` | 4 | Zip/Spec/Adler32.lean:29@7e10583 | INV | still blocked (needs author `requires`; §22-24 do not change it) |

### FOLD — `Array.foldl` over `ByteArray.data` with a table

No node needs only this feature.


Two-feature nodes (FOLD plus one other), smallest first:

| lines | function | needs | file:line@rev |
|---:|---|---|---|
| 2 | `Crc32.Native.updateBytes` | ARR+FOLD | Zip/Native/Crc32.lean:17@7e10583 |
| 4 | `Crc32.Native.crc32` | ARR+FOLD | Zip/Native/Crc32.lean:22@7e10583 |


## 2. Leaves of the `inflate` call tree

Reach from `Zip.Native.Inflate.inflate` is 76 nodes; 62 blocked, 14 supported (6 verbatim + 8 constants), matching probe §2. A leaf here is a blocked node whose callees are all supported or constant (computed from `decode_callgraph.json`).

| # | leaf (probe name) | lines | file:line@rev | needs | status |
|---|---|---:|---|---|---|
| 1 | `Zip.Native.HuffTree.DecodeTable.entryAt` | 2 | Zip/Native/Inflate.lean:260@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 2 | `Zip.Native.HuffTree.DecodeTable.lenAt` | 2 | Zip/Native/Inflate.lean:228@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 3 | `Zip.Native.HuffTree.DecodeTable.symAt` | 2 | Zip/Native/Inflate.lean:234@7e10583 | STR | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 4 | `ByteArray.copyWithin` | 3 | Zip/Native/CopyWithin.lean:37@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched — source has `@[extern]`; verbatim body only |
| 5 | `Zip.Native.HuffTree.DecodeTable.entryAtU` | 3 | Zip/Native/Inflate.lean:279@7e10583 | PRFARG+STR+USZ | still blocked (structure parameter); `if h :` bodies now allowed (§23 `dite`) |
| 6 | `Zip.Native.HuffTree.bitReverse` | 3 | Zip/Native/Inflate.lean:390@7e10583 | MAT | still blocked (no §22-24 change) |
| 7 | `Huffman.Spec.countLengths` | 5 | Zip/Spec/Huffman.lean:74@7e10583 | ARR | still blocked (no §22-24 change) |
| 8 | `Zip.Native.HuffTree.fillSlots` | 5 | Zip/Native/Inflate.lean:398@7e10583 | ARR | still blocked (no §22-24 change) |
| 9 | `Zip.Native.Inflate.fillEntries` | 5 | Zip/Native/Inflate.lean:757@7e10583 | ARR+TUP | still blocked (no §22-24 change) |
| 10 | `ZipCommon.BitReader.readBytes` | 6 | ZipCommon/BitReader.lean:54@6b7d018 | BAF+EXC | still blocked (no §22-24 change) |
| 11 | `ByteArray.fillDouble` | 7 | Zip/Native/ExtendWithin.lean:48@7e10583 | BAO | not unblocked: §24 is inductive-path only; ByteArray growth untouched — source has `@[extern]`; verbatim body only |
| 12 | `Zip.Native.HuffTree.countLongCodes.go` (nested) | 7 | Zip/Native/InflateTreeFree.lean:94@7e10583 | ARR | still blocked (no §22-24 change) |
| 13 | `Zip.Native.HuffTree.hasLongCode.go` (nested) | 8 | Zip/Native/InflateTreeFree.lean:176@7e10583 | ARR | still blocked (no §22-24 change) |
| 14 | `Zip.Native.HuffTree.kraftSumFast.go` (nested) | 8 | Zip/Native/Inflate.lean:555@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 15 | `ZipCommon.BitReader.readUInt16LE` | 8 | ZipCommon/BitReader.lean:44@6b7d018 | BAF+EXC | partly covered at base (§16 entry `readBitE`/`readBitsE`/`readUInt16LE5E`); bare form needs author `requires` |
| 16 | `Zip.Native.HuffTree.nextCodesFast.go` (nested) | 9 | Zip/Native/Inflate.lean:587@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 17 | `Huffman.Spec.nextCodes.go` (nested) | 10 | Zip/Spec/Huffman.lean:83@7e10583 | ARR | still blocked (no §22-24 change) |
| 18 | `Zip.Native.HuffTree.countLengthsFast.go` (nested) | 10 | Zip/Native/Inflate.lean:536@7e10583 | ARR | **possibly unblocked now** (§22 `wa` entries `kraftE`, `nextCodesE` with `countLengthsFast`; verified there, not on the list path) |
| 19 | `Zip.Native.Inflate.copyLoopGo` | 10 | Zip/Native/Inflate.lean:710@7e10583 | BAO+PRFARG | not unblocked: §24 is inductive-path only; ByteArray growth untouched |
| 20 | `ZipCommon.BitReader.readBit` | 10 | ZipCommon/BitReader.lean:17@6b7d018 | BAF+EXC | partly covered at base (§16 entry `readBitE`/`readBitsE`/`readUInt16LE5E`); bare form needs author `requires` |
| 21 | `Zip.Native.HuffTree.fillSlotsU` | 14 | Zip/Native/Inflate.lean:414@7e10583 | ARR+PRFARG | still blocked (no §22-24 change) |
| 22 | `Zip.Native.HuffTree.insert.go` (nested) | 15 | Zip/Native/Inflate.lean:53@7e10583 | IND | still blocked (probe); §17/§21 inductive work at base, not checked against `HuffTree` |

## 3. Summary

- **Possibly unblocked now (on `wa` only):** `countLengthsFast` (`Inflate.lean:536`, 10 lines), `kraftSumFast` (`:555`, 8), `nextCodesFast` (`:587`, 9), each with its `where` helper. Smallest first.
- **Smallest single-feature rows that remain blocked:** `DecodeTable.symAt/lenAt/entryAt` (STR, 2 lines each, structure parameter), `trimBitBufU` (USZ, 2), `bitReverse` (MAT, 3), `Adler32.Native.updateBytes` (INV, 2 lines but needs an author `requires`).
- **No function needs only EXC, WF, TUP, BAF, PRFARG or FOLD.** Their smallest two-feature nodes are listed in §1.
- **Gzip/zlib entry points** (`GzipDecode.decompress` and `ZlibDecode.decompress`) are not in the inflate tree and are not in these tables beyond the probe names. The probe stops at their result type `Except String ByteArray` (EXC plus BAO, inferred from that message); their bodies were not reached.

## 4. Inferences and what was not checked

- The feature set per node comes from the probe's messages plus the `(+Y)` extras of probe §2. The messages stop at the first unsupported construct, so these sets may be incomplete.
- §16, §22 and §23 claims are from `NOTES.md` text, not re-run. The `wa` status for `countLengthsFast`/`kraftSumFast`/`nextCodesFast` depends on the entries `kraftE`/`nextCodesE` existing as NOTES §22 says.
- `ByteArray.copyWithin`, `extendWithin` and `fillDouble` have `@[extern]` attributes in their source; this table covers the Lean body only.
- The `if h :` count is a grep over `DecodeOrig.lean`, not a per-node check of which bodies translate.
- Nothing was compiled, and no probe was re-run for this document.

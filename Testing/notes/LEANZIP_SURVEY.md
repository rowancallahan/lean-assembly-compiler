# lean-zip survey: pure kernels for the frontx compiler

Source: `rowancallahan/lean-zip` at 7e10583 (Lean 4.34.0) plus its dependency `kim-em/lean-zip-common` (`BitReader`).
Compiler: this repo, front end `Riscv/Frontx` on Lean 4.29. Only `Zip/Native/*` is implementation; `Zip/Spec/*` (≈50 k
lines, list-based reference functions and proofs) is not listed. Counts are from reading and `grep`, not a build of lean-zip.

Global facts: no `partial`, no `unsafe`, no `IO` in `Zip/Native`. Recursion is structural or well-founded
(`termination_by`: Inflate 21, InflateFast 7, InflateTreeFree 11, Deflate 54, DeflateDynamic 25). Four extern shims
with a pure reference body (`Wide.lean` `ugetUInt32LE/64LE`, `usetUInt*`, `CopyWithin`, `ExtendWithin`, `TokenArray`);
many `USize` / `@[specialize]` / `@[inline]` fast-path twins of one reference function (`go`, `goFused`, `goFusedP`,
`goFusedPU`, `goCur`, `goCurU`, `goCurUW`, `goTreeFree`, `goTreeFreeU`, …: same result, proved equal in `Spec/`).
Compile the *reference* member of each family, not the fast twins.

## 1. Pure implementation functions

Size = lines of the `def` (approx.). "Callers" = direct callers in `Zip/Native`.

| function | file:line | types | recursion | size | callers |
|---|---|---|---|---|---|
| `Adler32.Native.updateBytes/adler32` (+ `Spec.updateByte`, `pack`) | Native/Adler32.lean:14,19; Spec/Adler32.lean:29 | `ByteArray`, state `Nat × Nat`, `% 65521`, result `UInt32` | `Array.foldl` | 4 + 3 | Gzip.lean (zlib trailer) |
| `Crc32.Native.updateBytes/crc32`, `table`, `Spec.crcByteTable/mkTable/crcBit` | Native/Crc32.lean:17,21,25; Spec/Crc32.lean:30,78,84 | `ByteArray`, constant `Array UInt32` (256, `Array.ofFn`), `UInt32` | `Array.foldl`; bitwise `crcBit` ×8 | 4 + 5 + 3 | Gzip.lean:131,157 |
| `BitReader.readBit/readBits/alignToByte/readUInt16LE/readBytes` | lean-zip-common ZipCommon/BitReader.lean:17–54 | `structure {data : ByteArray, pos bitOff : Nat}`, `Except String (UInt32 × BitReader)`, `ByteArray.extract` | `readBits.go` structural on `n` | 5–12 each | Inflate (all block types) |
| `readBitsFast` (+`go`) | Native/Inflate.lean:28 | same, cursor as two `Nat`s | structural on `n` | 15 | extra bits in `decodeHuffmanFast` |
| `HuffTree.insert/insertLoop/fromLengthsTree/fromLengths` | Inflate.lean:53–110 | `inductive HuffTree` (leaf/node/empty), `Array UInt8` lengths, `Array UInt32` next codes | WF / structural | 60 | build of trees |
| `HuffTree.decode(.go)` | Inflate.lean:116 | `HuffTree`, `BitReader`, `Except` | structural on tree + depth guard | 12 | reference decode |
| `tableEntry`, `buildTable`, `buildTableCanonical(Fast)`, `countLengthsFast`, `nextCodesFast`, `kraftSumFast`, `fillSlots(U)`, `bitReverse` | Inflate.lean:150–620 | `Array UInt32/UInt8/Nat`, `DecodeTable := {packed : Array UInt32}`, writes with `Array.set` | WF loops on `Nat` | ≈250 | table build per block |
| `DecodeTable.entryAt`, `decodeSym`, `walkTree`, `takeBits`, `refill` | Inflate.lean:260,1170,1154,1180,1141 | `UInt32/UInt64` bit buffer, `Nat` count, `Except String (UInt16 × UInt64 × Nat × Nat)` | `refill` WF; `walkTree` structural on tree | 5–15 each | `go*` loops |
| `copyLoopGo`, `copyLoop`, `CopyWithin.copyWithin`, `ExtendWithin.extendWithin/fillDouble` | Inflate.lean:710,738; Native/CopyWithin.lean, ExtendWithin.lean | `ByteArray` read and `push`ed in the same buffer, `k % distance` | WF on `length - k` | 10–15 | every back-reference |
| `decodeStored`, `storedCopyLoop`, `decodeStoredCur` | Inflate.lean:848; InflateFast.lean:596,606 | `BitReader`, `UInt16`, `ByteArray ++`/`set!`, `Except` | `storedCopyLoop` WF | 12 | `inflateLoop*` |
| `decodeDynamicTrees`, `readCLCodeLengths`, `decodeCLSymbols`, `fillEntries` | Inflate.lean:757–846 | `Array UInt8`, `HuffTree`, `Except` | WF | ≈90 | dynamic blocks |
| `go/goFused/…/goTreeFreeU` (symbol loop), `decodeHuffmanFast*`, `inflateLoop*`, `inflate*` | Inflate.lean:1198–1640; InflateFast.lean; InflateTreeFree.lean | `ByteArray` output (`push`), `UInt64` buffer, tables, `Except String (ByteArray × …)` | WF on `dataSize*8 - bitpos`, tail-recursive | 60–150 each | `inflate`, `Gzip.decompress` |
| `lz77Greedy(.countMatch/.go/.goU/.goUW)`, `lz77Chain*`, `lz77ChainLazy*`, `lz77LazyMergedLoop*`, `chainWalk*`, `hash3*`, `updateHashes*` | Deflate.lean:495–3250; DeflateL5.lean | `ByteArray`, `Array Nat` hash/prev tables (`set`), `Array UInt32` / `TokenArray` output, `USize` | WF; tail-recursive `mainLoop` | 3 000 lines | `deflateRaw*` |
| `findLengthCode/findDistCode`, `lenCodeWord`, `canonicalCodes`, `fixed*Codes` | Deflate.lean:61–350 | `Array`, `Option (Nat × Nat × UInt32)` | WF / `Array.ofFn` | ≈150 | emit |
| `BitWriter.writeBits/writeBits64/writeHuffCode/reverse16/flush*` | Native/BitWriter.lean:345–565 | `structure {data : ByteArray, bitBuf : UInt64, bitCount : UInt8}`, `UInt64` shifts, `USize` | structural / none | 5–30 each | emit |
| `computeCodeLengthsN`, `mergeLoopN`, `huffTreeDepthsN`, `fixKraftListN` | Native/HuffmanEncode.lean | `List (Nat × Nat)`, `Array Nat` | WF | ≈400 | dynamic-block header |
| `deflateStored` | Deflate.lean:28 | `ByteArray`, `Id.run` `while`, `extract`, `++` | `while` | 25 | level 0 |
| `Gzip`/`Zlib` `compress/decompress` | Native/Gzip.lean | wrap the above; `Except` | — | 300 | API |

## 2. Classification against the compiler today

Compiler today (from `frontx/NOTES.md` §12 and this survey's runs): tail recursion (structural, `termination_by`, `for`) over
`BitVec 64`, `UInt8/32/64`, bounded `Nat`; read-only `ByteArray` and `List UInt8` views; results scalar, `Nat`, `Bool`,
`Option UInt8`, `List UInt8` (output block); `if`/`match`, helper inlining; `+ - &&& ||| ^^^ >>>`, `<<<` (literal, `Nat`),
comparisons; multiplication by a `Nat` literal. No multiply otherwise, no `/` `%`, no calls, no mutable arrays, no structures,
no `Except`/pairs, no constant data.

- **A** works now as is; **B** works after a small restatement (done and tested for four, §4); **C** needs feature X.

| function | class | what decides it |
|---|---|---|
| `Spec.crcBit/crcByte`, bitwise CRC loop | **A** | already `crcRaw` (`Frontx/Examples.lean`, `crcGo`), 810 → 201 words; same function as `Spec.crcByte` up to the final `^^^ 0xFFFFFFFF` |
| Adler-32 | **B** (done) | `% 65521` → one conditional subtraction (both operands `< 2·65521`); `Nat × Nat` state → two `UInt32`; pair `pack` → `Nat` `b*65536 + a`. Verbatim needs X1 (`%`/`/` by constant) and X2 (pair state) |
| `readBitsFast`, `BitReader.readBits` | **B** value only (done); **C** verbatim | `Except` / pair result (X3), `BitReader` structure parameter (X4), `UInt32 <<<` lemma (X5) |
| `decodeSym`, table hit path | **B** (done) | table as bytes in the input block, `le32` by four guarded loads; verbatim needs `Array UInt32` constant/argument (X6: word arrays), `Except`, and `walkTree` (X7: user inductive) |
| `countMatch.go` | **B** (done) | hypotheses `h1 h2` replaced by run-time guards, index kept as running position (G2); verbatim: Prop parameters. `goU/goUW` need `USize` + 8-byte `extern` load (X6) |
| `Crc32.Native` table CRC | **C** | constant 256-word table (X8: static data) or word arrays (X6); `Array.foldl` closure over the table (X9: specialised fold) |
| `deflateStored` | **C** | `Id.run`/`while` building a `ByteArray` with `push` and `++` (output with growth, X10), two nested loops, `UInt16` header bytes |
| `decodeStored`, `storedCopyLoop` | **C** | `Except`, header-derived length passed to the copy (X11: calls or sequenced loops), `set!` into the output block (store node exists in `Tree`, not generated) |
| `copyLoopGo/copyLoop/extendWithin` | **C** | reads the block it appends to (X12: output readable, same block), `k % distance` (X1), `push` (X10) |
| `HuffTree` insert/decode, `tableEntry` | **C** | recursive inductive data (X7), allocation |
| `buildTable*`, `countLengthsFast`, `nextCodesFast`, `fillSlots` | **C** | `Array` writes, results are arrays (X13: mutable arrays of words, work area), `Nat` arithmetic with `*`, `/` |
| `go*` symbol loop, `inflateLoop*`, `inflate` | **C** | everything above, plus `Except`, several mutable state components (X2), calls (X11), output growth (X10) |
| `lz77*` matchers | **C** | `Array Nat` hash/prev tables with writes (X13), `Array UInt32`/`TokenArray` output (X13), multiply (`* 0x1E35A7BD`, X14), `Option` chains, `USize` |
| `BitWriter.*` | **C** | structure state (X4), `UInt64` shifts by variables, `ByteArray.push` (X10) |
| `computeCodeLengthsN` & co | **C** | `List (Nat × Nat)`, `Array Nat` updates, WF with several arrays (X13) |

Features, in the order that unlocks the most (no X is implemented by this branch):

| X | feature | unlocks |
|---|---|---|
| X1 | `%`, `/` by a constant (shift/mask for 2^k; conditional subtraction or multiply-high otherwise) | Adler verbatim, `k % distance`, hash tables |
| X2 | pair / tuple state and results (several result variables; `UInt64 × UInt64` is rejected today) | Adler, BitReader, every `go` loop result |
| X3 | `Except`/`Option` with payload ≠ `UInt8` (tag + payload words) | all `decode*`, `readBits` |
| X4 | `structure` parameters and results flattened into variables | `BitReader`, `BitWriter` |
| X5 | `r32 (a <<< b)` lemma (`Rep.lean`; see G1) | readBits, pack, `le32` |
| X6 | word arrays: read-only `Array UInt32` / 4- and 8-byte loads | tables, `crc` table, `ugetUInt64LE` |
| X7 | small user inductives (tree) | `HuffTree` (or replace by the canonical table form, which lean-zip already has) |
| X8 | constant data placed in the code image | CRC table, `lengthBase`, `distBase`, fixed code lengths |
| X9 | `Array.foldl` / `ByteArray.foldl` with a known function (specialisation exists: `frontx_spec`) | `Crc32.updateBytes`, `Adler32.updateBytes` |
| X10 | output with growth (`push`, `++`) into a pre-sized output block with length | all producers |
| X11 | calls / sequenced loops | `inflate` = header + body + copy |
| X12 | reading the output block while writing it | LZ77 back-reference |
| X13 | mutable arrays of words/Nat in the work area | table build, hash chains |
| X14 | general multiply | hash, `lazyAcceptCost` (`4 * (len2 - len1)` is a literal and fine) |

## 3. Six kernels, smallest first, one new feature each

| # | kernel | smallest form | new feature (what is missing for the *verbatim* function) | status |
|---|---|---|---|---|
| 1 | Adler-32 full (`Adler32.Native.adler32 1`) | `adlerGo`, 7 lines | X1 `%` by 65521, X2 pair state | **B done**, tested |
| 2 | CRC-32 with table (`Crc32.Native.crc32`) | table lookup per byte | X8/X6 constant table or word array, X9 | C; not tried. (bitwise A: `crcRaw`) |
| 3 | bit reader `readBits n` | `rbGo`, 8 lines | X3 `Except`, X4 structure, X5 `<<<` | **B done** (value only), tested |
| 4 | Huffman decode, one symbol (`decodeSym`) | `huffAt`, 6 lines | X6 `Array UInt32` table, X3, X7 for the `walkTree` fallback | **B done** (hit path), tested |
| 5 | LZ77 match length (`countMatch.go`) | `cmGo`, 5 lines | Prop parameters, G2; `USize` wide loads for the fast twin | **B done**, tested |
| 6 | stored-block inflate (`decodeStored`) and back-reference copy (`copyLoopGo`) | header + `storedCopyLoop` | X11 sequencing/calls, X3, X10, X12 | C; not tried |

## 4. What was run

`Riscv/Frontx/LeanZip.lean` (4 restatements, entry points, `g.implements1` machine theorems, all through the existing
`frontx_compile` / `frontx_entry` / `frontx_implements`; nothing proved by hand; no `sorry`, no new axioms; `exec` of `adlerGo` checked
to depend on `propext`, `Classical.choice`, `Quot.sound` only, `implements1` has the usual Sail-model set).
`Testing/asm/emit_leanzip.lean` writes `Testing/asm/frontx-words/lz*.{words,cases}`; **the expected results come from
verbatim copies of lean-zip's functions** (`Ref` namespace in the emitter, Lean `#eval`), not from the restatements.
`python3 Testing/asm/frontx_test.py check N lz…` runs the `Implements1` convention on QEMU and the Sail C emulator.

| entry point | restatement of | words | work bytes | cases | result |
|---|---|---|---|---|---|
| `lzadler` | `Adler32.Native.adler32 1` | 123 | 103 | 71, lengths 0..2769 | QEMU = Sail = Lean; Lean reference also = `zlib.adler32` on all 71 |
| `lzreadbits` | `readBitsFast ⟨xs,0,3⟩ 13` value | 174 | 143 | 67 (inputs ≥ 2 bytes: the original errors below) | ok |
| `lzhuffsym` | `decodeSym` table hit, buffer + 2048-word table (input up to 8200 bytes) | 171 | 119 | 40 (10 fallback, 30 hits) | ok |
| `lzmatch04` | `countMatch.go data 0 4 0 (size-4)` | 105 | 87 | 111 (29 non-zero lengths, max 439) | ok |

Differences to the originals (all stated in the file header comments):
Adler: `Nat × Nat` + `%` → two `UInt32` + conditional subtraction, result `Nat` `b*65536 + a`. readBits: no `BitReader`/`Except`, reads past
the end give 0, `acc ||| bit <<< shift` → `acc + w`, `w := w + w`. huffSym: table is in the input block, index from two bytes (the original
masks a `UInt64`), fallback returns `0xFFFFFFFF`, result `Nat`. countMatch: bounds as run-time tests, running positions.
Not proved: the equality of a restatement with the original (only tested). Easy to prove for 1 and 5, not tried.

### Front-end findings (translator gaps found by these runs, all with a workaround used above)

| id | observation | workaround |
|---|---|---|
| G1 | `UInt32` `a <<< b` has no `Rep` lemma: goal `r32 b <<< 16 &&& 0xffffffff ||| r32 a = r32 (b <<< 16) ||| r32 a` stuck (`Rep.lean` has `r32_shr`, `rN_shl` only; the header comment says `<<<` is supported) | `Nat` arithmetic, doubling weight |
| G2 | load with a sum index under `dite … ∧ …`, `xs[p1 + i]`: `generalize failed: metavariable already assigned` (internal) | running position `a` instead of `p1 + i` |
| G3 | load at a literal index in a non-parameterised body (`xs[0]`): simp rewrites `0 < xs.size` to `¬ xs = ByteArray.empty`, `split` fails | index as a parameter, entry passes `0` (as `be32 xs 0`) |
| G4 | `Nat` `&&&`: no upper bound for `omega`, so `4 * (x &&& 2047) + p < 2^64` is unprovable | mask on `UInt8` bytes |
| G5 | `adlerGo` (two value-level `if` on `UInt32` plus `Nat` result): translation 18–20 s, exceeds default heartbeats, ends with a spurious `error: No goals to be solved` while still adding all theorems (`<` and `≥` forms alike); `maxHeartbeats 0` plus `#guard_msgs (error, drop info)` in the file. A mask version of the reduction (`x - ((0 - ((x+15) >>> 16)) &&& 65521)`) is not provable (bit-level goal) | as stated |
| G6 | with a `with` invariant the entry only knows `xs.size < 2^32`: an invariant like `b + (e - a) < 2^32` fails at entry | `< 2^40` |

## 5. Suggested order for eventually compiling inflate

1. X5 (lemma) and X1 (`%`/`/` by constant) in `Rep.lean`/`Op`-level expansion: verbatim Adler-32, `copyLoopGo`'s `k % distance`.
2. X2 + X3 + X4: tuple state/results and `Except`: verbatim `BitReader.readBits`, `decodeSym`, `takeBits`.
3. X6 + X8: word arrays and constant data: `Crc32.Native` table, `lengthBase`/`distBase`, packed decode tables.
4. X10 + X12 + X11: output block with length, readable while written, calls: `copyLoop`, `decodeStored`, then `goFused` (the
   symbol loop) is a tail-recursive function of 7 scalars + 2 tables + output.
5. Only then table building (`buildTableCanonicalFast`, X13) and the matchers (X13 + X14).
A cheap intermediate target that avoids building tables: inflate of fixed-Huffman and stored blocks only (tables are constants, X8).

## 6. Reproduce

```
elan toolchain Lean 4.29.0, ../deps/sail-riscv-lean at 51c635c (Testing/setup/box.sh), apt: qemu-system-misc gcc-riscv64-linux-gnu
lake build Riscv.Frontx.LeanZip          # after the Sail build, about a minute for the new file (adlerGo alone 18 s)
lake env lean Testing/asm/emit_leanzip.lean
for f in lzadler:71 lzreadbits:67 lzhuffsym:40 lzmatch04:111; do python3 Testing/asm/frontx_test.py check ${f##*:} ${f%%:*}; done
```

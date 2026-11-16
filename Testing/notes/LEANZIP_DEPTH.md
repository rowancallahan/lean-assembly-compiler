# lean-zip depth probe: what blocks a verbatim `inflate` (and gzip/zlib decode)

Branch `leanzip-depth`, compiler sources untouched. lean-zip @7e10583 (+ lean-zip-common @6b7d018), Lean 4.29.0.
Raw data in `Testing/leanzip-depth/`: `DecodeOrig.lean` (verbatim code, `file:line@rev` per block), `decode_first_failures.tsv`
(exact first message per node), `decode_callgraph.json`, `scripts/`.

## Method

* `DecodeOrig.lean`: all non-theorem items of the inflate / gzip-decode / zlib-decode modules plus the lemmas and defs they need, extracted
  mechanically (`scripts/extract.py`, `iter.py`, `drive.py`: add the item an `Unknown identifier` names, recompile). It compiles on 4.29 with
  no edit to any lean-zip line. Not lean-zip text: four 4.34 core lemmas (`dite_eq_left/right`, `ite_eq_left/right`, file header) that
  lean-zip proofs use; the compress items of `Gzip.lean` and `Wide.lean` items proved with `ByteArray.size_set` are left out.
* Call graph: constants used by each definition's value in the elaborated environment (matcher/proof auxiliaries, projections and core
  `ByteArray` functions removed; lean-zip's own `ByteArray.copyWithin…`, `extendWithin`, `fillDouble`, `uget/usetUInt64LE` kept).
* Per node: `frontx_compile f` on the unmodified function (one process each); first message recorded. `wa_compile` accepts only
  `ByteArray → scalar/Array Nat` entries, so for every inner node it says `expected a function of one ByteArray` (0-ary constants crash it with
  `_inhabitedExprDummy`); nothing is learned from it except for entries (see FOLD).
* Caveat: the translator stops at the first unsupported construct, and for most blocked nodes that is the signature. Bodies behind a rejected
  signature are untested, so every "unblocked" figure below is an upper bound.

Scope: `Zip.Native.Inflate.inflate` (InflateTreeFree.lean:633, the production decoder) reaches 76 nodes; with `GzipDecode.decompress`
(Gzip.lean:47) and `ZlibDecode.decompress` (Gzip.lean:181) 110 nodes. Inflate: 6 compile, 8 constants, 62 blocked. All decode: 10 compile, 11
constants, 89 blocked.

## 1. Blockers

direct = first failure is this feature; total = direct plus every caller of a direct node (a caller cannot be verbatim-compiled if a callee
cannot). Sorted by total, whole decode side.

| feature | inflate dir/tot | all decode dir/tot | example (verbatim) | first message |
|---|---|---|---|---|
| ARR: `Array Nat/UInt8/UInt16/UInt32` as parameter/result of an inner function | 18 / 33 | 21 / 43 | `countLengthsFast.go` Inflate.lean:536 | `unsupported result type Array Nat`, `unsupported parameter type Array Nat` |
| BAO: `ByteArray` result (output growth: `push`, `++`, `extract`, `set!`, `copyWithin`) | 5 / 13 | 11 / 28 | `copyLoopGo` Inflate.lean:710; `ByteArray.copyWithinAt` InflateFast.lean:84 | `unsupported result type ByteArray` |
| STR: structure with Array/USize fields as parameter or result (`DecodeTable`, `LongDecode`, `WideRefillState`) | 7 / 18 | 8 / 27 | `DecodeTable.entryAt` Inflate.lean:260 | `unsupported parameter type Zip.Native.HuffTree.DecodeTable` |
| EXC: `Except String β` result, `do`/`throw`/`←` | 11 / 14 | 18 / 23 | `BitReader.readBits` BitReader.lean:29 | `unsupported result type Except String (…)` |
| WF: recursion needing `from eq measure μ` | 5 / 11 | 8 / 19 | `goTreeFreeU` InflateTreeFree.lean:374; `goCurUW` InflateFast.lean:447 | `is not structurally recursive: give \`from eq measure μ\`` |
| BAF: `ByteArray` field inside a structure (`br.data.size`, `br.data[i]`) | 3 / 13 | 3 / 19 | `BitReader.readBit` BitReader.lean:17 | `could not prove … = if br.pos ≥ br.data.size then 1#64 else 0#64` (same with `requires br.bitOff < 8 ∧ br.pos < 2^32`) |
| TUP: tuple result holding arrays/structures | 6 / 13 | 6 / 18 | `buildSubLoop` InflateTreeFree.lean:118 | `unsupported result type Array UInt32 × Array UInt32` |
| MAT: `match` on two arguments with a Nat `succ` pattern | 1 / 13 | 1 / 18 | `bitReverse` Inflate.lean:390 | `unsupported match … n.succ, acc => bitReverse (x / 2) n (acc*2 + x%2)` |
| IND: user inductive `HuffTree` | 6 / 12 | 6 / 17 | `HuffTree.insert` Inflate.lean:53 | `unsupported result type Zip.Native.HuffTree` then `PANIC at Lean.Expr.appArg!` |
| USZ: `USize` parameter | 0 / 0 | 2 / 10 | `ByteArray.ugetUInt64LE` Wide.lean:65, `trimBitBufU` InflateFast.lean:442 | `unsupported parameter type USize` |
| INV: `Nat %` by a non-power-of-2 constant needs an author `requires`/`with` | 0 / 0 | 3 / 4 | `Adler32.Spec.updateByte` Spec/Adler32.lean:29 | `… is translated by one conditional subtraction and needs s.fst + byte.toNat < 131042 from the context` |
| FOLD: `Array.foldl` over `ByteArray.data` with a table | 0 / 0 | 2 / 3 | `Crc32.Native.updateBytes` Crc32.lean:17 | `unsupported term have index := … Crc32.Native.table.size …` (but see below) |

Hidden behind the first message, read off signatures (untested): PRFARG = proof arguments / `autoParam` / hypotheses in the signature, 12 nodes
(`copyLoop` Inflate.lean:738, `fillSlotsU` :414, `entryAtU` :279, `goTreeFreeU` InflateTreeFree.lean:374, `decodeHuffmanFastBufTables` :482,
`goCur` InflateFast.lean:159, `goCurUW`, `wideRefillU` :404, `ugetUInt64LE`, `usetUInt64LE`, `decodeHuffmanCurTablesU`, `copyLoopGo`).
`inflateLoopTreeFree`, `inflateLoopCurU` and `decodeDynamicLengthsOnly` first die in `simp` (maxRecDepth); with `set_option maxRecDepth 20000`
the first messages are WF, WF and `Except String (Array UInt8 × Array UInt8 × BitReader)` (EXC); classified so.

* Compile verbatim (10): `BitReader.alignToByte` BitReader.lean:39, `refill` Inflate.lean:1141, `takeBits` :1180, `unpackSym` :194, `unpackLen` :198,
  `packEntry` :190, `Crc32.Spec.crcBit`, `Adler32.Spec.pack`, `Adler32.Spec.unpack`, `GzipDecode.scanToZero` Gzip.lean:29.
* Constants (11): literal tables `fixedLitLengths` :668, `fixedDistLengths` :673, `lengthBase` :676, `lengthExtra` :682, `distBase` :691,
  `distExtra` :698, `codeLengthOrder` :749; scalars `fastBits` :144, `POLY`, `MOD_ADLER`, `presizeCap` (`frontx_compile` of a 0-ary constant fails with
  an internal `introN` error; callers read them as literals/hoisted tables). A probe entry `eLB xs := lengthBase[…]` reports `1 hoisted`
  but then fails at `Pg.wf` in my wrapper, so table constants are not established.
* FOLD is frontx-only: `WaLeanZip.lean` compiles `Crc32.Native.crc32` (`crc32E`) and `updateBytes` (`crcUpdateE`) through `wa_compile` behind
  `ByteArray → UInt32` wrappers, and `countLengthsFast` (node `HuffTree.countLengthsFast`) behind a `ByteArray → Array Nat` wrapper. So some ARR/FOLD
  bodies are within reach; what is missing is the calling convention (arrays across inner calls).
* `GzipDecode.decompress` and `ZlibDecode.decompress` die at their result type `Except String ByteArray`; their bodies (`for _ in [:1000]`,
  `let mut`, early `return`, `s!` in `throw`, `data[pos]` with `if hHdr :` proofs, `++`) are not reached.

## 2. Call tree of `inflate` (production, tree-free path)

✔ `frontx_compile` accepts verbatim · ◐ constant · ✘ X = first failure is feature X · `(+Y)` more features from the signature. A node
reached again is listed once (shared callees such as `readBits`, `fastBits`, `packEntry` appear at first occurrence).

```
- Inflate.inflate — ✘ EXC
  - Inflate.inflateRaw — ✘ EXC
    - Inflate.inflateLoopTreeFree — ✘ WF (+EXC)
      - Inflate.decodeHuffmanFastBufFixed — ✘ EXC
        - InflateBuf.decodeHuffmanFastBufTables — ✘ EXC (+PRFARG,STR)
          - InflateBuf.goTreeFree — ✘ WF (+EXC,STR)
            - HuffTree.decodeSymCanon — ✘ STR (+EXC)
              - HuffTree.subLookup — ✘ STR (+EXC)
                - HuffTree.DecodeTable.entryAt — ✘ STR
                - HuffTree.fastBits — ◐ scalar constant
                - HuffTree.unpackLen — ✔ compiles
                - HuffTree.unpackSym — ✔ compiles
            - Inflate.copyLoop — ✘ BAO (+PRFARG)
              - ByteArray.extendWithin — ✘ BAO
                - ByteArray.fillDouble — ✘ BAO
              - ByteArray.copyWithin — ✘ BAO
              - Inflate.copyLoopGo — ✘ BAO (+PRFARG)
            - HuffTree.DecodeTable.lenAt — ✘ STR
            - HuffTree.DecodeTable.symAt — ✘ STR
            - Inflate.distBase — ◐ literal table
            - Inflate.distExtra — ◐ literal table
            - Inflate.lengthBase — ◐ literal table
            - Inflate.lengthExtra — ◐ literal table
            - InflateBuf.takeBits — ✔ compiles
          - InflateBuf.goTreeFreeU — ✘ WF (+EXC,PRFARG,STR,USZ)
            - HuffTree.DecodeTable.entryAtU — ✘ STR (+PRFARG,USZ)
          - InflateBuf.refill — ✔ compiles
        - Inflate.fixedDistTF — ✘ TUP (+STR)
          - HuffTree.buildTreeFreeWithCount — ✘ TUP (+ARR,STR)
            - HuffTree.augmentSubTables — ✘ TUP (+ARR)
              - HuffTree.buildSubLoop — ✘ TUP (+ARR)
                - HuffTree.bitReverse — ✘ MAT
                - HuffTree.fillSlots — ✘ ARR
                - HuffTree.packEntry — ✔ compiles
              - HuffTree.countLongCodes — ✘ ARR
                - HuffTree.countLongCodes.go — ✘ ARR
              - HuffTree.nextCodesFast — ✘ ARR
                - HuffTree.nextCodesFast.go — ✘ ARR
            - HuffTree.buildTableCanonicalFastWithCount — ✘ STR (+ARR)
              - HuffTree.buildCanonicalLoop — ✘ ARR
                - HuffTree.fillSlotsU — ✘ ARR (+PRFARG)
            - HuffTree.hasLongCode — ✘ ARR
              - HuffTree.hasLongCode.go — ✘ ARR
          - Inflate.fixedDistCount — ✘ ARR
            - HuffTree.countLengthsFast — ✘ ARR
              - HuffTree.countLengthsFast.go — ✘ ARR
            - Inflate.fixedDistLengths — ◐ literal table
        - Inflate.fixedLitTF — ✘ TUP (+STR)
          - Inflate.fixedLitCount — ✘ ARR
            - Inflate.fixedLitLengths — ◐ literal table
      - InflateBuf.decodeHuffmanFastBufTreeFree — ✘ EXC (+ARR)
      - Inflate.decodeDynamicLengthsOnly — ✘ EXC (+ARR)
        - HuffTree.fromLengths — ✘ EXC (+ARR,IND)
          - HuffTree.fromLengthsTree — ✘ IND (+ARR)
            - HuffTree.insertLoop — ✘ IND (+ARR)
              - HuffTree.insert — ✘ IND
                - HuffTree.insert.go — ✘ IND
            - Huffman.Spec.nextCodes — ✘ ARR
              - Huffman.Spec.nextCodes.go — ✘ ARR
            - Huffman.Spec.countLengths — ✘ ARR
        - Inflate.decodeCLSymbols — ✘ WF (+ARR,EXC,IND)
          - HuffTree.decode — ✘ IND (+EXC)
            - HuffTree.decode.go — ✘ IND (+EXC)
              - ZipCommon.BitReader.readBit — ✘ BAF (+EXC)
          - ZipCommon.BitReader.readBits — ✘ EXC
            - ZipCommon.BitReader.readBits.go — ✘ BAF (+EXC)
          - Inflate.fillEntries — ✘ TUP (+ARR)
        - HuffTree.validateLengths — ✘ EXC (+ARR)
          - HuffTree.kraftSumFast — ✘ ARR
            - HuffTree.kraftSumFast.go — ✘ ARR
        - Inflate.readCLCodeLengths — ✘ WF (+ARR,EXC)
          - Inflate.codeLengthOrder — ◐ literal table
      - Inflate.decodeStored — ✘ EXC
        - ZipCommon.BitReader.readBytes — ✘ EXC (+BAF)
          - ZipCommon.BitReader.alignToByte — ✔ compiles
        - ZipCommon.BitReader.readUInt16LE — ✘ BAF (+EXC)
```

Added by gzip/zlib decode (`GzipDecode.decompress` calls `inflateRawSized` → fast path `inflateRawFastU` (falls back to `inflateRaw`), `crc32`;
`ZlibDecode.decompress` calls `inflateRaw`, `adler32`):

```
- GzipDecode.decompress — ✘ EXC
  - Inflate.inflateRawSized — ✘ EXC
    - Inflate.inflateRawFastU — ✘ EXC
      - InflateBuf.inflateLoopCurU — ✘ WF (+EXC)
        - InflateBuf.decodeHuffmanCurTablesU — ✘ EXC (+PRFARG,STR)
          - InflateBuf.goCurUW — ✘ WF (+EXC,PRFARG,STR,USZ)
            - InflateBuf.goCur — ✘ WF (+EXC,PRFARG,STR,USZ)
              - ByteArray.copyWithinAt — ✘ BAO
                - ByteArray.copyWithinAtGo — ✘ BAO
            - ByteArray.copyWithinAtShort — ✘ BAO (+USZ)
              - ByteArray.ugetUInt64LE — ✘ USZ (+PRFARG)
              - ByteArray.usetUInt64LE — ✘ BAO (+PRFARG,USZ)
            - ByteArray.copyWithinAtU — ✘ BAO (+USZ)
            - InflateBuf.wideRefillU — ✘ STR (+PRFARG,USZ)
            - InflateBuf.takeBitsU — ✘ EXC (+USZ)
            - InflateBuf.trimBitBufU — ✘ USZ
        - InflateBuf.decodeStoredCur — ✘ EXC
          - InflateBuf.storedCopyLoop — ✘ BAO
  - Crc32.Native.crc32 — ✘ FOLD
    - Crc32.Native.updateBytes — ✘ FOLD
      - Crc32.Native.table — ✘ ARR
        - Crc32.Spec.mkTable — ✘ ARR
          - Crc32.Spec.crcBit — ✔ compiles
            - Crc32.Spec.POLY — ◐ scalar constant
      - Crc32.Spec.crcByteTable — ✘ ARR
  - GzipDecode.presizeCap — ◐ scalar constant
  - GzipDecode.scanToZero — ✔ compiles
- ZlibDecode.decompress — ✘ EXC
  - Adler32.Native.adler32 — ✘ INV
    - Adler32.Native.updateBytes — ✘ INV
      - Adler32.Spec.updateByte — ✘ INV
        - Adler32.Spec.MOD_ADLER — ◐ scalar constant
    - Adler32.Spec.pack — ✔ compiles
    - Adler32.Spec.unpack — ✔ compiles
```

## 3. Smallest feature set that unblocks all of inflate

Every feature below is needed; none can be bypassed by choosing another path (`HuffTree` is used only for the code-length tree of dynamic
blocks, through `fromLengths`/`decode`, but that is on the production path). Greedy order: cumulative number of the 62 blocked inflate functions
whose every feature (first failure and signature) is then available.

| step | add | cumulative |
|---|---|---|
| 1 | ARR: arrays as parameters/results of inner functions | 17 |
| 2 | EXC: `Except String` results, `do`/`throw` | 25 |
| 3 | IND: `HuffTree` (3 constructors, `leaf` carries a `UInt16`) | 32 |
| 4 | STR: structures with array fields | 38 |
| 5 | TUP: tuples of arrays/structures | 44 |
| 6 | BAF: `ByteArray` field of `BitReader` | 48 |
| 7 | WF: `from … measure` for 5 loops (author-supplied measures) | 52 |
| 8 | BAO: `ByteArray` result growth (`copyLoop` reads its own output via `copyWithin`/`extendWithin`/`fillDouble`) | 55 |
| 9 | PRFARG: proof arguments / `autoParam` in signatures | 59 |
| 10 | USZ: `USize` (`entryAtU`, `goTreeFreeU`) | 61 |
| 11 | MAT: two-argument `match` on Nat (`bitReverse`) | 62 |

ARR + EXC alone give 25 functions but not `inflate` itself: every bit-reading decoder also needs BAF (13 functions transitively), and every
decoder loop needs WF/STR. Extra for gzip/zlib decode: the `Except`/`do`-with-`for` shape of the two entries, USZ + STR + BAO for the fast path
(`inflateRawFastU`; avoidable only by editing `decompress` to call `inflateRaw`), INV for Adler-32, and FOLD (or wa-style `ByteArray → UInt32` entries) for CRC-32.

## 4. Not reached: gzip/zlib compress

`GzipEncode.compress` (Gzip.lean:151), `ZlibEncode.compress` (:224) and `Deflate.deflateRaw` (Deflate*.lean, about 12k lines with `LZ77Token`,
`TokenArray`, proof-carrying arguments such as `hcl` in `deflateRawBaseP` DeflateDynamic.lean:3254) were **not compiled or tested**. The
extraction harness did not converge for them: the environment pulls about 45 `Zip.Spec`/`ZipForStd` modules and, with theorem proofs replaced by
`sorry`, the first round still has 43 errors, from 4.34-only core lemmas (`Array.size_set!`, `getElem!_set!_ne`/`_self`) and spec items
the by-name extraction does not find (`BuildTree`). Fixing that needs 4.29 shims or running on Lean 4.34 (the compiler is on 4.29). What can be said without
running: both entry points have the signature `ByteArray → UInt8 → ByteArray` with a `ByteArray` result, which is the BAO row of section 1, and
their bodies are `ByteArray.mk #[…] ++ deflated ++ trailer` around `Deflate.deflateRaw`. No blocker count is claimed for the compress side.

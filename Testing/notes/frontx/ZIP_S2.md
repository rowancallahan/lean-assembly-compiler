# lean-zip rows blocked by STR, TUP, EXC, INV, MAT (branch `zip-s2`)

Input: `Testing/notes/LEANZIP_TARGETS.md` (origin/leanzip-targets, lean-zip @ 7e10583), smallest first.
Source: github.com/kim-em/lean-zip @ 7e10583, copied VERBATIM (doc comments dropped), `file:line@7e10583` per block.
Code: `Riscv/Frontx/ZipS2.lean`. Setup: build cache restored from origin/build-cache (zstd), Lean 4.29.0 via elan,
`lake build Frontx` clean (320 jobs).

## Compiled and tested

| row | function | lines | file:line | path | test |
|---|---|---:|---|---|---|
| INV 1–3 | `Adler32.Native.adler32` (+ `updateBytes`, `Spec.updateByte`, `pack`, `unpack`) | 2–4 | Zip/Native/Adler32.lean:17, :13; Zip/Spec/Adler32.lean:29, :39, :47 | list (`frontx_compile`, `requires`/`with` as in PairExamples.lean) | `zip2_adler`: 50 cases ok (QEMU == Sail == Lean; lengths up to 2769; 107 words) |

- Axioms of `Proven.Frontx.ZipS2.adlerE`: `propext`, `Quot.sound`.
- The `requires`/`with` lines are the human input (same bounds as PairExamples.lean); the code is not changed.
- Word-array path (`wa_compile`) fails for this row: see below.

## Not compiled (first error)

| row | function | lines | file:line | path | first error |
|---|---|---:|---|---|---|
| MAT 1 | `Zip.Native.HuffTree.bitReverse` | 3 | Zip/Native/Inflate.lean:390 | wa (with invariant `n ≤ 8 ∧ x < 256 ∧ acc < 2 ^ (8 - n)`, measure `n`) | `wa_compile: unsupported term: Nat.casesOn x✝¹ ((fun acc => acc) x✝) fun n => …` |
| MAT 1 | same | | | wa (no invariant) | `wa_compile: loop 0 (Zip.Native.HuffTree.bitReverse) needs \`invariant … measure …\`` |
| MAT 1 | same | | | list | `frontx: unsupported match` (`match a✝¹, a✝ with \| 0, acc => acc \| n.succ, acc => …`) |
| TUP 1 | `Zip.Native.fillEntries` (`Array UInt8 × Nat` result) | 5 | Zip/Native/Inflate.lean:757 | list | `frontx: unsupported result type Array UInt8 × Nat` |
| TUP 1 | same, entry `fillIdxE` = `(fillEntries xs.data 0 3 256 …).2` | | | wa | `wa_compile: unsupported term: (Zip.Native.fillEntries (Array.replicate 256 0) 0 3 256 xs.data[0]!).snd` (the entry's projection; not reached the recursion) |
| EXC 1 + USZ | `Zip.Native.InflateBuf.takeBitsU` (`Except String (UInt16 × UInt64 × USize)`) | 6 | Zip/Native/InflateFast.lean:126 | list | `frontx: unsupported result type Except String (UInt16 × UInt64 × USize)` |
| EXC 1 | same | | | wa (entry `takeBitsE`) | `wa_compile: unsupported result type Except String (UInt16 × UInt64 × USize)` |
| INV, wa | `Adler32.Native.adler32` (for the word-array path) | 4 | Zip/Native/Adler32.lean:17 | wa | `wa_compile: unsupported let type Adler32.Spec.State` (the state is a `Nat × Nat` `let`) |
| EXC + STR 1 | `Zip.Native.HuffTree.decodeSymCanon` | 7 | Zip/Native/InflateTreeFree.lean:294 | — | **not attempted**: needs `LongDecode`, `subLookup` (`Except` of a 4-tuple); expect the `unsupported result type` error above |

Rows **already covered on main, not copied again**: STR 1–3 `DecodeTable.entryAt`, `lenAt`, `symAt`
(Zip/Native/Inflate.lean:260, :228, :234) are compiled on the word-array path in `Riscv/Frontx/WaStruct.lean`
(NOTES §32, tests `wa_entryat`, `wa_lenat`, `wa_symat`). `LEANZIP_TARGETS.md` lists them as still blocked; that is out of date.

## Notes

- Error texts are from the attempts before the failing blocks were removed from `ZipS2.lean` (the file now holds only the compiled Adler block), so `lake build Frontx` stays clean.
- The MAT, TUP and EXC rows fail on both paths. Each needs a translator feature (`match` on `Nat` with `succ`; tuple and `Except` results; `Except` on the word-array path), not a change to the lean-zip code.
- Test: `python3 Testing/asm/frontx_test.py check 50 zip2_adler`; `Testing/asm/ctest` deleted after the run.
- Words and cases: `Testing/asm/emit_zip2.lean` → `Testing/asm/frontx-words/zip2_adler.{words,cases}`.

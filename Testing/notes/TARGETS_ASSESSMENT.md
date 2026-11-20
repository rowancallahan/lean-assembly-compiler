# Targets assessment: con-leche, LeanZip, Lean SVG, Lean Align (SONNET-ASSESS-10)

Sources: the nine reports `Testing/notes/assess/{conleche-1..3,leanzip-1..2,leansvg-1..2,leanalign-1..2}.md` (branches `assess-01..09`, all present), plus `NANO_V2_IR.md`, `NANO_SUBSET.md`, `CONLECHE_TARGETS.md`.
All counts are the reports' grep counts (lines, not constructs, comments included): treat as ±20 %. Nothing was built or run by any assessor. "Not counted" means no report measured it.
Abbreviations: CL = con-leche, ZIP = LeanZip, SVG = Lean SVG, ALIGN = Lean Align.

What the nano v2 source language accepts today (from `NANO_V2_IR.md`): `UInt64`, `Buf`, `List UInt8` input, pairs/tuples, `let`, `if a == b / a < b`, `+ - * &&& ||| <<< >>>`, calls, fuel loops (`| 0 … | n+1 …`, tail self-calls only), prims `rd len put bnew bsize bget bset bpush`. Names are one letter + digits. No comments, `match`, structures, inductives, strings, `Nat`/`Int`, signed ops, division. Caps: 511 defs, 16,384 parser nodes, 1 MiB input, 1 GiB work memory, frame ≤ 250 words, `jal` range 1 MiB. (Lead correction: the 1,049,932 B figure is the old Nano.V2B `gen` route; the current self-hosted compiler B2 compiles self_S to 340,296 B, so self_S is NOT over the jal range today.)

## 1. Programs

**con-leche** (Lean 4 kernel re-implementation + soundness proof). Reads a `lean4export` NDJSON stream (or `.olean`) and prints one verdict line, exit code 0/1/2/3. Entry `Main.lean` → `Driver.runArgs` → `checkMainG`. 1,145 files / 308 k lines, but 93–95 % is proof (`Model/`, `Verify/`, `Semantics/`, `whitepaper/`). Executable part: Kernel + Cached + Frontend + Driver ≈ 41 k lines, ~1,970 defs, ~1,100 reachable from the checker roots. **Difficulty: hard.** It needs `Expr` (10 ctors, `letE` with 3 recursive fields), `Name`/`Level`, `Option`/`List`/`HashMap`, a `StateT`/`Except` monad stack, a 70-def mutual block with non-tail well-founded recursion (`CoreC.lean:444-2027`), and bignum `Nat` for kernel literals. The only near-subset part is the byte-level parser tier.

**LeanZip** (verified DEFLATE/zlib/gzip + CRC32/Adler32). Library, no CLI; entry points `GzipEncode.compress data level` (`Native/Gzip.lean:151`), `GzipDecode.decompress`, `Inflate.inflate`, `Deflate.deflateRaw`; `ByteArray` in, `ByteArray` or `Except String ByteArray` out. 99 files / 73.9 k lines; `Zip/Native` = 16,967 lines, 582 defs, the rest is proof. **Difficulty: medium** (hard if all 10 compression levels are kept). Almost all data is `ByteArray`/`Array UInt32`; loops are `termination_by` over input size; no HashMap/String logic/Float in the real path. Blockers: the 582-def count, `ZipCommon.BitReader` from another repo, 163 WF recursions, 3 mutual blocks, `Except`/`do`/`while`. A stored + fixed + one-inflate subset is ~150–200 defs.

**Lean SVG** (resvg-style SVG → PNG renderer). Entry `Main.lean:30` → pure `renderWithWarnings` (`Render.lean:1072`): XML → CSS → SVG tree → paths → rasteriser → filters/masks/text → PNG. 119 files / 35.3 k lines, no proofs about rendering (59 theorems, all about I/O shell and size bounds), no `partial`/`mutual`/`termination_by`, no Float. **Difficulty: hard** (size, not conceptual depth). ~1,750+ defs, 24 MB of embedded font data, 89 inductives+structures, `Int` fixed point (`Fx := Int`, clamped ±2^30), ~890 `for` loops, ~1,100 `do`. Loops are all `for … in [a:b]` or explicit fuel, which is the most compiler-friendly style of the four. A text-free core (Xml, Use, Svg shapes, Raster, Png encode) is est. 250–350 defs.

**Lean Align** (paired-end read aligner with end-to-end correctness proof). `Main.lean:21`: `build GENOME.fa INDEX` / `map INDEX R1.fq R2.fq OUT.sam MIN MAX`; reads a multi-GB index as one `ByteArray`. 306 files / 102.6 k lines, ~2/3 proof; ≈1,300 defs in part 1 (kernels, index) and ≈600 in the part-2 mapper. **Difficulty: hard as a whole program, easy for single kernels.** Kernels (banded/gapless scoring, `exFind`, CSR lookup, `MzWords`) are UInt64/ByteArray scalar loops with fuel-shaped recursion and no user inductives. The mapper layer is type-class-generic (`GRead`, `LookG`), uses closure-valued structure fields (`TierCfg`) and nested `Array (List (Array Nat))`.

## 2. Deduplicated feature table

Sorted by number of programs needing it, then by cost. Cost = compiler + proof cost for the cheapest encoding: S = days of front-end work, M = a week-scale feature with its own correctness lemma, L = new IR/runtime machinery or per-program rewrite with equivalence proofs.
"Core" = the program cannot run without it; "inc." = incidental, can be dropped or stubbed.

| feature | needed by | core / inc. | cheapest encoding in our subset | cost | notes |
|---|---|---|---|---|---|
| `Nat` as index/length/count (bounded) | CL ZIP SVG ALIGN | core | `UInt64` + `assert < 2^k` | S | Truncated `-` must stay saturating (ZIP `maxOutputSize - size`). Reports agree values never exceed ~2^35 except CL literals. |
| Fixed-width UInt8/16/32 (+USize) | CL ZIP SVG ALIGN | core | `UInt64` + mask after `+ * <<<` | S | Mask-after-every-op must be proven equal to the narrow semantics (ZIP: 648 UInt32 uses, ALIGN: 930). `USize` = UInt64. |
| `ByteArray` / `Buf` get/set/push/size/extract/`++` | CL ZIP SVG ALIGN | core | `Buf`, one byte per word; `extract`, `++` as copy loops | S | Prims exist. `extract`/`++`/`copySlice` need a library def each. 8× memory blow-up is fine for ≤ 1 MiB inputs. |
| Well-founded / counting loops (`termination_by`, `for … in [a:b]`, `while`) | CL ZIP SVG ALIGN | core | fuel loop, fuel = measure bound | M | Fuel bound needs a per-loop argument; `while` has none (ZIP 49, SVG ~53) so needs an explicit cap. Biggest mechanical cost in ZIP/ALIGN. |
| `Array α` of scalars | CL ZIP SVG ALIGN | core | `Buf` of words | S | Hash heads, CRC table, Huffman tables, pixel arrays (`Array Nat`, one packed RGBA word per pixel). |
| `Option α` | CL ZIP SVG ALIGN | core | `(flag, value)` pair or sentinel word | S | ZIP 20, SVG ~635, ALIGN ~1,550, CL ~530. |
| `structure` (flat) | CL ZIP SVG ALIGN | core | tuple, or `Buf` with fixed field offsets | M | ZIP 8, SVG 125, ALIGN 135 (many Prop-only), CL ~220. Frame ≤ 250 words limits tuples: `GW` has 16 fields, `TierOut` 10. Needs record syntax + field access + `{ s with … }`. |
| `inductive` enums (no payload) | CL ZIP SVG ALIGN | core | `UInt64` tag, `match` → `if` chain | S | Most SVG (`Cap`, `Join`, `CMKind`…), ZIP routes, ALIGN `Tag`/`Mate`. |
| `Except ε α` / `Option` as error channel | CL ZIP SVG ALIGN | core (ZIP, CL, SVG), inc. (ALIGN) | status word + out Buf; `.error msg` payload dropped | M | ZIP 68, CL ~200, SVG 37, ALIGN 8. Dropping the message changes the statement of the `.error` case: needs a bridge lemma. |
| `Int` (signed) | SVG ALIGN (CL ZIP: little) | core | two's-complement `UInt64`; need signed `<`, floor `/`, `>>` | M | SVG: `Fx := Int` everywhere, `Int.ediv`. ALIGN: scores, diagonals. New IR ops (`slt`, `sdiv`, `sar`) plus proofs. The subset has `<` unsigned only. |
| `List α` (executable) | CL ZIP SVG ALIGN | mostly inc. | `Buf` + count; cons cells in an arena if truly needed | M | ZIP production path uses `Array` twins; ALIGN mapper uses `flatMap`/`filterMap`/`mergeSort` on hit lists; CL has `List Expr`/`List Level` everywhere. |
| Comments, docstrings, attributes (`@[inline]`, `@[specialize]`, `@[csimp]`, `@[extern]`, `@[implemented_by]`), `namespace`/`open`/`private`/`section` | CL ZIP SVG ALIGN | inc. | lexer/parser skip; `extern`/`implemented_by` → compile the logical body | S | ZIP: comments ~26 % of Native lines, `@[inline]` 121; ALIGN `@[inline]` 429, `@[csimp]` 57. `namespace`/`open` not counted but certainly present in all four. |
| `a[i]!`, `a[i]'h`, `a[i]?`, `uget`/`get!` | ZIP SVG ALIGN CL | core | `bget` + assert (matches fail-fast) | S | ALIGN ~940 `[]!` + ~995 `get!`, ZIP 85. Index proof terms (`'h`) are erased. |
| `do` / `let mut` / `for` / `return` / `break` (`Id.run do`) | CL ZIP SVG ALIGN | core (SVG, ZIP), inc. (ALIGN part 1) | desugar to `let` + fuel loop with tuple state | L | Counts: SVG ~1,300 `do`, ~840 `for`; ZIP 89 `do`, 37 `let mut`, 21 `for`, 49 `while`; ALIGN ~100 `do`, ~60 loops; CL ~1,200 `do` (mostly monadic). Early exit and 10–20 mutable vars stress the frame limit. |
| `match` with patterns (Nat, Option, tuples, ctor) | CL ZIP SVG ALIGN | core | `if` chain on tag / `Nat` pattern → fuel arm | M | Not counted by any assessor, but all four use it (fuel recursion is `| 0 … | n+1`; SVG report says `match` "must be rewritten as `if` chains"). Already half-supported (fuel match). |
| Nested/tuple returns `(a, b, c)`, `let (a, b) := …` | CL ZIP SVG ALIGN | core | supported (PAIR/SPLIT) | S | Frame ≤ 250 words binds. `Except String (ByteArray × Nat)` is a nested one. |
| User `inductive` with payload / recursive | CL ZIP SVG | core (CL), core small (ZIP `HuffTree`, `LZ77Token`), core (SVG `Svg.Node`, `PathCmd`, `Paint`) | tagged cells in a `Buf` arena `[tag, f1..fn]`, node id = index | L | CL `Expr` 10 ctors; ZIP can avoid with packed tokens + flat tables; SVG recursion over `Svg.Node` needs an explicit stack. Needs `casesOn` encoding plus a heap-invariant proof. |
| General (non-tail, non-fuel) recursion | CL SVG (tree walks) | core | real `CALL` already in IR (KNOT); front end only accepts tail fuel loops | M | CL whnf/infer/defeq; SVG `Use.expand`, nested groups. ZIP/ALIGN do not need it. |
| `mutual` blocks | CL ZIP | CL core, ZIP inc. | single def with a `Nat` tag argument, or IR-level mutual calls | M | CL: one ~70-def block. ZIP: 3 blocks (lazy LZ77 matcher), mergeable. |
| `String` / `Char` literals and values | CL ZIP SVG ALIGN | inc. (ZIP, ALIGN, CL msgs), core (SVG names, CSS, XML; CL `Name.str`) | `Buf` of bytes; literal → generated byte-store prelude or interned id | M | SVG `startsWith bs i "<svg"`, CL hundreds of `Name.str … "Nat"`. Needs string-literal syntax and a bytes-compare helper. |
| Typeclasses / `instance` / `deriving` | CL SVG ALIGN (ZIP: implicit only) | ALIGN core for mapper, rest inc. | monomorphise by hand (ALIGN `GRead`/`LookG`: one instance each) | M per class, L if general | `deriving Repr/BEq/Inhabited` = ignore. CL `[Monad m]` + `CoreFns m` record of closures is the hard one. |
| Higher-order args, closures, `fun` | CL ALIGN (SVG small) | CL core, ALIGN mapper | specialise/defunctionalise at call site | M–L | ALIGN: 31 `Nat → Nat` args, `TierCfg` function fields (fix to production constants). |
| Monads: `StateT`/`StateM`, `Id.run` | CL (SVG, ZIP only `Id.run`) | CL core | explicit state tuple threading | L (CL) / S (`Id.run`) | `CheckCM := StateT CState (Except CheckError)`. |
| `HashMap` / `HashSet` | CL SVG ALIGN(bench/mapper 13) | CL perf-core, SVG inc. | open-addressing `Buf` or linear scan | M | CL memo is needed or whnf is exponential. SVG: 12 uses (id table, clip cache). |
| Bignum `Nat` (arbitrary size) | CL | core (accelerators), declinable | limb `Buf` library, or "decline" when over a bound | L | `natOpResult` add/sub/mul/pow/div/mod/gcd/land/lor/xor/shift up to 128 MiB. CL itself has a `declined` verdict, so a bounded version is sound-but-incomplete. |
| Integer `/`, `%`, `Nat.sqrt`, `log2`, `clz` | ZIP SVG ALIGN | core (small) | IR div/mod ops, or shift/sub loops; sqrt by fuel loop | S–M | ZIP `uint32_log2_clz`, SVG `Nat.sqrt`, `Int.ediv`. |
| `Float` | ZIP (`histEntropy`, 3 uses) | inc. | replace with integer approximation / fixed route | S | Changes compressed bytes of levels 3–5, not roundtrip. ALIGN benches only. |
| Recursion over structure-valued state with >16 fields | ZIP ALIGN SVG | core | state `Buf` | M | `lz77ChainLazy.mainLoop` 14 args; frame limit 250 words. |
| >511 defs / >16,384 nodes / >1 MiB code | CL ZIP SVG ALIGN | core | raise caps, modular compile, or compile a closure | L | See §5. |
| `IO` / `main` / argv / files | CL ZIP SVG ALIGN | inc. | byte-in/byte-out `m : List UInt8 → List UInt8` | S | Already the model. Loses CLI semantics; owner must accept the changed entry point. |
| `Task.spawn`, threads | CL SVG ALIGN | inc. | call sequentially (`(Task.spawn f).get = f ()`) | S | |
| Embedded data (SVG fonts 24–32 MB, Brotli dict 123 KB, ZIP `c/*.c`) | SVG (ZIP: C externs) | SVG core for text | pass as input bytes after the main input | M | Changes the program's contract; text rendering needs it, the rest of SVG does not. |
| Proof-carrying terms in defs (`if h : …`, `have … := by omega`, Prop fields, `decreasing_by`) | CL ZIP ALIGN | inc. (erased) | front end must erase `Decidable` proofs / Prop fields | M | See §4. |
| `@[computed_field]`, `unsafe`, `lean_is_exclusive_obj`, pointer equality | CL | inc. | drop; use a fixed mixer for `Expr.data` | M | CL `Expr.data` packs hash in a `UInt64`; check no theorem pins hash values (assessor marked uncertain). |
| Lean meta (`Lean.Expr`, `Environment`), `native_decide`, `bv_decide`, `Std.WP` | CL (PinGen), ZIP (CRC proofs) | proof/tooling only | not compiled | – | Excluded: build-time tools and proofs. |

### Syntax to add to the parser (lead's request)

Frequency = total grep lines over the four reports (indicative). "Programs" = how many of the four need it. Parser cost: S/M/L for lexer+parser+AST lowering, proof cost for the lowering lemma in brackets.

| rank | construct | programs | rough frequency | parser cost [proof cost] | note |
|---:|---|:-:|---|---|---|
| 1 | Comments `--`, `/- -/`, docstrings; `namespace`/`open`/`section`/`end`/`private`; `@[...]` attributes (skip) | 4 | ZIP 26 % of lines; ALIGN `@[inline]` 429, ZIP 121 | S [none: erased before lexing] | Zero semantic content; every real file has them. Do this first so real source can be fed unchanged. |
| 2 | `match` on `Nat`/`Bool`/`Option`/tuple/enum with patterns | 4 | not counted; every fuel recursion uses it | M [M] | Lower to `if` chain / fuel `LOOP` arms. Fuel arm is the only form accepted today. |
| 3 | Index notation `a[i]!`, `a[i]'h`, `a[i]?`, `a[i]` and `a.size`/`a.push`/`a.set!` | 4 | ALIGN ~940, ZIP 85, SVG/CL not counted (hundreds) | S [S] | Lower to `bget`/`bset`/`bpush`/`bsize` with assert. |
| 4 | `structure` decl, field access `s.f`, `{ s with f := v }`, anonymous ctor `⟨a, b⟩` | 4 | SVG 125, ALIGN 135, CL ~220, ZIP 8 | M [M] | Lower to tuples/fixed offsets; drop Prop fields. |
| 5 | `do` blocks with `let mut`, `for i in [a:b]`, `while`, `return`, `break`, `Id.run` | 4 | SVG ~1,300 `do`/~840 `for`; ZIP 89/21/49; ALIGN ~100 | L [L] | Biggest single multiplier for SVG and ZIP; every loop becomes fuel loop with tuple state; early exit. Do after 2–4. |
| 6 | `inductive` enums (no payload) + `deriving` skip | 4 | SVG ~20, ALIGN ~10, ZIP ~5 | S [S] | Tags as `UInt64` constants; makes `match` on enums work. |
| 7 | Numeric type sugar: `UInt32`/`UInt16`/`UInt8`/`USize` literals and `.toUInt64`/`.toNat`/`.toUInt32` conversions | 4 | UInt32 ZIP 648, ALIGN 930; USize ALIGN 665 | M [M] | Mask-after-op lowering. Not syntax proper but needed to parse real code. |
| 8 | `Option`/`Except` ctors and combinators: `some`/`none`/`.ok`/`.error`/`throw`/`<|>`/`if let`/`match … with | some x`; `←` bind in `do` | 4 | Option ~3,000 total; Except ~300 | M [M] | Needs status-word convention. Pair with `do`. |
| 9 | `where` clauses and local `let rec`; local `fun`; named `termination_by`/`decreasing_by` (parse and skip) | ZIP ALIGN CL (SVG: fuel) | `termination_by` ZIP 300, CL ~270, ALIGN 220; `where` not counted | S [S] for skip; M for `where` hoisting | `termination_by`/`decreasing_by` are skipped, but then fuel must come from somewhere (§4). |
| 10 | String/char literals, `s!` | CL SVG ZIP ALIGN | CL hundreds, SVG tens | M [S] | Byte-store prelude. |
| 11 | `inductive` with payload, `structure` recursion | CL SVG ZIP | CL ~220, SVG 53 | L [L] | Defer: needs arena + `casesOn` proof. |
| 12 | `class`/`instance`/`deriving`, `fun`, higher-order args, `mutual` | CL ALIGN SVG | ALIGN 19, CL ~40 | L | Defer; do by hand rewrite for ALIGN. |

**Proposed first 8 syntax additions** (ranked by programs × frequency vs cost): (1) comments/namespace/open/attributes skip, (2) `match` with patterns, (3) `a[i]!`/`a.size`/`a.push` index and Array API, (4) `structure` with field access and `with`, (5) enum `inductive`, (6) fixed-width UInt32/16/8 + conversions, (7) `do` with `let mut`/`for`/`return`/`break`, (8) `Option`/`Except` ctors with `←`. Items 1–6 are S–M and do not need new IR; item 7 is the large one but multiplies the most lines; item 8 needs the status-word convention agreed first.

## 3. Suggested feature order and which program compiles first

Order, with what each step unlocks:

1. **Comments/namespace/attributes skip** + **UInt32/16/8 masking** + **index/Array API** (S). Unlocks verbatim *leaf* functions: ZIP `Crc32`, `Adler32` (3 defs each), ALIGN `getU32`, `exFind`, `u32`, `letter`, SVG `Bytes.lean` byte predicates, CL `bvarOfData`/`fvarOfData`/`lpOfData`.
2. **`match` + enum inductives + flat `structure`** (M). Unlocks ZIP `BitWriter` (21 defs), ALIGN `CsrIndex`/`MapperMzWords`/band kernels, SVG `Fixed`-free numeric kernels.
3. **`do`/`let mut`/`for`/`while` desugaring with fuel** (L) and **`Option`/`Except` as status words** (M). Unlocks ZIP stored/fixed/inflate path, SVG `Inflate`, `Png`, `Xml`, `Bytes`, CL byte-level NDJSON parser.
4. **Signed `Int` ops** (M). Unlocks SVG `Fixed`/`Raster`/`Canvas` and ALIGN diagonal/score kernels.
5. **Raise caps** (defs, nodes, code size/jal range) (L). Needed by every whole-program target.
6. **Tagged-payload inductives, non-tail recursion, `mutual`** (L). Unlocks SVG tree walks and CL `Expr` core.
7. **Typeclass/closure monomorphisation, HashMap, strings, bignum** (L). Only CL and the ALIGN mapper need these.

**First to compile:** LeanZip, as a *subset*: Crc32 + Adler32 (≤ 10 defs, step 1), then stored gzip encode/decode, then raw inflate with fixed+dynamic tables (est. 60–200 defs, ends at step 3). It needs no inductives, no Int, no HashMap, no String logic, only `Nat → UInt64`, UInt32 masks, `ByteArray`, `Except`, and WF-loops → fuel. Second: Lean Align single kernels (gapless/banded score, `exFind`); third: Lean SVG Inflate/Png-encode/Xml pieces. No program compiles whole in any foreseeable order: ZIP whole-library needs the cap raise (582 defs), SVG ≥ 1,750 defs, ALIGN ≥ 1,500, CL ≥ 1,100 defs plus bignum/inductives.

## 4. Proofs: do we need to compile their tactics?

**No.** Our compiler consumes definitions only. Theorems and tactic blocks (`simp`, `omega`, `bv_decide`, `grind`, `decide`, `native_decide`) run in Lean at elaboration time, produce proof terms, and are never code. Our correctness theorem says the emitted binary computes the same Lean function `f` the front end read. So any existing theorem *about that same `f`* (e.g. `inflate_ok_iff_decodesTo`, `alignPairs_correct`) applies to the binary with no new proof, provided we compile `f` unchanged.

The real cost is any **rewrite** of their code into our subset (`Nat → UInt64`, `Except String` → status word, `List`/`structure` → Buf, WF recursion → fuel, `Int` → two's complement). Each rewritten function `f'` needs `f' = f` under range hypotheses; their existing bridge lemmas (`ldwU_eq`, `u32W_eq`, `exFind_eq_exFindF`, `Fits g`, `hk : k.toNat < 2^30`) are reusable for this.

Per program:

- **con-leche.** 93–95 % proof (`Model/`, `Verify/`, `whitepaper/`) is never compiled. Top theorems `model_exists`, `no_False_declaration`, `Cached.checkDecls_sound`, `runArgs_accept` are about `checkDecls` over `Nat`/`List`/`HashMap`/WF recursion/`StateT`. They transfer only if we compile those defs *verbatim*, which needs inductives, monads, mutual non-tail recursion, bignum: not available. A hand-stripped checker (no strings, bounded Nat, explicit stack) is a rewrite and would need a refinement proof to `checkDecls`: very large. Realistically: compile the byte-level parsers verbatim and keep the soundness story only for them.
- **LeanZip.** Strong theorems (`inflate_deflateRaw`, `gzip_decompressSingle_compress`, `inflate_ok_iff_decodesTo`, `crc32_append`). Defs that depend on tactic-produced terms: 163 `termination_by` + 110 `decreasing_by` in Native (WF recursion compiles through `WellFounded.fix`, which our front end must unfold or replace by fuel), `if h : i < a.size then a[i]'h`, `have hmaxLenP : … := by omega` in bodies, `TokenArray.aligned` (Prop field), `bv_decide` in `Crc32`. Mitigation: verbatim copies with erased proofs and fuel ≥ measure are mechanical; the `Except String` → status word change alters the `.error` case. CRC32/Adler32 and stored/fixed paths are the cheapest places to prove `f' = f`.
- **Lean SVG.** No correctness theorems about rendering; the 59 theorems are about I/O shell and size bounds (`renderWithWarnings_size_le`, `*_local`, `use_maxDepth_le`). Nothing worth inheriting except size bounds as memory specs. No `termination_by`/`partial`/`decreasing_by` (loops are `for` or fuel), so almost no tactic-dependent defs: the lowest proof-side risk of the four. The cost is all rewrite equivalence (`Int` → UInt64 bound analysis, `String` → Buf).
- **Lean Align.** Heaviest proof layer (`alignPairs_correct`, `process_correct`, `wfaAlign_sound`, `hitsC_sound`). Defs that depend on tactic terms: 96 (part 1) + 126 (part 2) `termination_by`, `@[csimp]` pairs (57; compile the fast def, the spec def is irrelevant at runtime), `Prop` structure fields (`Fits`, bounds), `a[i]'h`, `decide +kernel` ×4. Their own pattern "fast def + equality theorem + csimp" is exactly what we need: write nano-subset defs, prove equal to the fast def, reuse the top theorem. `alignPairs`/`buildIndex` in `Spec/Aligner.lean` are `sorry` holes by design (17 `sorry` in `Spec/`).

What the front end must therefore handle (not tactics, but tactic-built terms inside def bodies): WF recursion via `termination_by` (ZIP 273, CL ~270, ALIGN 222); `dite` with proof (`if h :`) and `a[i]'h`; subtype/Prop-carrying structure fields; `@[csimp]`/`@[implemented_by]` twin selection (logical body, not the fast unverified twin); `decide`-produced instances in def bodies (CL `Decidable ValidLengths`, `Std` instances). None run tactics; they must be erased or unfolded.

## 5. Limits: programs vs our caps

Our caps: 511 defs, 16,384 parser nodes (`d3` capacity, self_S uses 10,859), input 1 MiB, work memory 1 GiB (4 `bnew`), frame ≤ 250 words, code ≤ 1 MiB (`jal` range; self_S is 340,296 B with B2 — the 1,049,932 B figure was the old `gen` route).

| | defs (whole executable) | defs (realistic first slice) | parser nodes | input | output | memory |
|---|---|---|---|---|---|---|
| **CL** | ~1,970 executable, ~1,100 reachable (2–4× cap) | 150–300 (stripped checker, guess) | Kernel/Core closure 22 k source lines → est. ≥ 100 k nodes (≈6× cap; estimate) | real: tens of MB (Init) to GB (Mathlib); only the 614 test fixtures (35 MB total, each small) fit 1 MiB | 1 line | 1 GiB enough for ≤ 1 MiB inputs; Nat literals up to 128 MiB if not declined |
| **ZIP** | 582 in `Native` (1.14× cap), +`Zip.lean`, vendored `ZipCommon` (few hundred lines, unknown) | Crc32/Adler32 ≤ 10; inflate+stored+fixed ≈ 150–200; inflate only ≈ 60–80 | `Inflate.lean` 1,643 lines probably over after expansion (estimate, unmeasured); `DeflateDynamic` 4,081 lines certainly over | any (gzip ≤ 1 GiB `maxOutputSize`); tests ≤ 1 MiB OK | up to `maxOutputSize`; 8 B/byte as Buf | LZ77 tables ≈ 0.5 MiB; fine |
| **SVG** | ≥ 1,750 (slices ~1,021 + ~726; part 2 says whole repo > 1,500, part 1 says 2,000+) | 250–350 (no fonts/filters/JPEG/GIF/Woff) | `Svg.lean` 5,050 lines, `Filter` 1,144, `Font` 1,154 each plausibly 10 k+ nodes (estimate) | nominal 64 MiB; test SVGs ≪ 1 MiB OK; fonts 24–32 MB cannot be inlined | PNG stored deflate ≈ raw RGBA; e.g. 800×600 = 3.8 MB as Buf words | canvas up to 16.7 M px (67 MB RGBA, layers up to 268 MB); fine at small widths; fuel up to 10^7–10^8 iterations per pixel loop |
| **ALIGN** | ≈1,293 (part 1) + ≈600 (mapper) + index/kernels; whole path est. 1,500–2,500 | single kernel: a few dozen defs | `TierRouter.lean` alone 2,001 lines; whole path certainly over | real: multi-GB index, GB FASTQ; 8 MiB FASTQ chunk > 1 MiB cap; only micro tests (tiny genome, few reads) | SAM ≈ 300–500 B/pair | hg38 index ≫ 1 GiB; toy genome (chr21 ≈ 12 MB 2-bit) plausible |

Cap-related fixes, ranked by how many programs they unblock: (a) defs cap 511 → ≥ 2,500 (all four); (b) node cap 16,384 → ≥ 100 k (all four; self_S already needs κ ≥ 2^19 and 10,859 of 16,384 nodes); (c) code size > 1 MiB: long-jump encoding (`auipc`+`jalr`) or range-checked `gen` (all four whole programs; self_S itself is at 340 KB, not over); (d) input cap 1 MiB (CL, ALIGN real data, SVG fonts; not for tests); (e) frame ≤ 250 words (ZIP matcher state, ALIGN `GW`/`TierOut`, SVG rasteriser `let mut` sets).

## 6. Open questions and evidence quality

- Counts of `match`, `where`, `let rec`, `fun`, `if let`, `#[…]`, `namespace`/`open` were **not measured** by any assessor; ranks for those rows rest on the reports' descriptions, not counts. A single `grep -c` pass per repo would settle them before parser work starts.
- No assessor built any repo; parser-node and frame sizes are estimates. Measuring the node count of `Inflate.lean` after stripping comments is the cheapest next datum for ZIP.
- Part boundaries overlapped by one straddling file in each split; totals are ±1 file.
- CL hash assumption (`Expr.data` mixer replaceable): marked uncertain by assess-01.
- Disagreement: SVG whole-repo def count (assess-06 "2,000+", assess-07 "> 1,500"); the table above uses ≥ 1,750 (sum of slice greps).

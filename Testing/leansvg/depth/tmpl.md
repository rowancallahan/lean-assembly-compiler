# lean-svg depth probe: `render` call graph vs the front ends

Branch `leansvg-depth` (from `leansvg-verbatim`; no compiler source touched). Source: `rowancallahan/lean-svg` @ `df8e663`.

**Method.** lean-svg was built under Lean 4.29 (the compiler's toolchain) in a scratch copy with 3 edits for the 4.34→4.29 gap: a `Nat.sqrt` placeholder shim (Fixed.lean:47 `hypot` calls it; core has it only in 4.34, so `hypot` was not meaningfully tested), Css.lean:213 (`let (a, b) : T ← …` rewritten as two lets), Shape.lean:239 (`for tag in (… : Array Nat)` ascription). No other body was edited.
The call graph is **type-checked**: constants used by each elaborated definition, aux definitions folded into their parent, root `LeanSvg.render`.
`frontx_compile LeanSvg.<f>` was run on the imported definition itself (verbatim by construction), one attempt per function, `maxHeartbeats 300000`, `--tstack=4000000`.
Scripts and raw results: `Testing/leansvg/depth/` (`Graph.lean`, `ana.py`, `mk.py`, `gen.py`, `res.json`, `graph.tsv`).

**Numbers.** `render` reaches 3 466 constants; 2 598 are functions; **@@NREAL@@ are user definitions** (the rest are generated matchers/recursors). **@@NOK@@ compile**, all leaves: @@OKL@@.
All others are blocked (or no verdict, see §4). Only the **first** failure per function is recorded (the front end stops there), so a function's first failure is usually its signature and hides later blockers. "Transitive" = functions whose callee closure contains a function with that first failure.
Only `frontx_compile` was tried: `wa_compile` is not on this branch and `frontx_ind` needs a hand-declared `frontx_ind_type` per structure. The `ByteArray`/`Array`/structure rows are exactly what those two target, so they are not attempted here, not hopeless.

## 1. Blocker table (sorted by transitive impact)

| feature (first-failure class) | blocked directly | blocked transitively | example (file:line — message) |
|---|---|---|---|
@@ROWS@@

## 2. Call tree of `render` (stage level; "defs below" counts include accessors)

@@TREE@@

The big stages (`render`, `renderWithWarnings`, `Xml.parse`, `interpretWith`, `renderRgba`, `renderNodes`) hit the front end's own limits (simp steps, whnf heartbeats, memory) before a feature message. Their blockers are in their signatures: structure parameters (`Options`, `Svg.Doc`, `Mat`), `Array` of structures, `Except String` of tuples/structures.

## 3. Smallest feature set to compile `render` end to end

The first-failure classes in `render`'s closure number @@NNEED@@ (§1, every row with a non-zero transitive count). Greedy order by functions newly unlocked (first-failure data only, so a lower bound):

@@GREEDY@@

Needed beyond first failures, read from deeper messages: `Nat` `>>>`, variable×variable `*` and `/` by variables (`Canvas.premul/unpremul/blendLerp`, `PngDecode.to8/passLen`, `Lighting.*`), `"…".toUTF8` literals (`Bytes.findSeq`, `Svg.paintOrderKindOf`), `Shape.M` (StateM-like), closures (`Bytes.skipWhile`).
Verdict: not one or two features. Three structural gates: (a) user structures/inductives as values with `Int`/`Fx` fields, (b) `Array`/`ByteArray` results, (c) `Int` arithmetic. The Svg element tree plus `interpretWith` (~1 700 defs below) is the larger half. The nearest end-to-end subtree is the PNG encoder (`Png.encode` → `zlibStoredRows`, `crc32Range`, `zlibLen`), blocked by `ByteArray` results, var×var `*` and the `crcRun4` shape.

**Floats.** No `Float` type in the code (the only occurrence is a comment, Oklab.lean:13). Floating point is a software binary32 on `Nat` (`abbrev F32 := Nat`, Canvas.lean:343; ~40 reachable `F32.*`, plus `Lighting.*`, `Filter.f32*`, Oklab). It is integer-only but needs `>>>`, var×var `*`, `/` by variables, `have` bindings and a `bitLen` loop. **Flag:** if "floats out of scope" includes this soft-float, its users (filters, lighting, gradients, Oklab) are excluded. Fixed-point `Fx := Int` (Fixed.lean:16) carries the geometry.

## 4. Caveats
- Some functions have no verdict: the front end was killed for memory (15 chunks exited 137 and were re-run singly) and a few runs were lost when a background watcher ended. These count as blocked/"resource".
- A function is counted blocked even when only a callee blocks it; `frontx_compile` does not report the callee chain.
- Classes come from regexes over message text; rare messages remain as "other: …" rows.

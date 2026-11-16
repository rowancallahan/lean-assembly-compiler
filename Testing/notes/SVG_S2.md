# SVG_S2: lean-svg rows blocked by structures and Int/Fx

Source: `github.com/rowancallahan/lean-svg` @ `df8e663`, rows of `LEANSVG_TARGETS.md` (`origin/leansvg-targets`,
§1.1 structure ctor / projection, §1.5). Code: `Riscv/Frontx/SvgS2.lean` (verbatim, `-- file:line@df8e663` per block,
doc comments dropped, lean-svg not edited). Tests: `Testing/asm/emit_svg_s2.lean` → `Testing/asm/frontx-words/svg_*`,
run with `python3 Testing/asm/frontx_test.py check 50 <name>`. `lake build Frontx` is clean. Axioms of the compiled
functions: `propext, Classical.choice, Quot.sound` only.

Scope: a first batch of about 16 rows (smallest first), not the whole §1 list. Rows not listed below were not attempted.

## Compiled (`frontx_compile` on the library definition)

| function | file:line | notes |
|---|---|---|
| `Pt.mk`, `Pt.x`, `Pt.y` | Geom.lean:12 | `Fx` = `Int` fields |
| `Pt.neg` | Geom.lean:20 | |
| `Pt.add` | Geom.lean:18 | `requires` the sums in `[-2^63, 2^63)` |
| `Pt.sub` | Geom.lean:19 | `requires` the differences in range |
| `Mat.mk`, `Mat.a`, `Mat.e` | Geom.lean:61 | `Int` and `Fx` fields |
| `Box.mk`, `Box.x1` | Geom.lean:332 | |
| `Metrics.mk`, `Metrics.cap`, `Metrics.upem` | Units.lean:40 | `Nat` and `Int` fields |
| `Mat.clampLin` | Geom.lean:74 | uses `Mat.linMax` (Geom.lean:73, verbatim, not compiled alone) |
| `Box.meets` | Geom.lean:349 | compiles; its test entry fails (below) |

## Tests (QEMU == Sail == Lean, 50 cases each, all ok)

| name | entry | result | words |
|---|---|---|---|
| `svg_ptneg` | `Pt.neg` (of input) | `Pt`, bytes | 316 |
| `svg_ptaddx` | `(Pt.add p q).x` | `Int` | 295 |
| `svg_ptaddy` | `(Pt.add p q).y` | `Int` | 304 |
| `svg_ptsubx` | `(Pt.sub p q).x` | `Int` | 295 |
| `svg_mata` | `Mat.a` of input | `Int` | 115 |
| `svg_mate` | `Mat.e` of input | `Int` | 117 |
| `svg_boxx1` | `Box.x1` of input | `Int` | 117 |
| `svg_metricscap` | `Metrics.cap` of input | `Int` | 117 |
| `svg_metricsupem` | `Metrics.upem` of input | `Nat` | 59 |
| `svg_clamplin` | `Mat.clampLin` of input | `Int` | 124 |

Entry glue (in `SvgS2.lean`, not lean-svg code) reads signed 32-bit words or bytes of the input. The `Pt.add` and
`Pt.sub` entries return one coordinate: a whole-`Pt` entry failed (below).

## Failures (first error)

- `Box.meets` entry, glue with eight input-derived arguments: `Tactic simp failed with a nested error: (deterministic)
  timeout at whnf, maximum number of heartbeats (200000)`. With four constant arguments: `frontx: could not prove`
  on the glue (`meetsAt`). Library compile itself is fine. Entry dropped.
- `Pt.add` as `frontx_compile` without `requires`: `Tactic rfl failed: BExp.denote (σ.env.set 9 (rI x✝)) … is not
  definitionally equal to rI (if x✝ > Fx.maxVal then …)`. Fixed by the `requires` range hypothesis.
- `Pt.add` / `Pt.sub` whole-`Pt` entry (`frontx_implements_bytes`): `Tactic decide failed for proposition
  BStmt.wf slots [0, 3] prog … did not reduce to isTrue or isFalse`, also with `maxRecDepth 20000`. Entry replaced by
  the coordinate entries above.

## Hypotheses to note

- `Pt.add`, `Pt.sub` have `requires` (sum / difference of coordinates in `[-2^63, 2^63)`); the entry glue only feeds
  32-bit words, so the hypothesis holds on all tests but is not discharged by the library itself.
- `Mat.clampLin`, `Box.meets` have `requires` as in `IntExamples.lean` (operands of `<`, `≤`, `/` in range).

## Not done

Rows of §1.1 with payloads of `Option`, `Array` or `String` fields (`Poly`, `Xml.Attr`, `Viewport.AspectRatio`), the
inductive constructors (`PathCmd.*`, needs the Ind path), `Pt.dist` (needs `Fx.hypot`), and the other §1.2–§1.5 rows.

# LEAN_DIFF: standing differential campaign, nano vs real Lean 4.34.1 (branch lean-diff)

Generated 2026-11-21 06:25Z. Harness: `Testing/nano/v2self/fuzz/lean_diff/` (UNPROVEN glue). Oracle: `lean` 4.34.1 on `import Nano.Main.Prelude` + program + `#eval m input`; nano = B2.bin via nanorun (RV) and GA_arm.bin under qemu-aarch64 (sampled). Classes M1–M14: `LEAN_RULES.md` §0; `cls` is an auto-classification of the *minimized* program (heuristic; `NEW?` = needs manual triage).

## cur
```
cur iters=3 seed=2003 t=190s {"x": 311, "same": 120, "NANO-ACCEPTS-LEAN-REJECTS": 19, "cls:M12": 15, "cls:M9": 2, "cls:M9/M10": 2}
```
distinct minimized divergences by class: {"M12": 33, "M9/M10": 6, "M9": 5}

* **M12** (NANO-ACCEPTS-LEAN-REJECTS): `'def m (x : List UInt8) : List UInt8\n    := put [] ((320 <<< 1) &&& rd x 1 &&& 256)'` input `00020203` nano `ACCEPT out=00` lean `REJECT /tmp/tmpa039frl5/p.lean:3:15: error(lean.synthInstanceFailed): failed `
* **M9/M10** (NANO-ACCEPTS-LEAN-REJECTS): `'def m (x : List UInt8) : List UInt8\n  := put [] ((let v0\n    := rd x 0; 257))'` input `7fff03ffff00` nano `ACCEPT out=01` lean `REJECT expected ';' or line break`
* **M9** (NANO-ACCEPTS-LEAN-REJECTS): `'def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n | 0, x, i, a\n  => a\n| n + 1, x, i, a\n=> f n x (1) ((255) ||| rd x 4)\ndef m (x : List UInt8) : List UInt8 := put [] (f 0 x 0 36893488147419103232)'` input `016161017fa1ff` nano `ACCEPT out=00` lean `REJECT Missing cases:`

## syn
```
syn iters=1 seed=6001 t=167s {"x": 84, "same": 45, "NANO-ACCEPTS-LEAN-REJECTS": 17, "cls:M9/M10": 6, "ARM-DIFF": 4, "cls:ARM": 4, "cls:M11": 1, "cls:M12": 7, "cls:M5": 1, "cls:M9": 1, "cls:M4": 1}
```
distinct minimized divergences by class: {"M12": 1, "M5": 1}

* **M12** (NANO-ACCEPTS-LEAN-REJECTS): `'def m (x : List UInt8) : List UInt8 := put [] (if 63 < ((100000000000000000000 >>> 130) * (rd x 0 ||| rd x 3)) then 1 else 2)'` input `7f7f617f8a0d61` nano `ACCEPT out=01` lean `REJECT /tmp/tmpiuugqx5l/p.lean:2:56: error(lean.synthInstanceFailed): failed `
* **M5** (NANO-ACCEPTS-LEAN-REJECTS): `'namespace A\n@[inline] def m (x : List UInt8) : List UInt8 := put [] (rd x 5)\nend B'` input `61016180808001` nano `ACCEPT out=80` lean `REJECT Invalid name after `end`: Expected `A`, but found `B``


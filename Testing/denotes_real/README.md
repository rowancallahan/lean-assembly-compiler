# DENOTES-3 acceptance runs (real con-leche @3b37939, Lean 4.35.0-rc3)
* `TinyExp.lean`: program `f x = x + 1` + the theorems the bridge reads (f_eq, f_body, add_one, outParam_eq).
* `tiny.ndjson`: `lean4export TinyExp -- f f_eq f_body add_one outParam_eq` (lean4export v4.35.0-rc3).
* `con-leche tiny.ndjson` → `accepted 27 declarations (--verified)`.
* `CheckTiny.lean` (run from `bridge/` with `lake env lean ../Testing/denotes_real/CheckTiny.lean`):
  every record `Real.Tiny.tiny_model` / `Real.AddOne.addOne_model` assume is in the parsed stream EXACTLY
  (kind, name, level params, declared type); `Cached.checkDecls .verified natOpPinSets (preparePrelude ..)` = ok;
  `natLitSupported env = true`.  These are `#eval` checks, not kernel proofs.

# mixHash and the con-leche computed hash fields

Pins: con-leche `6810492c1` (`lean-toolchain` = `leanprover/lean4:v4.35.0`, `con-leche/lean-toolchain`); Lean core tag `v4.35.0` (commit `eb6cafb7`). Lean `master` (`9ecf584d`) has the same `mixHash` and C body. Paths below are relative to those trees.

## 1. `mixHash` in Lean core

| Fact | Evidence |
|---|---|
| Declared as `opaque` with an extern attribute; no body, no `implemented_by`. | `src/Init/Prelude.lean:4820-4821`: `@[extern "lean_uint64_mix_hash"]` / `opaque mixHash (u₁ u₂ : UInt64) : UInt64` |
| Docstring: block step of MurmurHash64A, except the second `k *= m` is `k ^= m`. | `src/Init/Prelude.lean:4819` |
| No Lean-level definition or reference implementation exists in core. Uses are all calls. | `src/Init/Data/Hashable.lean:19,35,38,41,74`; `src/Init/Prelude.lean:4916-4917` |
| C body (what the compiled code runs): `m = 0xc6a4a7935bd1e995`, `r = 47`; `k *= m; k ^= k >> r; k ^= m; h ^= k; h *= m; return h;`, all `uint64_t` (wrapping). | `src/include/lean/lean.h:2293-2302` |
| Same C body in `master`. | `lean.h:2396-2405` of `9ecf584d` |
| C++ wrapper that calls it. | `src/runtime/hash.h:17` |

Related but separate: `mixHash32` (`Prelude.lean`, extern `lean_uint32_mix_hash`). con-leche does not use it (grep: no hits).

Other externs con-leche's hashes depend on:

| Fact | Evidence |
|---|---|
| `String.hash` is `@[extern "lean_string_hash"] protected opaque`. | `src/Init/Prelude.lean:4829-4830` |
| C: `hash_str(sz, bytes, 11)` where `sz = lean_string_size(s) - 1` (bytes, no NUL). | `src/runtime/object.cpp:2550-2554` |
| `hash_str` is MurmurHash64A with the given seed, tail switch, final `h ^= h>>r; h*=m; h ^= h>>r`. | `src/runtime/hash.cpp:15` (function), `:57-59` (`hash_str`) |
| `Hashable Nat` is `UInt64.ofNat n` (Lean-level, mod 2^64). | `src/Init/Data/Hashable.lean:15-16` |
| `hash64 u := mixHash u 11`, used by con-leche's `PKey` hash. | `src/Init/Data/Hashable.lean:73-74` |
| `Name.hash` in core is itself a `@[computed_field]`. | `src/Init/Prelude.lean:4887` |

## 2. How con-leche uses the computed hash fields

### 2a. Definitions (writers of the field)

- `Name.hashData` (`@[computed_field]`): `ConLeche/Kernel/Name.lean:35-38`. `anonymous = 1723`; `str p s = mixHash (mixHash 1 p.hashData) (hash s)`; `num p n = mixHash (mixHash 2 p.hashData) (hash n)`. Instance: `Name.lean:43`.
- `Level.hashData` (`@[computed_field]`): `ConLeche/Kernel/Expr.lean:46-51`. Instance: `:56`. `levelHash`/`levelsHash`: `:200-205`.
- `Expr.data` (`@[computed_field]`, packed word): `ConLeche/Kernel/Expr.lean:414-458`. Bits 63..32 = `hash32(mixHash …)`, bits 30..16 = loose-bvar bound, bits 15..1 = fvar range, bit 0 = has-level-param (`:211-216`, `packData` `:247`, field readers `:251-263`). `Expr.hash` `:478`; instance `:494`.
- The non-hash packed fields (bvar bound, fvar range, has-LP) are not mixHash-dependent; they are functions of the structure with spec definitions in `ConLeche/Kernel/ExprOps.lean:68-75` (section "Derived-field spec functions").

### 2b. Readers of the hash VALUE or the field

Equality guards (fast reject):

- `Name.decEqPtr`: `ConLeche/Kernel/Name.lean:75` (`if hh : a.hashData = b.hashData`), reject branch `:94` (`else isFalse (fun e => hh (by rw [e]))`).
- `Level.decEqPtr`: `ConLeche/Kernel/Expr.lean:92`.
- `Expr` beq, interpreted: `enterBeq` `ConLeche/Kernel/Expr.lean:1098` (`a.data != b.data` → `.no`); `beqMemo` `:1248` (`a.data == b.data` guard); correctness lemma `beqMemo_iff` `:1254-1259`.
- Doc of the intended role: `Expr.lean:734` ("a hash mismatch *is* an inequality").

Hash-map keys (Std.HashMap / HashSet keyed by a node):

- `Hashable Expr`: `ConLeche/Kernel/Expr.lean:494`.
- Expr-keyed memos: `ConLeche/Kernel/ExprOps.lean:153,183` (`Std.HashMap Expr Nat`); `ConLeche/Kernel/CheckerBase.lean:69` (`HashSet Expr`); `ConLeche/Frontend/NatOpGround.lean:88` (`HashSet Expr`, insertion/membership).
- Name-keyed environment tables: `ConLeche/Kernel/FEnv.lean:36-37,60,76`.
- Cached engine: `PKey` (`ConLeche/Cached/ExprOpsC.lean:193-200`) is a packed **pointer address** plus cursor, hashed by `hash64`; the cached engine validates every hit by pointer identity (`ConLeche/Cached/ExprOpsC.lean:1268-1271` and the `ptrDec` check at `:186-193`). So bucket placement depends on heap addresses, and the outcome does not.
- `BeqMap` (`Expr.lean:816`) is keyed by a packed address pair `beqKey` (`:824`), not by the hash.

Proof obligations that mention the hash:

- `LawfulHashable Expr`: `ConLeche/Verify/Cached/Erase.lean:102-105` (`hash_eq _ _ h := by rw [eq_of_beq h]`).
- Product and list lawfulness: `ConLeche/Verify/Cached/SimC.lean:60-61` (`prod_hash … := rfl`), `:86-94`, `:156-179` (`list_hash_fold`, congruence only).
- No lemma in the repo states any arithmetic property of `mixHash` (grep for `mixHash` in theorem statements: only the congruence lemmas above).

### 2c. Does any checker result depend on the hash value?

Checked:

- **Equality correctness** needs only that the field is a function of the structure: `a = b → a.hashData = b.hashData` (proved by `rw`/`rfl`, `Name.lean:94`, `Expr.lean:1254-1259`). Any deterministic total `mixHash` satisfies this.
- **HashMap/HashSet correctness** needs only `LawfulHashable` (`BEq`-equal ⇒ equal hash), again a consistency property (`Erase.lean:104-105`).
- **Iteration order**: I found no `fold`, `toList`, `toArray`, `keys` or `for … in` over a `Std.HashMap`/`HashSet` in `ConLeche/Kernel`, `ConLeche/Verify`, or `ConLeche/Cached`. The `.toList` hits are on `Array`/`List` values (e.g. `ConLeche/Kernel/Inductives/BlockTail.lean:42,109` is `Array`). This is a grep result, not a proof.
- **Olean reader** does not read stored hash words: `ConLeche/Frontend/Olean/Region.lean:26-27` ("a cached field … is never read"), `ConLeche/Frontend/Olean/Spec.lean:28-29` ("skipped").

Conclusion: the checker's verdicts depend on the hash only through equality-consistency. Hash *values* affect only speed (collision rate, bucket layout). They never appear in output.

## 3. Options for compiling con-leche verbatim

**A. Lean definition, bit-exact to the C code.**

```
def mixHash (h k : UInt64) : UInt64 :=
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := (k ^^^ (k >>> 47)) ^^^ m
  (h ^^^ k) * m
```

- Equivalence to `lean.h:2293-2302` is by reading only. `UInt64` ops are mod 2^64 and `>>>` masks the shift with `% 64` (`src/Init/Data/UInt/Basic.lean:680`). I did **not** run a C-vs-Lean comparison (no `lean` binary here; only `gcc`). Lean cannot prove the link to C, so it stays a trusted replacement, the same kind of trust as the existing extern/pointer escapes.
- Bit-exactness is not needed for correctness (see 2c). It only matters if the checker must reproduce official hash values, which it never reads.
- `String.hash` would need the same treatment (MurmurHash64A over UTF-8 bytes, seed 11, little-endian 8-byte loads; `hash.cpp:15-59`, `object.cpp:2550-2554`).

**B. Lean definition, any deterministic function (recommended for the checker).**

- Replace `mixHash` and `String.hash` with ordinary total Lean definitions that are functions of the value; no C correspondence is claimed.
- Proofs unchanged: `Name.lean:94`, `Expr.lean:1254-1259`, `Erase.lean:104-105` use only the consistency property.
- Trust base: none added for the hash itself, only the definitional replacement of two externs, and the result differs from official values, which nothing reads.
- Check: the verified compiler must actually use the substitute in the compiled path. If it compiles kernel terms, this is the only change.

**C. Drop the cache: hashes as plain recursive functions.**

- Kernel terms do not contain the field. `@[computed_field]` is implemented by `implemented_by` of unsafe `_override` definitions (`src/Lean/Elab/ComputedFields.lean:141-150`, `:163-172`, `:191-205`), and the spec `hashData` is an ordinary structural function. A compiler that ignores the `implemented_by` compiles the spec directly: no storage, no unsafe code.
- Cost: `hash` of a node walks its subtree, so every memo probe costs `O(size)`. This may be a large slowdown on the memo-heavy paths, and I did not measure it.

**D. Hash as a data field (explicit constructor argument).**

- Needs a proof, per constructor, that the stored value equals the spec, because the guards need `a = b → data_a = data_b`. This is the same kind of lemma as `bvarB_eq` (`ExprOps.lean`). It changes every constructor and all ~26 `mixHash` sites. Strictly more proof work than B or C, for no checker-level gain.

**Recommendation.** B for the hash, if the verified compiler honours the substitution. Use C only if the compiler will not accept any extern for the hash; the cost is performance. D is not worth it.

## 4. Other blockers in the same files (not mixHash)

These are outside this question but block "compile verbatim" the same way:

- Pointer equality: `withPtrEqDecEq` / `withPtrEq` from `Init.Util` (`ConLeche/Kernel/PtrDecEq.lean:1-30`, `ConLeche/Kernel/Expr.lean:5-6`, `:748`, `:1248`).
- `lean_is_exclusive_obj` via `implemented_by` (`ConLeche/Kernel/Exclusive.lean:12-14`, `:62-71`, `:89-107`).
- `@[csimp]` substitutions (`ConLeche/Kernel/Name.lean:97-98`, `Expr.lean:1290-1296`).

## Summary

- `mixHash` is `@[extern "lean_uint64_mix_hash"] opaque` (`Prelude.lean:4820-4821`); core has no Lean definition; C body at `lean.h:2293-2302`.
- The hash fields are read only in equality fast-paths and as `Hashable` keys. Checker verdicts depend only on the hash being a function of the value. No output depends on hash values.
- Recommended: substitute a Lean definition of `mixHash` and `String.hash` (option B). Bit-exactness is not required; if it is later wanted, option A's equivalence is untested.
- The owner's plan in `Testing/notes/ROADMAP.md` (section "Strategy", bullet "con-leche hashing") is option A plus fuzzing against native `mixHash`, and it already says "if output does not depend on the hash function, any Lean hash will do". Section 2c of this file establishes that premise. The fuzzing step is then needed only if bit-exactness is wanted.
- Not tested in this work: no Lean binary, so nothing here was compiled or run.

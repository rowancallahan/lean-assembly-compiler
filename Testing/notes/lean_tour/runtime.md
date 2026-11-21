# Lean 4 (v4.34.1) code emission + runtime: tour for nano

Sources read: `src/Lean/Compiler/LCNF/EmitC.lean` (NOTE: in v4.34.1 EmitC lives under `LCNF/`, not `IR/`; `IR/` has only EmitLLVM),
`src/include/lean/lean.h` (3474 lines), `src/runtime/object.cpp` (2989), `mpz.{h,cpp}`, `mpn.{h,cpp}`.
Line numbers are for tag v4.34.1. Not executed/tested here; everything below is from reading source.

## 1. Plain-language explanation

After Lean elaborates and optimises a definition, the compiler holds it in a small IR (let-bindings, `cases`, join points,
explicit `inc`/`dec` reference-count instructions, `ctor`/`proj`, calls). `EmitC` is a ~1200-line pretty-printer from that IR to
C text: each IR instruction maps to ONE call of a C helper from `lean.h` (`lean_nat_add`, `lean_alloc_ctor`, `lean_dec` ...).
So the "backend" is thin; the semantics live in `lean.h` + `runtime/`.

Every Lean value is one machine word `lean_object*`:
* low bit 1 -> unboxed scalar: `lean_box(n) = (n<<1)|1`. Used for small `Nat`, enum-like constructors, `Bool`, `Char`, `UIntN` in polymorphic position.
* low bit 0 -> pointer to a heap object with an 8-byte header `{int rc; u16 cs_sz; u8 other; u8 tag}`.
* Monomorphic `UInt8/16/32/64/USize/Float` are passed as raw C ints (IR types `uint8`..`usize`); boxed only when stored in polymorphic data.

Worked example `def f (x : Nat) := x + 1`:
1. IR: `def f (x : @& obj) : obj := let y := 1; let r := Nat.add x y; ret r` (x borrowed, so no inc/dec).
2. EmitC (`emitLetDecl` -> `emitLit` L~700, `emitFap` L~650): literal `1` becomes `lean_unsigned_to_nat(1u)` (<2^32; larger literals `lean_cstr_to_nat("...")`, parsed at runtime); `Nat.add` has `@[extern "lean_nat_add"]` so the call is `lean_nat_add(x, y)`.
3. C: `LEAN_EXPORT lean_object* l_f(lean_object* x){ lean_object* x_2; lean_object* x_3; x_2=lean_unsigned_to_nat(1u); x_3=lean_nat_add(x,x_2); return x_3; }`
4. `lean_nat_add` (lean.h:1543): if both are scalar -> `lean_usize_to_nat(unbox a + unbox b)` (result boxed if <= 2^63-1 else allocates a bignum via `lean_big_usize_to_nat`); otherwise `lean_nat_big_add` (object.cpp:1433) -> mpz.
   Note the add of two unboxed values can't overflow `size_t` (each <2^63).
5. Constructors with fields: `lean_alloc_ctor(tag,numObjs,scalarSz)` then `lean_ctor_set(o,i,arg)` per field; zero-field ctor = `lean_box(cidx)`. Reuse: `reset/reuse` pair = "if exclusive, overwrite in place" (emitReset/emitReuse).
6. Self tail calls become `goto _start` (emitTailCall L725, with temp copies when params overlap). Non-self calls are real C calls (no general TCO; relies on the C compiler).

## 2. File map

| What | Where |
|---|---|
| IR type -> C type (`uint8`->`uint8_t`, object/tagged/tobject/erased/void->`lean_object*`) | EmitC.lean:31 `toCType`; box/unbox/sproj/sset op names :46-:84 |
| per-IR-instruction emission | `emitLetDecl` :558 (ctor, reset, reuse, proj/uproj/sproj, fap, pap, ap, box, unbox, isShared, lit, erased) |
| tail call -> `goto _start` | `emitTailCall` :725 |
| inc/dec/del/setTag/set/cases/jmp/ret/unreach | `emitBasicBlock` :780 (`cases` -> `switch` on `lean_obj_tag`, or `if` for 2 alts) |
| function header, `_start:` label | `emitDecl` :925; >closureMaxArgs params use `lean_object** _args` for the boxed closure entry |
| closed-term / `[init]` handling, module init, `main` | `emitGroundDecl` :309, `emitInitFn` :1007, `emitMainFnIfNeeded` :1084 |
| string literal escaping | `quoteString` :213 |
| object header, tags (ctor<=243, Closure 245, Array 246, ScalarArray 248, String 249, MPZ 250, ...) | lean.h:90-130, struct layouts :130-260 |
| scalar box/unbox | lean.h:334-336 |
| RC inc/dec, sticky range for overflow, MT counts negative | lean.h:640-700, `lean_dec_ref_cold` object.cpp |
| alloc small objects (mimalloc or malloc with size word) | lean.h:482-530 |
| Array API (`uget`, `uset`, `push`, `pop`, `swap`) | lean.h:1000-1140; `lean_copy_expand_array` object.cpp:2739; `lean_array_push` :2768 |
| ByteArray (scalar array, elem size in `m_other`) | lean.h:1160-1250; copy/push in object.cpp |
| String (`m_size` incl. NUL, `m_capacity`, `m_length` = #chars, UTF-8 data) | lean.h:211; ops object.cpp:2037-2530 |
| Nat small-path inlines | lean.h:1500-1700 |
| Nat big-path / mpz glue | object.cpp:1397-1700 (`mpz_to_nat` normalises), mpz.h/.cpp (GMP if `LEAN_USE_GMP`, else own) |
| own bignum fallback (32-bit digits, schoolbook add/sub/mul/div, to_string) | runtime/mpn.cpp (356 lines) |
| UIntN ops | lean.h:2038-2200 (`lean_uint8_*` ... `lean_uint64_*`, `lean_usize_*`) |
| panic | `lean_panic_fn` object.cpp:198, `lean_internal_panic*` :92-111 |
| closures / `lean_apply_N` | lean.h:913-940, runtime/apply.cpp (925 lines, generated-style) |

## 3. Facts that matter for nano (exact semantics)

### Nat
* Representation: boxed scalar iff value <= `LEAN_MAX_SMALL_NAT = 2^63-1` (64-bit); otherwise pointer to an MPZ object. Invariant (relied on by `lean_nat_eq`'s pointer comparison and everything else): **a Nat that fits in 63 bits is NEVER a bignum** (`mpz_to_nat` object.cpp:1402 normalises; `mpz_to_nat_core` asserts non-small).
* `add`: small path `unbox a + unbox b` (cannot overflow size_t), then re-box or promote. `mul`: small path checks `r <= MAX_SMALL && r/n1 == n2`, else `lean_nat_overflow_mul` (bignum). `n1==0` returns early.
* `sub`: truncated: `n1 < n2 -> 0`. Big path also returns 0 when a1<a2 (:1443).
* `div`: `n2 == 0 -> 0` (small path); `mod`: `n2 == 0 -> n1` (lean.h:1606). Big paths follow the same (`x/0=0`, `x%0=x`) - I read the small paths; big div/mod bodies at object.cpp:1473/1504 were only skimmed.
* `shiftr` small: shift >= 64 -> 0 (lean.h:1697). `shiftl`/`pow` with non-small or > UINT_MAX exponent: **`lean_internal_panic` (process abort/exit)**, not a Lean-level result. So Lean's *runtime* diverges from the Lean *logic* here; nano's "same results" must treat these as out of scope (or must also abort).
* `Nat.log2 0 = 0`; `Nat.pred 0 = 0` (via sub).
* `Nat -> UIntN` (`lean_uintN_of_nat`): scalar -> C cast (truncation mod 2^N); big -> `mod8/16/32/64` of mpz, i.e. also mod 2^N. `USize.ofNat` for big uses `get_size_t` (mod 2^64 on 64-bit). So all are `n % 2^N`.
* Literals >= 2^32 are not emitted as constants: `lean_cstr_to_nat("decimal")` parses at runtime.
* `Nat.decEq/decLt/decLe`: both scalar -> compare words (boxing is monotone), else big compare.

### UIntN (lean.h:2038-2200)
* `add/sub/mul/neg/complement`: plain C modular arithmetic (mul written `1U*a1*a2` to avoid signed promotion UB on UInt16/8).
* `div`: `b==0 -> 0`; `mod`: `b==0 -> a`.
* `shift_left/right`: **shift amount taken mod width** (`a << (b % 64)`), as Lean's `UInt64.shiftLeft` spec says. RISC-V `sll` masks to 6 bits and ARM64 `lsl` register form also masks mod 64, so these are native.
* `log2`: loop, `log2 0 = 0`. `of_nat` truncates. `to_nat` -> boxed if <= 2^63-1 else bignum (UInt64 values >= 2^63 become MPZ objects!).
* Comparisons/`dec_eq` unsigned.

### Array (object array)
* Layout: header, `m_size`, `m_capacity`, `m_data[]` of `lean_object*`. Capacity doubles on growth: `(cap+1)*2` (copy_expand, :2743); in non-exclusive push, expand only if `cap < 2*size+1`.
* In-place update iff `lean_is_exclusive(a)` (rc == 1); otherwise copy (all elements inc'd) then update. This is what makes `Array.push/set` O(1) amortised for linear use; semantics are identical either way.
* `Array.get!` out of bounds: prints "Error: index out of bounds" via `lean_panic_fn` and **returns the default value** (does not abort unless `LEAN_ABORT_ON_PANIC`); `set!` OOB returns the array unchanged after a panic message; `swap` OOB returns the array unchanged silently; `pop` of empty returns the same array. Fast variants (`uget/fget/uset`) assume proofs: no checks (assert only in debug).
* Non-scalar (boxed) index is by construction OOB.

### ByteArray (scalar array, 1 byte/elem)
* `get!` OOB returns **0** silently (lean.h:1207); `set!` OOB returns array unchanged; `push` amortised like Array (copy_expand for sarray); `uget` unchecked. Copy-on-write if shared.
* Elements are raw bytes; `UInt8` unboxed in IR. FloatArray uses elem size 8.

### String
* UTF-8 bytes + NUL terminator; `m_size` counts the NUL, `m_length` counts code points (O(1) `String.length`, `utf8ByteSize = m_size-1`). Positions are **byte offsets** (`String.Pos` = Nat).
* `get s i`: i >= size -> default char `'A'` (U+0041, `lean_char_default_value`); i in the middle of a codepoint / invalid -> also default (`get_core` fails). Decoding is strict: rejects overlongs, surrogates, > 0x10FFFF (lean_string_utf8_get_fast_cold, :2310s).
* `next s i`: `i >= size -> i+1`; otherwise advance by lead-byte length (1..4); invalid lead byte -> `i+1`. `prev s i`: `0 -> 0`, `i > size -> i-1`, else step back over continuation bytes. `extract s b e`: empty if `b >= e || b >= size`, or `b` not a char start; if `e` not a char start, treated as end of string; `e` clamped to size. `set` OOB or at non-start returns s unchanged.
* `push`/`append` in place if exclusive and capacity allows (`mk_capacity`), else copy. `String` literals are `lean_mk_string_unchecked(lit, bytes, chars)` built at init (or persisted ground terms).
* Equality/ordering: bytewise (`lean_string_eq`, `lt` is memcmp-order, which equals code-point order for valid UTF-8).

### RC / misc
* `m_rc > 0` single-threaded, `< 0` multithreaded (atomic), `0` persistent (never freed). Inc/dec on scalars is skipped by `lean_is_scalar`. 32-bit RC overflow goes into a "sticky" band (object leaked, never freed) - a safety hack, not a semantic feature.
* Closures: `{fun ptr, arity u16, num_fixed u16, args[]}`; `lean_apply_n` in apply.cpp saturates/over-applies/under-applies generically. Closure functions always take boxed args (`_boxed` wrappers generated by IR).
* Out-of-memory, `unreachable`, `sorry`, big-shift/pow exponent: `lean_internal_panic` = print + `exit/abort`; they are not observable Lean values.
* Tail calls: only direct self-recursion in tail position becomes a loop. Mutual/non-self tail calls consume C stack (stack overflow detection exists in runtime/stack_overflow.cpp).

## 4. Reuse assessment for nano

Legend: (a) blueprint = copy design, re-prove our version; (b) test oracle; (c) copy code as-is. "Provable?" = in nano's setting (total, first-order, nano subset, proofs against Sail ISA models).

1. **Boxed-scalar/pointer word representation (`lean_box`, low-bit tag).** (a) blueprint. Cheap and well-matched to 64-bit RISC-V/ARM: tag test = `andi 1`. Prove a rep invariant `rep(v, w)`; box/unbox lemmas are bit lemmas (`(n<<1|1)>>1 = n` for n<2^63), small effort (days). Choice for nano: whether to adopt Lean's exact layout (header with rc/tag) or a simpler one; matching Lean's layout is NOT required for result equality, only values.
2. **Nat small path semantics** (truncated sub, `/0=0`, `%0=n`, overflow detect on mul, promote on add). (a)+(b). The semantics are one-liners; the proof content is the bit-level overflow test (`r/n1 == n2` needs a 64-bit divide, so on RISC-V use `mulhu` (high word == 0) instead; both provable from Sail's `mul`/`mulhu`). Effort: small-medium per op (1-3 days each with Sail semantics for mul-high).
3. **Bignum Nat.** Two realistic options:
   * (a) own design modelled on `mpn.cpp` (356 lines: add, sub, mul schoolbook, long division per Knuth D, to_string; digits `unsigned int` = 32-bit so a 64-bit product fits in a machine word with no carry flag/`mulhu` needed). Total functions on `Array UInt32` (or packed words) are easy to write in the nano subset; proving them correct against `Nat` arithmetic (`toNat (add a b) = toNat a + toNat b`) is the real work: add/sub/compare ~1-2 weeks, schoolbook mul ~1 week, Knuth D division ~2-4 weeks (the hard one; normalisation/quotient-estimate lemma). A simpler division (shift-subtract, O(n^2) bit-by-bit, or repeated limb-by-limb with a trial-quotient loop) is far easier to prove and is probably acceptable at nano's scale.
   * (c) GMP: not usable (C library, unverifiable, not in nano subset). `mpn.cpp` as-is: it is C++ with raw pointers/`unsigned` carries; cannot be consumed or proven directly - treat as blueprint/oracle only.
   * Keep Lean's normalisation invariant (value <= 2^63-1 is always boxed) - needed so `Nat.decEq` can compare words in the fast path; make it part of the rep predicate, and state each big op's result as `norm(...)`.
   * (b) oracle: any big-Nat test can be run against real Lean (`#eval`) and diffed. High value, near-zero cost.
4. **UIntN ops.** (a)/(b). Lean's table is the spec (mod 2^N, `/0=0`, `%0=a`, shift mod N). Trivial to match on RISC-V: `divu` by 0 gives all-ones (NOT 0) and `remu` by 0 gives a - so nano must emit an explicit zero check for div (and Sail's `DIV` model encodes that); `remu` by 0 = a already matches Lean. ARM64 `udiv` by 0 gives 0 (matches Lean directly; `urem` needs msub). Sub-word types (UInt8/16/32) need masking after add/sub/mul on a 64-bit ISA (not needed on load/store-width ops). Effort: small per op once the width-N wrap lemma exists.
5. **Packed arrays (ByteArray / UInt64 arrays).** (a) blueprint: header `{size, capacity}` + inline data, element width in header; copy-on-write via rc==1; growth `cap = (cap+1)*2`. Semantics to match: `get!` OOB = 0 silently (ByteArray) vs panic+default (Array); `set!` OOB = no-op; `push` amortised doubling. Proof burden is the separation-style invariant "buffer holds `size` initialised elements = model list", plus allocator/capacity arithmetic. With nano's block memory model: medium (2-4 weeks for push/get/set/copy with a bump allocator). If nano lacks RC/exclusivity, arrays are copied on every `set` (O(n)) or the compiler must prove linearity; Lean's `isExclusive` runtime test is the pragmatic route and is also easy to prove sound ONLY with a proven RC discipline - that is the big dependency (see 7).
6. **String.** (a)+(b). Representation as UTF-8 ByteArray + cached length is simple; the edge-case table in section 3 (default char, invalid positions, extract rules) is exactly what must be reproduced and is best used as a conformance test list. Note the C runtime's behaviour on invalid positions is made to agree with the reference (`String` logical definition on `List Char`); nano should state the spec in terms of the logical model and prove decode/encode round-trip (UTF-8 decode lemmas: ~1-2 weeks, mostly bit arithmetic). Do not copy the C.
7. **Reference counting + `inc/dec` insertion + reset/reuse (Perfect Reuse).** (a) blueprint if nano wants in-place updates; (c) impossible (compiler passes in `LCNF`/`IR`, ASTs of Lean's own compiler, huge, partial defs, not in nano subset). Proving an RC pass correct is research-grade (Ullrich & de Moura "Counting Immutable Beans"; tests in Lean repo `tests/elab/rc_model.lean` model the RC arithmetic). Honest estimate: months; alternative for nano: no RC, immutable values with bump allocation + no free (arena), and arrays updated destructively only under a compiler-proven linear-use analysis, or copy always. This choice drives everything in 5.
8. **EmitC structure itself (IR -> text).** (a): shows a minimal IR suffices: `let` of {ctor, proj, call, pap, apply, lit, box/unbox}, `case`, `jmp` to join points, `ret`, `unreachable`, plus self-tail-call loops. For nano, emit machine code directly from this IR with 1:1 instruction templates per construct (one rep-lemma per construct) - this is also how EmitC works (one helper per instruction). Copy as-is: no (Lean's EmitC depends on the whole `CompilerM`/`Environment`, partial defs, `Name`, extern attribute tables).
9. **Closure representation + `lean_apply_n`.** (a). Header + fn ptr + arity + fixed args; apply handles under/exact/over-application. Needed only if nano supports higher-order values. apply.cpp is mechanical (generated-style per arity) -> blueprint; proof = one generic lemma on the apply loop; medium. Boxed wrappers `_boxed` for scalar-typed params are required for uniform closure ABI.
10. **Test oracle use.** The cheapest high-value reuse: compile test programs with real Lean (`lake build` -> C -> binary, or `#eval`) and diff outputs against nano on edge cases from section 3 (`n-m` with n<m, `x/0`, `x%0`, `2^64` boundaries around 2^63 box limit, UInt shift by >= width, `get!` OOB, string with invalid positions, `extract` boundaries). Also the C source of `lean.h` is a ready list of per-op semantics to turn into property tests.

### Things nano must decide / risks
* **2^63 boundary:** nano Nat small-limit must be explicit; UInt64 `to_nat` of values >= 2^63 must produce a bignum (or nano's `Nat` rep must otherwise be able to hold it).
* **Panic divergence:** real Lean returns default after printing on `get!`/`set!` OOB (Array), but aborts for big `shiftl/pow` and OOM. "Same results" must define output equivalence modulo stderr text and exit paths; recommend restricting nano's subset to total/checked ops (`get`, `[i]'h`, `getD`) in compiler sources and treating `!` variants as out-of-subset or modelled as default-return.
* **No `Int`/`Float` needed** for the above; `Int` small range is 32-bit (`LEAN_MAX_SMALL_INT = INT_MAX`) on 64-bit, a quirk if ever added.
* `lean_nat_eq` by pointer comparison depends on the normalisation invariant; any nano bignum op that forgets to normalise silently breaks equality.
* Not verified by running anything: big `div/mod` details, `mod64` of mpz, string `append`/`mk_capacity` growth policy were not read line-by-line.

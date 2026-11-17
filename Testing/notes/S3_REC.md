# S3 recursion: equation-lemma front end, Lean's induction principles as the termination certificate (branch s3-rec, 2026-11-17)

Base: `origin/ir-s3` (S3 calculus, `Testing/notes/IR_S3.md`) merged with `origin/main`. Plan followed:
`Testing/notes/CONLECHE_KNOT.md` steps 2–5 on small examples, then the smallest recursive component of con-leche's
`CoreC`. Toolchain: `elan.lean-lang.org` was refused by the network proxy at the start; the owner approved adding
the host to the environment's allow-list (approval prompt), then elan installed normally.

## 1. What the front end does with recursion (`Compiler/S3/Front.lean`)

- **Driven by equation lemmas.** Every function, recursive or not, is read from `f.eq_def` (`getUnfoldEqnFor?`): for
  structural recursion this is the equation over the function itself, not the `brecOn` term; for well-founded
  recursion (`WellFounded.fix`, irreducible in 4.29) likewise. One application is rewritten, the right side is
  normalised (matchers, `casesOn`, instance projections, lets, `do` join points), and every call — to itself, to a
  member of its mutual block, or to anything else — becomes an S3 `call`. The component is never unfolded.
- **Body certificate + ONE closure per component** (CONLECHE_KNOT.md §4). Per function, the certificate is
  `Good P φ f [enc x…]` (its body evaluates to the oracle's value, every call it makes is good). It is proved:
  - self-recursive: by the function's own `f.induct` (Lean's functional induction = its termination argument,
    structural or well-founded, any measure incl. tuples), the recursive calls closed by the induction hypotheses;
  - **mutual** (new): the call graph's strongly connected components are computed; a component that is a Lean mutual
    block gets ONE theorem `certM<k>` by the block's `mutual_induct` (one motive per member: `Good` for the members
    the program uses, `True` for the others), and each member's certificate is its projection;
  - non-recursive: unfolded once.
  The two certificates of the review stay apart: the body equation is `f.eq_def` (used by `rw`), the call decrease
  is inside Lean's `induct`/`mutual_induct` (never computed, never re-proved).
- **Termination of the program** (`WfCert`, `Compiler/S3/Syntax.lean`). The slot is now a statement:
  `WfCert P D := ∀ f vs, D f vs → Acc (CallRel P) (f, vs)` with `CallRel P a b` = "`a` is a call reached by the body
  of `b`". Generic theorems: `acc_of_reaches` / `acc_of_ev` (any evaluation's call tree is well-founded, by induction
  on the evaluation), `wfCert_of_good` (`Cert.lean`). Every program gets `N.wf : WfCert P (main on any encoded
  input)`, from `main_good`, i.e. from the certificates, i.e. from Lean's own induction principles.
  Decision (noted): the old slot (a `Nat` measure on ALL argument lists, including ill-typed ones) could not be
  filled in general, and a lexicographic measure does not embed into `Nat`; it was unused, so it was replaced.
- State through recursion: a parameter whose type reduces to a function (`StateT σ m α` = `σ → m (α × σ)`) is a
  parameter of the S3 function; the equation (fewer binders) has its right side applied to the extra arguments;
  the certificate's induction generalises those arguments (`induction xs using f.induct generalizing s`).

Other front-end features added on the way (all generic, none restates a library function):

| feature | how |
|---|---|
| `Nat` | its own inductive type (unary: `zero`/`succ`), `Enc Nat` (`natV`/`natD`); `+`, `==`, `<`, `≤` compile `Nat.add`, `Nat.beq`, `Nat.blt`, `Nat.ble` **verbatim from their equation lemmas** (structural recursion on `Nat`, i.e. `Nat.brecOn`/`Nat.rec`); literals as constructor chains (≤ `natLitMax` = 4096) |
| `BitVec 64` | a word (as `UInt64`); `UInt64.ofBitVec`/`toBitVec` are the identity |
| proof fields | a `Prop` field of a constructor is not stored (`St.masks`): constructors, `casesOn` arms, projections remapped; `Fin n` = `mk [val]`, `Fin` literals `⟨k % n, _⟩` |
| `Array`, `ByteArray`, `String` | their kernel structures (`Array.mk (toList)`, `ByteArray.mk data`, `String.ofByteArray bytes _`); `Enc` instances (String: validity decided on decode) |
| `Int` | its inductive (`ofNat`/`negSucc` over `Nat`) — no code needed |
| `StateT`/`Except`/`ExceptT` | monad values applied to their state are inlined (a non-recursive function applied beyond its declared arity); `ite`/`dite`/`cond` with extra arguments push them into the branches; `(let x := v; b) a` → `let x := v; b a`; the certificates unfold the monad operations (`monadSimp`, added when a program mentions these types) |
| `isRecursive` | also plain structural recursion (an unfold equation exists for the recursive definition) |
| certificate tactics | `s3FinValLit` (`(k : Fin n).val` → `k % n`), `s3EncNatLit` (`enc (k : Nat)` → `.c 1 [enc (k-1)]`), `-Fin.isValue`, `UInt64.toBitVec_ofNat`, `Nat.beq/blt/ble = false` normal forms, `Bool.or/and_eq_true`; split order: `if` conditions before call results (avoids a 6-constructor blow-up on `Code`); closers `omega`, `rfl`, `apply_assumption` (all-or-nothing), callee certificates under `intros` |
| `s3_compile … simp [ids]` | the optional simp list was never parsed (the optional group has 4 children); fixed |
| dependent index parameters | `args[i]` with its proof unfolds to `List.get xs ⟨i, h⟩`, a parameter of type `Fin xs.length`: its value is `.c 0 [enc i]` (`encFin`), the oracle decodes it by `match` + `dite` on `i < bound` (no total decoder into `Fin 0` needed), the caller-facing certificate takes `(n, n < bound)`; all `Fin _` with a run-time bound share one S3 datatype |
| unreachable code | `False.elim`, `absurd`, `False/Empty.rec/casesOn` become some value of the result type (never evaluated; the certificate's induction never enters that arm) |
| mutual + state | members' parameters beyond the motive's (a `StateT` state) are quantified inside the motive; a well-founded block's `mutual_induct` lives on its first member |
| `optParam` | parameter types lose `optParam`/`autoParam` annotations (else the oracle lemma does not rewrite) |
| closers | each closer is all-or-nothing (`c; done`): a partial closer no longer stops `first`; BitVec order contradictions via `toNat` + `omega`; generated certificates get `maxHeartbeats 1000000` |

The 15 entries of `S3Examples.lean` regenerate byte-identical words (checked: `emit_s3.lean` re-run, no diff).

## 2. Results (`Riscv/Frontx/S3RecExamples.lean`), QEMU + Sail, 50 cases each

Every entry: `N.correct` (machine theorem, exactly the Sail axiom set), `N.computes`, `N.wf`
(⊆ {propext, Classical.choice, Quot.sound}); `Testing/scripts/axioms_s3-rec.lean` (in `check.sh`).
Tests: `lake env lean --tstack=4000000 Testing/asm/emit_s3rec.lean` (IR interpreter == Lean on all cases), then
`python3 Testing/asm/ir_test.py check 50 s3_<name>`.

| entry | function (verbatim) | shape | words | QEMU + Sail |
|---|---|---|---:|---|
| s3_incs | `Mach.IR.SR.incs` (self-hoster) | `List.brecOn` row; `List (Nat × Nat) → Code Nat` | 3237 | 50 × 2 ok |
| s3_inits | `Mach.IR.SR.inits` | `List.brecOn` row; extra `Nat` | 3287 | 50 × 2 ok |
| s3_sets | `Mach.IR.Hoist.sets` | `List.brecOn` row; `List (BitVec 64)`, `m + 1` | 3660 | 50 × 2 ok |
| s3_initl | `Mach.initL` (static `sp`) | `List.brecOn` row; `Nat.beq`/`Nat.blt` | 3619 | 50 × 2 ok |
| s3_storeregs | `Ir.storeRegs` | `List.brecOn` row; two lists, `Reg = Fin 15`, `List EOp` (`Int`) | 3672 | 50 × 2 ok |
| s3_fetchg | `fetchG` (`Compiler/Front/Pipe.lean`) | `List.brecOn` row; `AStmt` accumulator, `Fin 8` | 2808 | 50 × 2 ok |
| s3_merge | `merge` (ours) | well-founded, `termination_by xs.length + ys.length` | 1541 | 50 × 2 ok |
| s3_evod | `evSum` / `odCnt` (ours) | mutual, result types `List UInt64` / `UInt64`, non-tail calls both ways | 1311 | 50 × 2 ok |
| s3_lex | `lex` (ours) | lexicographic `(xs.length, k.toNat)`, inner counter reset to `x &&& 7` | 1164 | 50 × 2 ok |
| s3_stexc | `stepS : List UInt64 → StateT UInt64 (Except UInt8) UInt64` (ours) | state + exception across a non-tail recursive call | 2094 | 50 × 2 ok |
| s3_iotanumargs | con-leche `Cached.iotaNumArgs` (`CoreC.lean`) | structural over con-leche's `Expr` (`Name`/`String`/`Level`/`Literal`) | 1128 | 50 × 2 ok |
| s3_getappargsarr | con-leche `Cached.getAppArgsArr` + `getAppArgsArrGo` + `iotaNumArgs` | structural; `Array.set!`, `Array.replicate` from their equations | 2502 | 50 × 2 ok |
| s3_mkapprange | con-leche `Cached.mkAppRange` | well-founded `termination_by j - i`; `args[i]` with its proof | 2090 | 50 × 2 ok |
| s3_dropvars | con-leche `Expr.dropVars` (+ `Expr.instantiate1`) | the probe's `Nat.brecOn` row: structural on `Nat`; `Nat.sub`/`Nat.blt`/`Nat.beq` | 2582 | 50 × 2 ok |
| s3_knot | `walkK` / `tagK` (ours) | the knot's shape: mutual in `StateT UInt64 (Except UInt8)`, well-founded on `(xs.length, rank)`, one member calls the other on the same list; exceptions in 10 of 50 cases | 3564 | 50 × 2 ok |

The harness (`natW`, `wNat`, the `*B` encoders, `pairsN`, …) is compiled through S3 with the function; `wNat`
is itself well-founded (`termination_by x.toNat`) and `natW` structural on `Nat` (`Nat.rec`).
All six self-hoster `List.brecOn` rows of the probe (`yield.json` `lowest/selfhost` 54, 68, 87, 101, 105, 146)
and con-leche's `Nat.brecOn` row `Expr.dropVars` now compile verbatim.

## 3. Not done / blocked

- `Nat.brecOn` rows of the probe: con-leche `Expr.dropVars` compiles verbatim (`s3_dropvars`); its cached twin
  `dropVarsC` needs `Expr.instantiate1C` (the `Cached` sources, not in the repository); the book rows
  (`addNatPos`) are not in this repository.
- `CoreC`'s knot itself (one mutual block of ~70 functions in `CheckCM = StateT CState CheckM`): the shape now
  compiles (`s3_knot`), and `Array` indexing with proofs / `set!` / `replicate` / `size` compile (`s3_mkapprange`,
  `s3_getappargsarr`). Blocking: `CState`'s default `maxNatSize = 134217728` and the fuel `2^62` (unary `Nat`
  cannot hold them), then con-leche's `Cached` sources (`StateC`, `ExprOpsC`: `Std.HashMap` keyed by `Expr`)
  in the repository, then the members one by one.
- `Nat` is unary: exact but O(n) space/time; fine for register numbers, not for fuel or byte offsets. Next: a
  limb representation with primitive `Nat.add/sub/mul/div/mod/beq/ble` proved once (a compiler feature, like the
  word operations).
- Generic monads (`[Monad m]`, `CoreFns` records): specialisation only, as before.
- Dependent `Fin` parameters inside a mutual component: rejected for now (the mutual certificate path has no
  `encFin` form yet).

## 4. Decisions (taken without asking, per the round prompt)

- `WfCert` replaced by an accessibility statement over the call relation (see §1); filled per program from the
  certificates, which come from Lean's induction principles.
- `Nat` unary (exactness first; library `Nat` functions compiled verbatim). Literal limit 4096.
- Proof fields are erased everywhere; projecting a proof field at run time is an error.
- `φ` is `noncomputable` (proof-only object) so that encoders need not be computable.
- Small monad wrappers applied to a state are inlined rather than made S3 functions (their certificates would need
  instance unfolding inside `Enc.enc (throwThe …)`).

## 5. Final check

After merging `origin/main` (ROADMAP only): `bash Testing/scripts/check.sh`: **ALL CHECKS PASSED** (51 min; again after `dropVars`, 20 min; 45 new axiom
lines from `axioms_s3-rec.lean`, 48 after `dropVars`: every `correct` exactly the Sail set, `computes`/`wf` ⊆ {propext, Classical.choice,
Quot.sound}, `acc_of_ev`/`wfCert_of_good`/`certM4` ⊆ {propext, Quot.sound}). The statement-fingerprint step prints
its usual WARNING (statement hashes unchanged, dependency closures changed; warning-only, not re-frozen, per the
round rules). QEMU + Sail: all 15 new entries 50 × 2 ok (§2); the 15 entries of `S3Examples.lean` regenerate
byte-identical words.

## 6. Next for the knot (CONLECHE_KNOT.md steps 6–7)

1. `Nat` as limbs (`.c 0 []` / `.c 1 [w limb, rest]`, canonical), with `Nat.add/sub/mul/div/mod/beq/ble/blt`,
   `succ`-patterns (`n + 1` = test + `n - 1`) and literals as primitives proved once against `Nat` (a compiler
   feature like the word operations). Unblocks `maxNatSize = 2^27`, fuel `2^62`, and keeps every `Nat` function of
   this round working (the representation changes, the certificates' shape does not).
2. con-leche's `Cached` sources into the repository verbatim (`StateC`: `CState`, `ModeMemos`; `ExprOpsC`), then
   `Std.HashMap` operations (`insert`/`get?` over `Array (AssocList)`, `hash` on `Expr`'s computed `data`) through S3.
3. Dependent `Fin` parameters inside mutual components (the `encFin` form in `genMutual`).
4. The `CoreC` members in call-graph order (`iotaNumArgs`, `getAppArgsArr`, `mkAppRange` done), each component
   certified by its block's `mutual_induct`; the knot's tuple measures need no extra work (`s3_knot`).

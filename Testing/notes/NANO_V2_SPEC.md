# NANO v2 milestone 1: frozen interfaces (DRAFT by worker 1, branch `nano-v2`; the owner confirms)

Basis: NANO_V2_ASTRA.md rounds 1–4 (binding), NANO_V2.md (plan, increment 1), and what workers 2 (backend,
`nano-v2-backend`, namespace `Nano.V2B`) and 3 (stage rewrite, `nano-v2-src`, namespace `Nano.V2S`) reported on
2026-11-17 18:07–18:35. Where they differ, this file picks one and says so (§8). Changes after the freeze: only by the owner.

## 1. The construct set (exact Lean forms; everything else is rejected)
A source file is a sequence of `def`s in the closed environment of §2. Types: `UInt64` (scalar), `Nat` (FUEL ONLY),
`List UInt8` (the input, read-only, and the output, affine), `Buf` (word buffer, affine, §3).

| construct | exact form | notes |
|---|---|---|
| numerals | `0`… (UInt64; wrap mod 2^64), `-n` only as v1 | in fuel position: Nat numerals `< 2^32` |
| arithmetic | `a + b`, `a - b`, `a * b` | UInt64, wrapping (v1) |
| bits | `a &&& b`, `a \|\|\| b`, `a ^^^ b`, `a <<< k`, `a >>> k` | `k` a numeral `< 64` (worker 3 uses only these) |
| comparisons | `a == b`, `a < b`, `a <= b`, `a ≤ b` | UInt64 only (Int64 dropped for milestone 1, Astra r2 §8); only in `if` conditions; the typing guard of NANO_V2.md B1 |
| conditions | `c && d`, `c \|\| d`, parentheses | Bool; pure, so eager evaluation is Lean's value |
| `if` | `if c then e else e` | both branches the same type (UInt64, `Buf` or `List UInt8`); ownership checked per branch |
| `let` | `let x := e; body` | v1 rules (`;` required) |
| calls | `g a1 … ak` of an EARLIER def, fully applied | non-recursive helpers are inlined; acyclic only |
| fuel loop | §1.1 | the ONLY recursion |
| prelude ops | §3 | the only operations on `List UInt8` / `Buf` |
| fuel arithmetic | `len' xs` (= `xs.length`), `n + m`, `n * m`, numerals, in a fuel argument only | the value must be `< 2^64` for admitted inputs (proved per stage via `Adequate`) |

### 1.1 The ONE loop pattern (Astra r2 §1, generalised to several parameters as worker 3 needs)
```lean
def f : Nat → T1 → … → Tk → R
  | 0, x1, …, xk => e0                -- the zero case keeps its Lean meaning (`| 0 => s` is SUCCESS)
  | n + 1, x1, …, xk => e             -- self calls `f n a1 … ak` only in TAIL position, fuel exactly `n`
```
Fuel first; `x1 … xk` are any of the types above; at most one self call per branch; no other recursion (mutual,
non-tail, other fuel arguments are rejected). Lowered to a real loop (header, zero test, decrement, parameter update,
backward branch), never unrolled; ONE generic header-to-header theorem (Astra r4 §1).
DECISION for worker 3's inliner (one non-tail self call whose result is the output argument): NOT in the subset (Astra r2
§1 binding); rewrite it tail-only with a `Buf` table (worker 3's option b).

## 2. The fixed, closed Lean environment
- Header-less file = `import Init` (exactly what `Testing/nano/oracle*.lean` uses), plus ONE prelude module
  `Nano/V2/Prelude.lean` (§3) whose names are reserved. No `open`, no `namespace`, no `variable`, no attributes, no
  `instance`, no `where`, no `termination_by`, no `match` other than §1.1's fuel match, no `fun`, no tactics.
- Instances used: `UInt64`'s `Add Sub Mul AndOp OrOp Xor HShiftLeft HShiftRight BEq LT LE` + decidability, `Bool`'s
  `&&`/`||`, `Nat` literals / `+` / `*` / `n + 1` patterns, `List.length` on `List UInt8` through `len'` only.
- Names: v1's rule (one lowercase letter, then digits / `_`digits) plus the prelude names; keywords of §1.

## 3. The prelude (buffer and I/O API; functional semantics = the definitions themselves)
```lean
-- input (read-only, never consumed)
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64     -- 0 past the end
def len (xs : List UInt8) : UInt64 := xs.length.toUInt64
def len' (xs : List UInt8) : Nat := xs.length                                      -- fuel only
-- output (affine: consumed and returned)
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
-- word buffers (affine)
abbrev Buf := List UInt64
def bnew : Buf := []
def bsize (b : Buf) : UInt64 := b.length.toUInt64
def bget (b : Buf) (i : UInt64) : UInt64 := b.getD i.toNat 0                        -- 0 out of range
def bset (b : Buf) (i v : UInt64) : Buf := b.set i.toNat v                            -- no change out of range
def bpush (b : Buf) (v : UInt64) : Buf := b ++ [v]
def bpop (b : Buf) : Buf := b.dropLast
```
Worker 3's existing `rd`/`len`/`put` already have these names and meanings. Capacities: every buffer and the output have a
fixed capacity κ (a constant of the stage). A program that may exceed it must test `bsize b < κ` itself and fail in Lean
(Astra r3 §3); the machine's capacity trap (status −2) is outside the admitted domain.
Ownership (Astra r3 §4), checked by the elaborator: `rd`/`len`/`bsize`/`bget` borrow (result scalar);
`put`/`bset`/`bpush`/`bpop` consume their buffer argument and return the new one; a consumed variable is dead afterwards;
both `if` branches consume the same set; a loop consumes and returns the same shape; `xs` is never consumed.

## 4. State shape
No record type: the state of a stage loop is its parameter list (fuel, `xs`, cursor and other scalars, `Buf`s, output
`o`), as worker 3 writes it. Products are NOT in milestone 1 (no stage needs them so far; Astra r1 "a language addition
must name the compiler-source use that needs it"). A stage entry is `def stage (xs : List UInt8) : List UInt8 := f
(len' xs + 1) xs 0 … bnew … []` (fuel expression of §1).

## 5. Stage formats and the composition
- C = L >=> P >=> I >=> E >=> A over `List UInt8 → List UInt8`, ERROR = the EMPTY output (every valid intermediate and
  final output is non-empty), propagated: a stage given `[]` returns `[]`.
- Formats (milestone 1 = the v1 formats, so the existing stage proofs and tests apply; extended per increment):
  L = lexer + parser 2a: `stage2a (lexB src)` (Nano/ParseS3B.lean tag format); P = parser 2b: `serU u`
  (Nano/SerU.lean); I = inliner: `inlB` records (Nano/InlP*.lean); E = expander: `mexp` records (Nano/ExpandM.lean);
  A = assembler: `asm` bytes (Nano/Asm.lean).
- Growth: each language increment adds its tags to these formats in ONE place (the shared format file of the stage);
  worker 1 adds the tag to the elaborator and AST, worker 3 to the stage, in the same increment.
- Astra r4 §0: the required equation is `Adequate x κ → C x = compileV2 x` (the v2 compiler definitions); equality
  with the v1 stages is only a route.

## 6. Calling convention and the contract
- Entry (StartCorrect, unchanged): a0 = input address, a1 = input length, a2 = work base (8-aligned), sp = work top,
  a3 = output address, ra = return; code at a FIXED origin (no PIC; Astra r3 §5).
- Exit: ok ⇒ a0 = 0, a1 = output length, output bytes at a3; Lean error (empty output) ⇒ a0 = 1, a1 = 0; out of work
  memory ⇒ a0 = −1 (oomFlag), a1 = 0; capacity trap ⇒ a0 = −2. Written registers: t0–t6, a0, a1, a4, a5 (worker 2's
  list); everything outside the output and work blocks unchanged.
- `ImplementsBytes B Cκ adm work` (Astra r3 §6): for every input with `adm input` and every initialised state
  (`StartCorrect` with work ≥ `work input.length`), the Sail run returns to ra with the observation above for
  `Cκ input`. Lean shape (to be stated in `Nano/V2/Contract.lean`, owner: worker 1):
  ```lean
  def ImplementsBytes (B : List (BitVec 32)) (C : List UInt8 → List UInt8) (adm : List UInt8 → Prop)
      (work : Nat → Nat) : Prop :=
    ∀ input s0 call, adm input → StartCorrectAt B s0 call input (work input.length) →
      ∃ s1, Runs riscv s0 s1 ∧ pcAt s1 call.returnAddress ∧ FrameKept s0 s1 call ∧
        (if C input = [] then a0 s1 = 1 ∧ a1 s1 = 0
         else a0 s1 = 0 ∧ a1 s1 = (C input).length ∧ readMemory s1 call.outputAddress (C input).length = some (C input))
  ```

## 7. Theorem interfaces (who proves what)
- Worker 1 (language + front end, this branch): `Nano.V2.nanoElab : List UInt8 → Option Prog`, `Nano.V2.Prog.eval`
  (functional, loops by fuel recursion, prelude as §3); subset evidence (oracle fuzz + per-program agreement); the
  ONE-SOURCE certificate generator (Astra r4 §4: `body_f`, `lookup_f`, `meaning_f` per definition); `ImplementsBytes`
  and `Adequate` definitions.
- Worker 2 (backend): `compile : Prog → Option (List (BitVec 32))` and
  `compile_correct : compile p = some B → ImplementsBytes B (Prog.eval p) (Adm p κ) (work p)`.
- Worker 3 (stages): the five stage defs IN the subset, accepted by `nanoElab`, and
  `Adequate x κ → (L >=> P >=> I >=> E >=> A) x = compileV2 x`.
- Worker 4 (bootstrap): `ImplementsBytes B₁ C` from compiler 1 (`link_stage`), staged kernel evaluation of `C s = B₂`,
  the fixed point B₂ = B₃.

## 8. Differences between the workers, resolved here
1. Output model: worker 3's threaded `List UInt8` with `put` (affine) — kept (§3); worker 2's in-place buffer is its
   implementation under ownership.
2. Loops with several parameters (worker 3) — allowed (§1.1); Astra's single `s : St` is the one-parameter case.
3. Non-tail self call in worker 3's inliner — rejected (§1.1), rewrite with a `Buf` table.
4. Word buffers: `List UInt64` in Lean (worker 3) vs `Array UInt64` (worker 2, Astra r2): the PRELUDE hides it; the
   Lean definitions above use `List UInt64` (simpler bridges and kernel evaluation); the machine representation is
   worker 2's `[len][cap][data]`.
5. Exit codes: worker 2's proposal (§6) with the Lean error = empty output mapped to a0 = 1.
6. Increment 1 of NANO_V2.md (branch-free `if` on v1's records) stays as the proved link for pure expressions; the
   milestone-1 backend with branching `if`, loops and buffers is worker 2's (`Nano.V2B`); worker 2 translates
   `Nano.V2.E` or adopts it, and the AST of §1 becomes `Nano.V2.E` extended (worker 1 owns the file).
7. Int64: dropped for milestone 1 (Astra r2 §8); the v2 elaborator keeps it only for v1 compatibility.

# TINYSELF2: growing the self-hoster with the inductive path (branch `tinyself2`, based on `main` @ce989e1)

Base: `Testing/notes/TINYSELF.md` (`tinyCompile`, bytes → bytes, 17 slots, machine theorem, `selfhost_test.py`) and NOTES §17–21
(`Testing/notes/frontx/NOTES.md`). Every step below is a compiler written as ordinary Lean over a **user inductive**, compiled
verbatim by `frontx_ind` (no compiler source touched), with the generated theorem `….implements1` (77 Sail-model axioms +
`propext`/`Classical.choice`/`Quot.sound`/`valid_reservation`, no `sorryAx`: `Testing/asm/tiny2/axioms.lean`).

Tests per step (`bash Testing/asm/tiny2/run_all.sh`):
(a) `frontx_test.py check 50 tiny2_sN`: the compiled compiler on qemu-system-riscv64 **and** Sail == Lean's compiler (50 source trees,
guards, gp/sp, Sail write set);
(b) `Testing/asm/tiny2/selfhost2_test.py sN`: the binary's output (bytes of the output tree) is executed and compared with Lean's `eval` of the
source on 5 inputs each (250 runs): steps 1–3 by a Python machine on the instruction bytes, step 5 by **native RV64 code on qemu-riscv64**
(`driver2.c`: `uint64_t f(uint64_t x)`).

## Steps

| step | file | what | words | result |
|---|---|---|---|---|
| 1 | `Riscv/Frontx/TinyS1.lean` | `Ex = lit n \| var \| bin k a b` (source tree) → `Ins` list (stack machine), two types, `Ins.app` as a second function of the program | 2452 | **ok**: 50 cases QEMU == Sail == Lean; 250 runs == `eval` |
| 2 | `TinyS2.lean` | + comparisons (`ult`, `eq`), `set`, `seq`, `if` (as strict select `sel`, no jumps), difference-list `comp e K`, source and target in ONE type `T = nil\|lit\|var\|bin\|op` | 2174 | **ok** (same checks). Jumps / `while`: **not done** (F3, F4, F5) |
| 3 | `TinyS3.lean` | register allocation: three-address code, register = stack depth `d`, threaded as the word parameter and packed into the instruction scalar (`k + d`, source opcodes pre-multiplied by 16) | 2133 | **ok** (same checks) |
| 4 | — (`repro/r14…`) | constant folding as a separate function / pass | — | **blocked**: F1, F12, F13, F14; pass pipeline F11 |
| 5 | `TinyS5.lean` | real RV64 words: `addi x16/x17, x0, imm`, `mv x16, a0`, `op x16, x16, x17` for left-deep expressions (right operand a leaf) | 2194 | **ok**: the code the compiled compiler emits runs on qemu-riscv64 == `eval` (250 runs) |

Honest scope of the successes. Step 5 is an encoder for left-deep pure expressions with two registers, and the *source* supplies the
pre-shifted fields (literal as `imm << 20`, operator as its funct bits): the front end has no shifts (F15). Step 3's allocation is the
depth parameter, not a graph/liveness allocation. Step 2's `if` evaluates both branches. None of this is a bootstrap (the compiler's own
source is not a program of its language); `tinyCompile`'s self-hosting run (bytes → bytes, 17 slots) is untouched.

## Failures, ranked by how much they limit the self-hoster

Re-run of r1–r15 on the final tree: all fail as described (`repro/repro_results.txt`); r16, r17 were checked separately (same errors). Each has a standalone reproducer in `Testing/asm/tiny2/repro/` (`bash Testing/asm/tiny2/repro/run_repros.sh` prints each first error;
`/tmp`-free, each file imports only `Riscv.Frontx.IndCmd`).

**F1 — the dispatch function of `F` must fit one `beqz` range, so about 4–5 arms.** (`r1_arm_count.lean`; the checks that fail are
`decide` on `2 * (glF … + …) < 2048` of `Pg.wf`/`WfProg1W`.) With one recursive call and one constructor per arm: nil + 4 constructors
build, nil + 5 do not (measured, `n5`); 3 arms with two `app` calls each build, 4 do not; one arm with two `mk` and two calls (`.op k (.op d K)`
as an argument) already fails. Every other limit below is met inside this budget: the compiler of step 2 had to be folded into the four
constructors `nil/lit/var/bin` (+`op`) with the operator in the scalar. *Missing feature:* long branches or a jump table / one function per
arm in the plain back end (the loop body is a single function; `compBFC`'s checked-words route is for the optimiser only).

**F3 / F2 / F9 — `sem` cannot be proved when a call argument is anything but a call or a constructor over variables.**
`r2` (`.op 8 .nil`, a literal scalar, as the tree argument of `Ins.app`), `r3` (`.pop (comp b)`, a constructor around a call result, even
through a `let`), `r5` (`.push 0 K` as the `b` argument of a recursive call), `r8` (`if k == 5 then K else .op k K` as the argument).
All: `frontx_ind: unsolved goals`, case `bin`/`set`; the goal shows the induction hypothesis stated on `emb b` while `simp` has already
unfolded `emb (ctor …)` into cells, so it no longer matches. Literal scalars and computed scalars containing a literal (`d + 1` as a scalar of
a constructor, `4 + 4`) fail; `k + d`, `d`, `k` (variables) work; a word `d + 1` as the word argument works; an `if` in a word argument fails.
Consequences met: no constants (`push 0`, `pop`, `stx`) inside continuations (payload-free constructors or a no-op/`nip` instruction
instead), no `jmp (len E - len K) E` (F3 + F4), a `seq` that needs a `pop` between two compiled subtrees. *Missing feature:* a `sem` simp
set that rewrites `emb (ctor …)` back (e.g. `generalize` the argument before applying the IH), i.e. the induction step for arguments that are
built terms.

**F4 / F7 — an arm may call only ONE later function; a later function that calls another, or has a variable pattern, fails `sem`.**
`r4` (arm with `Ins.app` and `Ins.len`: the program lists `[comp, app]`, `len` is dropped, then `unsolved goals` + `decide`),
`r7` (`wrap E m K` with a variable pattern calling `len`: `sem` leaves `h2.pg.arms[0]?` unevaluated), and the `cp`/`app` variant (type
mismatch in the generated `E.ext 0 .w …`). Together with F2/F3 this is what blocks **jump offsets** (need `len` of a compiled subtree and
the subtree itself) and **`while`** (F5: the backward offset needs `len C + len B` where both are built *after* the jump in a difference list
and a second compile of a child violates "each child called at most once"; backpatching needs `len` + `app`/`patch` in one arm). Worked
around by `sel` (branchless) and by dropping `while`. *Missing feature:* several later functions per arm in the program's
function-list construction; helper-of-helper `sem`.

**F6 — one tree type per program.** A tree parameter `b` of another type than the main tree (`comp : Ex → Ins → Ins`), or a two-input entry of
two types, gives `Application type mismatch … Ex × Ins → Ins` / the entry glue plugs `Ex.lit` for a nullary `Ins.nil` (`r6`, `r5`).
Different types are fine only through `ext` calls on already-built trees (step 1's `Ins.app`). Worked around by one inductive holding source
and target constructors (step 2 on), which also eats the F1 arm budget (the target constructors are pass-through arms).
*Missing feature:* a typed `b` parameter (`Kd`/shape per parameter) in `E`, `enc2` for two shapes.

**F11 — a pipeline of passes cannot be one entry.** `def twice e := ren (ren e)` (`r16`): `frontx_ind` accepts `f e := g lit e` only
(`'show' tactic failed`); one pass alone is fine. So step 4/5 are separate programs; the harness would have to chain binaries (bytes of one tree
are the input of the next; formats agree). An arm may call a later function on a *node's* result (step 1) but there is no way to run a
second pass over the whole result of the first. *Missing feature:* an entry that is a composition `g (f e)` (the `ext` of the entry with
a call as its tree argument; `E` already has `ext`).

**F12 / F13 / F14 / F10′ — match forms for a folding pass.** `r13`: nested patterns `.bin k (.lit x) (.lit y)` — "nested patterns are not
supported". `r12`: `match a, b with | .lit x, .lit y => … | _, _ => .bin k (fold a) (fold b)` on the *children*: `sem` ends with `⊢ False` in
the case `bin.nil.nil…`. `r10` / `r14`: `match fold a, fold b with …` (the shape of `Level.simplify`, here with 2 calls): `decide` on the
code size fails even with the right-hand side reduced to `.lit (x + y)` (F1), and a tree-valued `if` over `UInt64 ==` inside the arm
leaves the `emb (if …)` goal unsolved (`r11`, the same with a helper `mk2`; also F9). So **constant folding (step 4) is blocked**.
*Missing feature:* nested patterns (reduce to the two-value match that exists), and the F1 budget.

**F8 / F10 — entry glue.** A `UInt64` literal as an argument of the entry's call (`comp e 0 .nil` with `0 : UInt64`) fails in the last
`rewrite` (`UInt64.toBitVec 0` vs `0#64`); with `Nat` it works. An entry with a word argument read from the input and a tree literal
(`compile e d := comp e d .nil`, `r9`) gives `Function expected at compile p.fst p.snd`. A tree literal at the entry must be nullary
(`.op 164115 …` → "the second argument must be nullary"), so the `mv a0, x16; ret` trailer of step 5 is appended by the harness.
Worked around with `Nat` fields and a constant depth `0`.

**F15 — no shifts / multiplication in the inductive path** (`reify` has `+ - & | ^` only, `IndCmd.lean` l.437). The three
register fields of an RV64 word (`d<<7`, `d<<15`, `(d+1)<<20`) need `d * 1081472`; doubling by `+` with `let`s is inlined by `simp`
(a 13-doubling term has 8449 leaves): `` `simp` failed: maximum number of steps exceeded `` in `sem` (`r15`); 3–4 doublings per arm
overflow F1 (the first attempt of step 3: 24 locals). Hence the pre-multiplied source fields and the two fixed registers of step 5.
*Missing feature:* `shl`/`lshr` by a constant (the `Op`s exist: `Spec/Code.lean`; only the front-end reification and `sem` lemmas are
missing) and `*` by a constant.

**F16 — `_` arm in a function called from another function** (`r17`): `equation len.eq_2 has no constructor pattern … unsupported term`
(entry-level `_` arms are accepted, `armsOfCases`).

Minor: `Ins.len` etc. as a *result of kind word* works when it is the only later function in an arm (`g2`, `g4` in the exploration).
The equation order of a function must be the constructor order (a `len` written `push, jz, … , nil` gave an unsolved goal on the first
attempt; cause not isolated, kept in constructor order after that).

## Where it stands, by ask

1. *source program as an inductive* — done (steps 1–5). 2. *more ops* — comparisons, assignment, sequencing, conditional (as select): done;
real jumps and loops: blocked by F1+F3+F4 (each alone is a fix of the compiler: arm size, argument terms in `sem`, several later functions).
3. *register/slot allocation* — by depth, done (step 3); a non-trivial allocator (liveness, spilling) not attempted. 4. *second pass* —
constant folding blocked (F1, F11–F14); a second pass as a separate program is possible only for pass-through maps. 5. *real encodings* —
done for left-deep expressions (step 5, runs natively), general depth blocked by F15.

Suggested order of compiler work (largest unlock first): **F1** (arm size / long branches; unlocks every richer arm), then **F3/F2/F9**
(`sem` for built arguments; unlocks continuations, `pop`, constants), **F4/F7** (two later functions per arm: `len`/`app`, so jumps and `while`),
**F15** (shifts: real encodings of arbitrary depth), **F11** (pass pipeline), **F6** (typed `b`), then the match forms (F12–F14) and F8/F10/F16.

## Environment notes

Lean 4.29.0 and the model were installed from the GitHub release (the box had none), `qemu-user`, `qemu-system-misc`, `gcc-riscv64-linux-gnu`
from apt; Sail C simulator 0.9 (`Testing/setup/box.sh`). All steps were run with QEMU and Sail. No RV64 gcc is needed except for the
test drivers (`driver2.c`, the harness `.S`). Base build: `lake build Riscv.Frontx.TinySelf` ≈ 45 min on 4 cores (the Sail model),
each step 10–150 s.

Files: `Riscv/Frontx/TinyS{1,2,3,5}.lean`; `Testing/asm/emit_tiny2_s{1,2,3,5}.lean` (words, cases, run files);
`Testing/asm/frontx-words/tiny2_s*.{words,cases}`; `Testing/asm/tiny2/{selfhost2_test.py,driver2.c,s*.run,axioms.lean,run_all.sh,repro/}`.
(`TinyS4` is not a file: the attempt is `repro/r14_s4_fold_full.lean`.)

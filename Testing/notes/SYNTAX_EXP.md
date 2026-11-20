# SYNTAX_EXP: growing nano's accepted syntax (branch `exp-syntax`, experimental, NOT the release)

Base: `origin/release-434` @ 56e2584. Toolchain: Lean 4.34.1. RISC-V model: `deps-rv-regen434` @ 4cf120c8 (model_hash
`6ac35da9… 161`, checked). Locally the root `lake-manifest.json` was switched to lean-sail v10 to build the regenerated
model (as on `rv-regen-434`); that change is **not committed** (release-434 still pins v5).

## Decision table

| # | construct | status | C delta (lines) | proof delta (lines) | difficulty | next-step estimate |
|---|---|---|---|---|---|---|
| 1 | comments, nested block comments, docstrings, `@[…]`, `namespace`/`open`/`section`/`end`, `private` | **done + proved** (lexer only) | Lex2 +28 −3 | Lex2Sound +417 −56, Lex2Spec +27, MainTokWF +34 −22, SrcLink +115 −27, Sem +55 −21 (regenerated Cert/SrcLink/Tests not counted) | S (≈4 h incl. regen) | — |
| 2 | `match` on UInt64 literals, `_`, a variable, a pair | **done + proved** (new desugar stage; branch `exp-syntax-match`, see §2 for build status) | new Dsg +106 (12 defs) | DsSpec +108 (trusted spec), DsSound +1299, DsTok +298, Compile +24 −13, SelfC +15, Tests ≈ +30 (generated Cert/SrcLink and Tests ids not counted) | M (≈5 h) | — |
| 3 | `a[i]!`, `a.size`, `a.push` | not started | — | — | S–M | see §3 |

## 1. Trivia in the lexer

### What is accepted (spec: `LexSpec.step`, `Nano/V2Self/Proof/Lex/Lex2Spec.lean`)
New `step` cases, emitting **no tokens**:
- `--` up to (not including) the newline;
- a block comment from slash-dash to the matching dash-slash, **nested** as in Lean (`blockEnd`, depth counter); this
  covers docstrings and module docs. An unterminated one has no `step`, so the text is rejected;
- `@[` up to and including the first `]` (attributes). Without a `]`, the text is rejected;
- the words `namespace`, `open`, `section`, `end` (whole words, maximal munch) up to the newline;
- the word `private`.
`--` used to lex as two minus tokens. No valid program used that: `a - -b` is not in the grammar, and in Lean it is a comment.

### Semantics caveats (owner decision)
- **Namespaces are flattened.** `namespace A` / `end A` lines are dropped, so `A.f` and `B.f` both become `f`. The
  parser's duplicate-def check then rejects the program. A qualified reference `A.f` is rejected, because `.` is not a
  token. Nothing is silently mis-resolved.
- `open X in` on its own line is dropped, which is harmless. `namespace X def f …` on one line drops the def. Lean
  formatting puts it on its own line, so this is unlikely in practice.
- An all-trivia text lexes to `[]`, which C rejects, as before.
- Not covered: `protected`, `noncomputable`, `partial`, `set_option … in`, `variable`, `universe`, `#eval`. Each is one
  more `kwX` entry and one more `s3'_eq` length case.

### Implementation (C, `Nano/V2Self/C/Lex2.lean`)
- `s3` (keyword chain) gets 5 entries: kind 92 (skip the line) for namespace/open/section/end, kind 93 for private.
- `s4` gets 3 kinds: 94 `--`, 95 slash-dash, 96 `@[`.
- New scanners: `s12 n x i b` gives the first position ≥ i holding byte b, or the end. `s11 n x i d` scans a nested
  block comment and returns the position after its end, or 0 to reject.
- `s9` gets 5 branches. Parser, Own and Gen are untouched.

### Proofs (all local; no parser/Own/Gen/machine proof changed)
- `Lex2Sound`:
  - `kwX` = `kwTable` + the trivia words. `s3'_eq` is extended to 9-byte words (namespace).
  - `s4'_eq`, `kind`, `kind_spec` (+5 disjuncts).
  - `s12_eq`/`s12_drop`, `s11_sound`.
  - `s9_sound` gets 5 cases.
  - The main theorem `s10_sound` is unchanged in statement.
- `MainTokWF.step_tok`: the new steps emit `[]`.
- `Main/Sem.step_len`: the 9-words-per-byte bound, with `blockEnd_len`.
- `SrcLink.step_app`: lexing composes across newline-terminated chunks. New lemmas `blockEnd_app`, `mem_dropWhile`,
  `dw_head`.
- Regenerated as in PERF_NAMES:
  - `Proof/Cert/*` (`dump_pc` + `gen_cert.py`);
  - `Proof/SrcLink/*` chunks (`srclink/gen.lean … 800`; this reproduces the committed chunks byte for byte from the old
    text);
  - `Tests/SelfInPath` and `SelfInQuiet`: def ids ≥ 13 shift by 2 (s11 and s12 are inserted before s9; both are push-free
    and added to `S`).

### Tests
- Fixpoint, with nanorun (no QEMU on this box): B1 (Lean-compiled) → B2 → B3. B3 = B2 = 348,904 B, sha256 `395f0b9d…`.
  The old B2 also compiles the new source to the same bytes. Self-compile costs 664,861,123 instructions (was 641,996,759:
  +3.6 %, for C's 2 extra defs and the larger s3/s9).
- All 8 `examples/*.lean` now compile **with** their `--` header lines. The code is byte-identical to the old compiler's
  code for the stripped files.
- `arm/rv2arm.lean` (45 comment lines) compiles unstripped to the same `rv2arm_rv.bin`.
- New `examples_syntax/trivia.lean` (ROT13) uses every trivia form. `run_syntax.sh` gives `exp:OK`, and real Lean
  `#eval` gives the same bytes.
- 21 probe strings (nested comments, `-/` outside a comment, `@[x` unterminated, `endx`, …): C's `s10` and the spec agree
  on all of them, including the rejections.
- `arm/B2_arm.bin` was regenerated with the nanorun-run translator. The same procedure reproduces the old SHA256SUMS
  entry exactly.

### Surprises
- Lean's block comments nest, so this module's own doc comments must not mention slash-dash literally (it opened a
  nested comment and the file did not parse).
- A third consumer of `LexSpec.step` existed (`Main/Sem.step_len`). It was found only by the full build.

## 2. `match` (new stage `t10` between lexer and parser)

### What is accepted (spec: `DsSpec.ds`, `Nano/V2Self/Proof/Lex/DsSpec.lean`)
- `match E with | 3 => a | 7 => b | y => c` desugars at token level to
  `let $ := E; if $ == 3 then a else if $ == 7 then b else let y := $; c`.
  - `$` (identifier `14 1 36 0`) cannot be spelled in Lean, so it cannot clash with user names.
  - `| _ => e` becomes `else e`.
  - A **first** arm `| (x, y) => e` becomes `let (x, y) := $; e`.
- `match` and `with` are recognised as identifier spellings (they are Lean keywords, so they are never user names). The
  lexer is unchanged.
- A match ends at the `)` of its paren depth, at the next `def`, or at the end of the text. By then it must have a
  catch-all arm (`_`, a variable or a pair).
- Rejected, which is what Lean does too or close to it:
  - an arm after the catch-all;
  - a match without a catch-all;
  - `match` inside a scrutinee;
  - `| (x, y)` as a later arm;
  - multi-scrutinee matches, `| 1 | 2 =>`, Nat/Bool/enum patterns (out of scope).
- Checked against real Lean: the if-chain ends at `else` and `;` the same way Lean's `match` does. `if c then match … | _ => 2
  else 3` and `let y := match … | _ => 2; y` give the same values under `lake env lean` (`#eval`) as in our compiler.
- Conservative difference: after a match that ends at `;` or `else`, a later `|` at the same paren depth (for example the
  next fuel arm) is rejected, although Lean accepts it. Workaround: parenthesise the match.
- **A text without the token `match` passes through unchanged and allocates nothing** (`t11` scan; spec `noMatch`).
  - Match-free programs need exactly the old work memory.
  - A program with `match` needs about 8 MiB more (two buffers at κ capacity). `examples_syntax/run_syntax.sh` uses
    120 MiB; the nanorun default is 80.

### Verification (4.34.1, exp-syntax-match = exp-syntax with rv-regen-434 + match)
- `lake build Nano.V2Self.REVIEW` plus Tests.SelfInPath / MainCert / AuditWitness and Main.ArmTop: all OK.
- `Testing/scripts/review_axioms.sh`: **`OK: 8 theorems, axioms as pinned`**.
- `t10_sound` and `hsrc_C`: [propext, Classical.choice, Quot.sound].
- No `sorry`, `native_decide` or `bv_decide`. `decide +kernel` is used for C's own token list and the witnesses.

### Statement change (owner decision)
- `pOf` (`Proof/Main/Compile.lean`): `∃ ts, Lexes x ts ∧ ParsesProgram ts p` becomes
  `∃ ts, DsSpec.LexesD x ts ∧ ParsesProgram ts p`, where `LexesD x ts := ∃ t0, Lexes x t0 ∧ ds t0 = some ts`.
  `DsSpec.ds`/`go`/`pat`/`armCode`/`splitTok`/`noMatch` are new trusted definitions (≈80 lines, readable). They should
  go into REVIEW §3.
- `mC = g41 x (o41 (y16 (t10 (s10 x))))`.
- The main theorems keep their names and shapes: `compiler_correctG`, `TopOn`, `C_correctLO`, `C_runsO`,
  `self_correct_C`.

### Proofs
- `DsSound.t10_sound : t.length < 2^24 → C.t10 t ≠ [] → ds t = some (C.t10 t)`. Axioms: propext, Classical.choice,
  Quot.sound. Its parts:
  - token splitting (`t0_sound`, `t1_sound`);
  - word tests (`t2_eq`/`t3_eq`/`t4_eq`, via generated linear case chains);
  - emit (`t5_eq`, `t6_eq`);
  - arms (`t7_sound`, `t8_sound`);
  - the scan (`t11_sound`) and `go_noMatch`;
  - the cell stack (`Rep`, `rep_set`/`rep_push`/`rep_pop`/`rep_zero`);
  - the main loop `t9_sound`;
  - the output bound `go_len` (≤ 3 words per input word).
- `DsTok.ds_tokWF`: the desugared words are `TokWF` and below 2^24 words, which is what `parStage` needs.
  `DsTok.ds_id`: a `TokL` stream without the token `match` desugars to itself.
- `SelfC.hsrc_C`: C's own text has no `match`. This is checked by `decide +kernel` on SrcLink's token list `T0` (under 5 s).
  So `LexesD X0 W0` holds and `self_correct_C` keeps its statement.
- Tests:
  - `MainWitness`/`MainCert` gain one kernel-checked premise per witness (`C.t10 ts = ts` or `ds ts = some ts`);
  - `SelfInPath`: def ids ≥ 17 shift by 12; new `X27`/`X28` for the empty-input path through `t11`/`t10`;
  - `SelfInQuiet.S` gains the push-free 17–21 and 27.

### Tests
- Differential, C `t10` against spec `ds`:
  - 17 hand cases;
  - 20,000 random fragment soups;
  - 20,000 generated nested matches with mutations (1,010 of them really desugared).
  0 disagreements.
- Fixpoint (nanorun, default 80 MiB): B3 = B2 = 376,088 B, sha256 `37a6be1c…`. 721,873,615 instructions (+0.0 % for the
  scan; the old B2 compiles the new source identically).
- The 8 old examples give byte-identical code. `examples_syntax/matchdemo.lean` (literal, `_`, variable and pair arms;
  nested in `let` and in a call argument) passes and matches real Lean.

## Trusted-statement changes (owner review)

Every definition below is listed in REVIEW §3 or used by `pOf`/`mC`. Each is shown as a verbatim `git diff` against `origin/release-434`.

### (1) `LexSpec.step` and its new helpers (Nano/V2Self/Proof/Lex/Lex2Spec.lean)
```diff
@@ -3,6 +3,9 @@
 whitespace (space, newline) is skipped; the operator table is searched longest-first; a word is a maximal run of
 [A-Za-z0-9_'] (a keyword/prim, an identifier `14 (1,b)* 0`, or, when it starts with a digit, a decimal number
 `5` + 8 little-endian bytes of the value mod 2^64, all characters of the word must then be digits).
+Trivia (no tokens; exp-syntax, Testing/notes/SYNTAX_EXP.md): two dashes up to the newline; a nested block comment
+(slash-dash ... dash-slash, docstrings included; unterminated: rejected); an attribute `@[ … ]` up to the first `]` (none: rejected); the
+words `namespace`, `open`, `section`, `end` up to the newline; the word `private`.
 Anything else (and a digit-led word with a non-digit) is rejected: no `step`, so no `Lexes`. -/
 import Nano.V2Self.Prelude
 namespace LexSpec
@@ -40,6 +43,21 @@ def kwTable : List (List UInt8 × UInt64) :=
    ([98, 115, 101, 116], 46),
    ([98, 112, 117, 115, 104], 47)]
 
+/-- words that skip the rest of their line: namespace open section end -/
+def lineKw : List (List UInt8) :=
+  [[110, 97, 109, 101, 115, 112, 97, 99, 101], [111, 112, 101, 110], [115, 101, 99, 116, 105, 111, 110], [101, 110, 100]]
+/-- words that are dropped: private -/
+def dropKw : List (List UInt8) := [[112, 114, 105, 118, 97, 116, 101]]
+
+/-- the rest after the dash-slash closing a block comment; `d` = comments still open inside it -/
+def blockEnd : Nat → List UInt8 → Option (List UInt8)
+  | _, [] => none
+  | _, [_] => none
+  | d, c :: c' :: r =>
+    if c = 45 ∧ c' = 47 then (if d = 0 then some r else blockEnd (d - 1) r)
+    else if c = 47 ∧ c' = 45 then blockEnd (d + 1) r
+    else blockEnd d (c' :: r)
+
 /-- decimal value mod 2^64 -/
 def numVal (w : List UInt8) : Nat := w.foldl (fun a b => (a * 10 + (b.toNat - 48)) % 2 ^ 64) 0
 /-- 8 little-endian bytes -/
@@ -50,6 +68,12 @@ def step : List UInt8 → Option (List UInt64 × List UInt8)
   | [] => none
   | c :: r =>
     if c == 32 || c == 10 then some ([], r)
+    else if c == 45 && r.head? == some 45 then some ([], r.tail.dropWhile (· != 10))
+    else if c == 47 && r.head? == some 45 then (blockEnd 0 r.tail).map fun t => ([], t)
+    else if c == 64 && r.head? == some 91 then
+      (match r.tail.dropWhile (· != 93) with
+       | [] => none
+       | _ :: t => some ([], t))
     else match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
       | some (s, k) => some ([k], (c :: r).drop s.length)
       | none =>
@@ -57,7 +81,9 @@ def step : List UInt8 → Option (List UInt64 × List UInt8)
         let rest := (c :: r).dropWhile isW
         if isD c then (if w.all isD then some (5 :: le8 (numVal w), rest) else none)
         else if isW c then
-          some ((match kwTable.lookup w with
+          if lineKw.contains w then some ([], rest.dropWhile (· != 10))
+          else if dropKw.contains w then some ([], rest)
+          else some ((match kwTable.lookup w with
                  | some k => [k]
                  | none => 14 :: (w.flatMap fun b => [1, b.toUInt64]) ++ [0]), rest)
         else none
```

### (2) `pOf` and `mC`, branch exp-syntax-match only (Proof/Main/Compile.lean, Proof/Main/Sem.lean)
```diff
+theorem lexesD_det {x : List UInt8} {t t' : List UInt64} (h : DsSpec.LexesD x t) (h' : DsSpec.LexesD x t') : t = t' := by
-/-- the program a text denotes (Lex2Spec, then ParSpec) -/
+/-- the program a text denotes (Lex2Spec, the match desugaring DsSpec, then ParSpec) -/
-  if h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p then some (Classical.choose h) else none
+  if h : ∃ p, ∃ ts, DsSpec.LexesD x ts ∧ ParsesProgram ts p then some (Classical.choose h) else none
-theorem pOf_eq {x : List UInt8} {ts : List UInt64} {p : List DefA} (hl : LexSpec.Lexes x ts) (hp : ParsesProgram ts p) :
+theorem pOf_eq {x : List UInt8} {ts : List UInt64} {p : List DefA} (hl : DsSpec.LexesD x ts) (hp : ParsesProgram ts p) :
-  have h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p := ⟨p, ts, hl, hp⟩
+  have h : ∃ p, ∃ ts, DsSpec.LexesD x ts ∧ ParsesProgram ts p := ⟨p, ts, hl, hp⟩
-    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ Q (mC x) p := by
+    ∃ ts p, DsSpec.LexesD x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ Q (mC x) p := by
-def mC (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.y16 (C.s10 x)))
+def mC (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.y16 (C.t10 (C.s10 x))))
```

The new trusted definitions (`MU`, `MATCH`, `WITH`, `WILD`, `identTok`, `splitTok`, `Pat`, `pat`, `armCode`, `cell`, `go`, `noMatch`, `ds`, `LexesD`) are all of Nano/V2Self/Proof/Lex/DsSpec.lean (≈100 lines). The owner should read that file whole.

**Why `pOf` has to change for `match`.** The lead preferred leaving the statement untouched and proving the desugaring
semantics-preserving inside the proof. That is not possible here. The meaning of a text is `pOf` (lex, then
`refParse`). A text containing `match` lexes to a token stream with the identifier `match`, and `refParse` rejects it
(the S grammar has no such form). So under the old `pOf` every match program has no meaning (`srcRun = none`), and
`Computes`, a premise of `CompileCorrect`, can never hold. The theorem would be true but vacuous for exactly the new
programs. Giving them a meaning means changing the definition of meaning. The change is kept minimal: one extra stage
`ds`, specified independently of C's code. On match-free texts it is the identity, so the meaning of every old program
is unchanged (`DsTok.ds_id`).

## Open owner decisions
1. **Namespaces are flattened** (construct 1). `A.f` and `B.f` collide, and the duplicate-def check rejects them;
   qualified references are rejected. Proper qualified names would cost:
   - lexing `.` inside identifiers (Lean names), `namespace` tracking in a pre-pass, and name resolution
     (current namespace, then `open`ed ones, then the root);
   - in nano this means the desugar stage rewrites each identifier to its fully qualified spelling.
   That is about the size of construct 2 (M: ≈150 lines of C, ≈1k lines of proof), plus a decision on how `open`
   interacts with shadowing.
2. **Accept the `pOf` change** for `match` (above), or keep only construct 1.
3. `match` programs need about 8 MiB more work memory. Packing the cell stack into one word (depth ≤ 31) would halve that.

## Work memory of `match` programs (+8 MiB)
- **Where it comes from.**
  - The generated code allocates every buffer (`bnew`) at the full capacity κ = 2^19 words = 4 MiB and never frees it.
  - `t10` allocates two buffers: the cell stack `s` (one word per paren depth) and the output `o`. The lexer's buffer `t`
    stays live while `o` is written.
  - Measured: `sum.lean` needs 73–76 MiB with the old B2. With match code it needs 81–84 MiB, above the 80 MiB
    default of nanorun, the shims and selfrun.
  - Match-free texts take the `t11` shortcut and allocate nothing, so their need is unchanged; the self-compile passes
    at 80 MiB.
- **Can it be avoided?**
  - *Cell stack (−4 MiB, cheap).* Pack the cells into one UInt64 (2 bits per depth, depth ≤ 31; reject deeper `(`).
    Spec change: `(` fails when `cs.length = 32`. The proof needs bit-field lemmas for `Rep`, about +100 lines.
  - *Output buffer (−4 MiB, larger).* In place is impossible, because the output is longer than the input
    (`| 3 =>` 11 words becomes `else if $ == 3 then` 17 words). But the desugaring is a **streaming** transduction:
    output order is input order with insertions, and the scrutinee is emitted once where it stands. So it could be
    fused into the lexer's emit loop (`s9`), which writes the lexer's single buffer directly. Cost:
    - the trivia/cell state moves into `s9`;
    - `s10_sound` would state `LexesD` directly (Lexes composed with `ds`);
    - this is a restructuring of the Lex2Sound proof (est. M, about 1 day).
  - With both changes, match programs would need no extra memory.

## 3. Index notation (`a[i]!`, `a.size`, `a.push`): not started; estimate and blockers
- **Semantics gap (needs an owner decision first).** nano's `Buf` is `List UInt64` and `bget b i = b.getD i.toNat 0`.
  - Real Lean `a[i]!` needs `a : Array _` (or a `List` with a Nat index) and panics out of range; `bget` returns 0.
  - `a.size` exists for `Array` only (`List` has `.length`).
  - Verbatim Lean source over `Array UInt64` would need either a second prelude, in which `Buf := Array UInt64`
    (B1's BootPrelude already does this), or a spec saying "`a[i]!` means `bget a i` (0 when out of range)", which
    differs from Lean's panic default only on programs that would panic.
- **Mechanics, once decided.**
  - Lexer: `!` and `.` (field access) as new tokens. This is a `LexSpec.step` change, like construct 1; a `.` inside
    an identifier affects qualified names (see the open decisions).
  - Desugar stage (as for match): `x [ e ] !` becomes `bget x (e)`, `x . size` becomes `bsize x`, and `x . push v`
    becomes `bpush x v`. This is a local token rewrite with a one-token lookbehind (an identifier) and bracket matching.
- **Estimate:** C about +80 lines in Dsg; proof about +600 lines (the same pattern as `t9_sound`, with fewer cases),
  plus the lexer cases (about +150). Roughly 4–6 h, after the semantics decision.

### Index notation: semantics options (owner decision; nothing implemented)
In Lean's logic, `a[i]!` out of range **is `default`** (0 for UInt64). The panic is only a runtime message outside the
logic, so a silent 0 agrees with Lean's meaning and with `bget`. Options:
- (i) **Silent default**: `a[i]!` desugars to `bget a i`. Equal to Lean's logical meaning; out-of-range reads give 0
  without notice.
- (ii) **Loud failure**: out of range traps or returns an error status, as the existing `cap` stop does. This is closer
  to the owner's "fail loudly" preference, but it differs from Lean's logical value, so the meaning (`Sem`) would get a
  new stop reason. That is a trusted-definition change and needs proof work in Gen/Machine (a new stop path).
- (iii) **Only proven-in-bounds forms**: accept `a[i]'h` or `if h : i < a.size then a[i] else …` and reject `a[i]!`.
  No semantic gap. The desugar stage drops `h` (a proof term), and the bound check becomes an ordinary `if`.

### Memory reduction attempt (time-boxed, stopped; nothing committed beyond these notes)
- **Tried:** pack the cell stack into one UInt64 (2 bits per depth, depth ≤ 31). With `cget s d = (s >>> (d+d)) &&& 3`
  and `cset s d v = (s - (s &&& (3 <<< (d+d)))) ||| (v <<< (d+d))`, `bv_omega` cannot prove
  `cget (cset s d v) d = v`: the shift amount is a variable. Case-splitting d (32 cases, and 32×31 for the "other
  digit unchanged" lemma) is too slow, and `bv_decide` is not allowed.
- **Workable route, not done:**
  - write the update arithmetically, `cset s d v = s - (cget s d <<< 2d) + (v <<< 2d)`;
  - prove the base-4 digit lemmas in Nat (`S = A·4^{d+1} + c·4^d + R`; digits below/above d are unchanged; standard
    `Nat.add_mul_div` lemmas);
  - change `Rep` to a word, the spec to "`(` fails at depth 32" (a trusted change, to be listed), and the three cell
    updates in `t9_sound`;
  - regenerate Cert/SrcLink/Tests ids.
  Estimate 3–4 h. Gain: **−4 MiB only.** A small program with `match` would then need about 77–80 MiB, so it fits the
  80 MiB default, but just barely.
- **Removing the other 4 MiB** (the output buffer) needs the fused lexer-desugar described above (about 1 day).
- **Recommendation:** if memory matters most, do the fused version directly; it removes both buffers. The packed word
  alone is a half-measure.

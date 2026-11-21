# LEAN_RULES: what Lean 4.34.1 does, against what nano does (branch `lean-rules`, 2026-11-21)

Goal: invariant 1 (ROADMAP): every program nano accepts, Lean 4.34.1 accepts with the same result.
Sources: `leanprover/lean4` tag `v4.34.1`, paths below are under `src/`. Line numbers are of that tag.
Nano under test: the `syntax-1` lexer/desugar/parser specs (`Lex2Spec`, `DsSpec`, `ParSpec`) and the **real compiler binary** `B2.bin` of that
branch (run with `nanorun`). Lean under test: the real 4.34.1 release (`lean`, `#eval m input`, `import Nano.Main.Prelude` for `rd put len' Buf ...`).
Harness and batteries: `Testing/nano/v2self/fuzz/lean_rules/` (README there; `results_run1.txt` = raw output of the 222 hand cases).
Every "test" below is a program that was run on both; "same" means both reject or both give the same bytes.
Compiler/proof code was not touched.

## 0. Mismatches found (nano accepts, Lean rejects or disagrees) — action list

| # | class | example | Lean | nano | test |
|---|---|---|---|---|---|
| M1 | **literal-only arithmetic typed UInt64 (Lean: Nat)** | `if 3 - 4 == 0 then 1 else 2` | Nat: 3-4=0 → `1` | UInt64 wrap → `2` | n11 n12 n16 n17 n23 y02 y05 y06 y09–y11 y13 y15 y17 |
| M2 | huge fuel numeral wraps mod 2^64 | `f 18446744073709551616 0` (loop stops by its own test) | Nat fuel, loop runs: `3` | fuel 0 → Z arm: `0` | n18 |
| M3 | `<--` / `<-` lexed as `<` + comment | `if a <-- c⏎ b then` | token `<-` → parse error | `a < b` accepted | t14 |
| M4 | namespace flattening: name visible after `end` | `namespace A def f.. end A def m := f 1` | `unknown identifier f` | accepted | s01 s12 |
| M5 | `end`/`open` content not checked | `namespace A … end B`; extra `end`; `end` of named section without name; `open Foo` (no such namespace) | errors | accepted | s05 s06 s08 s09 s10 |
| M6 | reserved words accepted as names | `let at := 1`, `def fun`, param `in`, `Type`, `Prop`, `sorry`, `do`, `from`, `by`, … (168 words, §3) | parse error | accepted | i06 i07 i09, `lean_reserved_words.txt` |
| M7 | `_` as a term / def name; char-literal and `'x` names | `let _ := 1; put [] _`; `def _ …`; `let 'a' := 1` | errors | accepted | i01 i02 i03 i05 |
| M8 | root-name clash | `def id (a : UInt64) …` | `id has already been declared` | accepted | i10 |
| M9 | match layout (offside rule) | arm bars at different columns; rhs at a column < its `|`; loop-def arms the same | parse/`Missing cases` error | accepted | m10 m11 d02 d04 |
| M10 | application args / let rhs at column ≤ saved position | `put []⏎1` (arg at col 0); `let a := rd x⏎0;` inside parens; `f 1⏎2` in a match rhs at the bar column | arg not consumed → error | accepted | l05 o13 a1 a2 |
| M11 | duplicate literal arms (incl. mod-2^64 duplicates) | `\| 97 => a \| 97 => b`; `\| 0 => a \| 18446744073709551616 => b` | `Redundant alternative` error | accepted (if-chain) | m02 m03 |
| M12 | shift fragility inside arithmetic trees | `7 + (rd x 1 >>> 2)`, `1 >>> 64`, `3 * (rd x 0 >>> 2)` | elaboration error (§6.4) | accepted | sh2/*, rnd (48 of 120 random programs) |
| M13 | attributes: unknown name; attribute not at a def; `implemented_by` | `@[bogus] def`, `private @[inline] def`, `@[extern f] def`, `@[implemented_by g] def f` (**different result**) | errors / `f 1 = 0x65` | accepted, ignored | d28 d29 d34 d36 |
| M14 | trivia in impossible positions (documented superset) | `put [] (/-- d -/ 1)`, `put [] (@[inline] 1)`, `put [] (private 1)` | parse error | accepted | t06 t19 d18 |

M1, M2, M13(`implemented_by`) are **miscompiles** (accepted, different value). M3 is a semantics-bearing lexer difference. The rest are
accepted-but-invalid (superset). Everything else probed agrees or is nano-stricter (§7 lists the nano-stricter set, which is harmless).

Suggested fixes, in order of value: (a) M1: reject, or type as Nat, any arithmetic/comparison subtree whose leaves are all numerals when it is not the direct
argument of a UInt64 position (§6.1); simplest sound rule: **reject a numeral-only operand in an `if` condition, `let`/tuple value or `match` scrutinee; allow it
only where a UInt64 is expected (call/put argument, `put`, `if` branch result)**. (b) M2: reject fuel numerals ≥ 2^64 (the lexer wraps every numeral mod 2^64; a numeral
≥ 2^64 is only equal in a UInt64 position — safest is to reject any numeral ≥ 2^64 outright). (c) M3: lex `<-`-prefix: reject `<` immediately followed by `-`
(also `<` `|`, `<` `$`: any Lean token that has an nano operator as proper prefix: §2.3). (d) M4/M5: make `namespace`/`section`/`end`/`open` real (scope stack, name check,
`open` only of existing namespaces) or reject the program unless every `end` closes its opener and nothing declared inside a namespace is used outside by its short name.
(e) M6/M7/M8: lexer rejects the reserved word list, bare `_` outside binder/`match` arms, and names starting with `'`; reject defs named like an Init root
constant (`id`, `ite`, `dite`, `and`, `or`, `not`, `xor`, …: any name declared in `Init` at root, §3.3). (f) M9–M11: implement the layout rule of §5 (a column check on `|`, rhs and
application arguments; all three are `column`-only conditions on tokens) and the redundancy check (reject duplicate literal arms after mod 2^64). (g) M12: reject a shift
whose result is an operand of `+ - * ||| &&&` when a numeral operand lies to its left in the same tree (§6.4), or parenthesize/let-bind during desugaring. (h) M13: lexer
accepts only attribute names that Lean knows and are semantics-free for a def (`inline`, `noinline`, `specialize`, `reducible`, `simp`, `macro_inline`, `export x`?: test each);
reject `implemented_by`, `extern`, `export`, `init`, `csimp`, `instance`, `default_instance`… Safest: accept only `@[inline]`, `@[noinline]`, `@[simp]`, `@[reducible]`.

## 1. Whitespace and comments

| Lean rule | Cite | nano | test |
|---|---|---|---|
| Whitespace between tokens: `Char.isWhitespace` = space, `\n` (and `\t`, `\r`, which are then rejected). Tab → error "tabs are not allowed"; isolated `\r` → error. | Parser/Basic.lean:563–590 (`whitespace`) | space, `\n` only; every other byte (tab, CR, FF, VT, NBSP) rejected — stricter | t10 t12 t21 t22 |
| `\r\n` is accepted: the frontend normalises line endings before parsing (positions preserved) | Parser/Extension.lean:458–468 (`crlfToLf`) | **rejects** CRLF files outside comments (stricter; inside `--` comments CR is fine, t13) | t12 t23 |
| `--` line comment: consumed by `whitespace` only, i.e. *after a token or at a token boundary*; runs to `\n` (excluded) | Basic.lean:575–578 (`takeUntilFn (· = '\n')`) | `step`: `--` anywhere a token may start | t01 t11 t16 t17 |
| Block comment `/- … -/`, nesting counted (`/-` opens, `-/` closes; the pair is recognised on a 2-char window so `/-/` and `--/` behave as shown) | Basic.lean:537–561 (`finishCommentBlock`), 580–588 | `blockEnd` (same 2-char window) | t02 t03 t04 t18 |
| `/--` and `/-!` are **tokens** (doc comment / module doc), not whitespace; they parse only where a docComment/moduleDoc is allowed: before `def`/`theorem`/… (`declModifiers`), as a command (`/-! … -/`). Mid-expression → error. | Basic.lean:583–585 (`curr == '-' \|\| '!' then s`), Parser/Term.lean:91 (`docComment`), Command.lean:60 (`moduleDoc`), 114–115 | treated as comments anywhere (**M14**, documented) | t05 t06 t07 |
| Unterminated block comment → error "unterminated comment" | Basic.lean:560 (`eoi`) | rejected | t08 |
| A comment cannot hide a *later* char of a multi-char token; but a comment *start* directly after a token prefix wins over a longer token only if the token has already ended: tokens are taken longest-first **before** whitespace is looked at. So `<--` is token `<-` then `-`, **not** `<` + comment | Basic.lean:1027–1055 (`tokenFnAux`: `matchPrefix` of the token table), 943–957 (`mkTokenAndFixPos` then `whitespace`) | `<` then `--` comment (**M3**) | t14 t15 |

Edge table (Lean result = nano result unless noted): `a --b` comment; `a--b` comment (ident then whitespace); `+--c` token `+` then comment; `x<-/ c -/ y`
Lean: token `<-`, hence error; `x </- c -/ y` fine in both; `/- --/` closes; `/-/ x -/` closes at the last `-/`; `-- /-` line comment wins; `/- -- -/` closes at `-/`.

## 2. Tokens

### 2.1 Identifiers
Rule (Lean): first char `isIdFirst` = ASCII letter, `_`, or a letter-like char (Greek except λ Π Σ, Coptic, Latin‑1/Ext‑A letters, script letters, …);
rest `isIdRest` = alphanumeric, `_`, `'`, **`!`, `?`**, letter-like, subscripts. A `.` followed by an idFirst/`«` continues the name (`A.f`). `«…»` escapes any text.
Cite: Init/Meta/Defs.lean:101–142; Parser/Basic.lean:921–931 (`isIdCont`), 975–1010 (`identFnAux`).
An identifier that is also a **token** (keyword) is the token if the token is at least as long as the identifier: `isToken` Basic.lean:934–941; so `fun`, `at`, … cannot be names, `fun1`, `at'`, `end'` can.
nano: word = maximal `[A-Za-z0-9_']*`; digit-first words are numerals; `.`, `!`, `?`, `«»`, non-ASCII are rejected (stricter, harmless: t i18–i20).
**Mismatches**
* A word starting with `'`: Lean reads a char literal (`curr == '\'' && getNext != '\''`, Basic.lean:1030) → `let 'a' := 1` is a type error and `let 'x := 1` "missing end of character literal"; nano reads the identifier `'a'`/`'x` (M7; i01 i02). Fix: reject words starting with `'`.
* `_`: Lean's `_` is the hole token. `let _ := 1; …` is fine, a *use* of `_` is "don't know how to synthesize placeholder", `def _` is a parse error; a param `(_ : UInt64)` is fine (i03 i04 i05). nano treats `_` as an ordinary name (M7). Fix: `_` only as a binder/pattern, never as a term or def name.
* Reserved words: see §3.
* Digits inside: `f1x`, `a''`, `f'` are ordinary in both (i13 i21).

### 2.2 Numerals
Lean numeric literal forms: decimal `d(_*d)*` (underscores allowed between digits, repeated), `0x`/`0X` hex, `0b`/`0B` binary, `0o`/`0O` octal (also with `_`), scientific `1.5`, `1e3`, `1.` (+ the "bare dot before identifier" error), char/string literals.
Cite: Basic.lean:817–839 (`takeDigitsFn`), 831–882 (`decimalNumberFn`, scientific), 884–898 (bin/oct/hex), 900–917 (`numberFnAux`). A numeral followed by an identifier char is *two tokens* (`1a` = `1`, `a`; error as an application `1 a`). Leading zeros are decimal (`007 = 7`).
Typing: a numeral is `OfNat ?α n` with `?α` unknown until unified or defaulted; the default instance `instOfNatNat` (priority 100) makes it `Nat` — Init/Prelude.lean:1280–1281. `UInt64` literal: `instance : OfNat UInt64 n := ⟨UInt64.ofNat n⟩`, `UInt64.ofNat n = ⟨BitVec.ofNat 64 n⟩`: **wraps mod 2^64** (Init/Data/UInt/BasicAux.lean:255–261, 339). `(100000000000000000000 : UInt64) = 7766279631452241920`.
nano: decimal digits only, value mod 2^64 stored as `UInt64` (`numVal`); `0x…`, `0b…`, `0o…`, `1_000`, `1e3`, `1.5`, `1a` all rejected (stricter; n03–n09, same or nano-stricter).
Agreement in a UInt64 position (n01 n02 n10 `put [] 256+65 = 0x41`). **Disagreement**: M1 (§6.1) and M2 (§6.2).

### 2.3 Operators and punctuation: longest match of the *Lean* token table
nano ops: `( ) : := + - * ; , | < [ ] => == ||| &&& <<< >>> → × ` (and `||| &&& <<< >>>` triple chars).
Rule: Lean takes the longest token in its table at the current position (`matchPrefix`, Basic.lean:1049–1054) **before** looking at comments. Therefore any text in which a nano operator is a proper prefix of a longer Lean token lexes differently in Lean. Verified by test: `<` + `-` = `<-` (M3, t14); `</-` (t15) is fine. Known tokens that have a nano op as prefix (nano rejects all of them already, because the next char is not a nano token): `<` + `|` = `<|`, `<` + `$`, `<` + `=` (`<=`, nano has no `=`), `|` + `|` (`||`), `=` `=` `=`, `=` `>`, `-` `>` (`->`), `:` `=`, `:` `:` (`::`), `[` `]` (nano takes `[]` as one atom; Lean `[]` is `List.nil`), `+` `+` (`++`), `*` `*`?, `&&` , `^^^`, `>>` `=`. nano rejects these because the second char is not an nano token — **except `<-`, which survives because `-` starts a nano comment**. Fix: nano must reject `<` immediately followed by `-`, `|`, `$` (and any other char that starts a Lean token with prefix `<`, e.g. `<=`, `<>`, `<;>`, `<*>`).
Whitespace is required nowhere between these tokens in Lean (`a<b` ok) except where tokens would merge.

## 3. Reserved words

Lean's token table (`parserExtension` tokens) contains every keyword; an identifier that is a token is not an identifier. I extracted the identifier-like tokens of a full `import Lean` environment (219) and tested each as a `let` name, a parameter name and a def name under Init only (`toks.lean`, `kwscan.py`): **190 are rejected in all three positions**, identical in each (`lean_reserved_words.txt`). 168 of these are lexed by nano as ordinary names (`nano_accepts_reserved.txt`; M6), e.g.
`at by do fun from have in for mut return where with try show Type Prop Sort sorry instance structure theorem example class inductive local meta public export extends deriving exists forall unless until while repeat break continue calc catch finally suffices syntax macro notation prefix infix postfix opaque partial protected noncomputable nonrec unsafe universe variable mutual set_option termination_by decreasing_by using hiding renaming nomatch nofun nat_lit initialize attribute axiom abbrev import include omit …`
(`!`/`?` tokens such as `assert!`, `by?`, `f!` cannot be lexed by nano at all). nano already treats `def let if then else namespace open section end private` specially, and `match`/`with` via the desugar stage.
Non-reserved although they look like keywords: tactic names (`exact intro simp rfl omega …` are `nonReservedSymbol`s), `true false`, `deriving`'s siblings are reserved (see list). Case matters (`Type` reserved, `type` not).
**Test**: `let at := 1; put [] at` → Lean "unexpected token 'at'"; nano accepts (i06, i07 `def fun`, i09 param `in`).
### 3.2 nano-only keywords (nano stricter, harmless)
`UInt64 Nat Buf List UInt8 len' rd len put bnew bsize bget bset bpush` are tags in nano's lexer, so user defs of these names are rejected (i12); in Lean they are ordinary names (the Prelude declares `rd len put len' Buf bnew …`, so redefinition is also an error there).
### 3.3 Root-name clashes (M8)
A top-level `def n` is `_root_.n`; Lean rejects it if `n` is already a root declaration of `Init` (`id has already been declared`, i10). `def max` was accepted (i11: `max` is `Max.max`, exported, not a root constant). nano has no knowledge of Init. Fuzzers must avoid generated def names that exist at root: single letters/digits (`a`…`z`, `f1`, `x_2`) are safe; avoid `id ite dite and or not xor min? (ok) cast absurd ...`. Check with `#check @name` at generation time or restrict def names to `[a-z][0-9_']*`.

## 4. Declarations, modifiers, attributes, namespaces

`declaration := declModifiers >> (abbrev|def|theorem|instance|…)` Parser/Command.lean:302; `declModifiers := optional docComment >> optional «attributes» >> optional visibility >> optional «protected» >> optional (meta <|> noncomputable) >> optional unsafe >> optional (partial <|> nonrec)` Command.lean:114–121; `visibility := private | public` Command.lean:70–72.
**Order is fixed**: doc comment, attributes, `private`/`public`, `protected`, `meta`/`noncomputable`, `unsafe`, `partial`/`nonrec`. So `@[inline] private def` is valid, `private @[inline] def` is a parse error (d34, M13).
`@[…]`: `"@[" >> withoutPosition (sepBy1 attrInstance ", ") >> "]"` Parser/Term.lean:588–591; the attribute **name must exist**: Elab/Attributes.lean:61–63 `Unknown attribute `[bogus]``; some attributes take arguments (`export f`, `extern "c" `—string required, d36).
* `@[inline]`, `@[noinline]`, `@[simp]`, `@[specialize]`, `@[reducible]`, `@[export my_f]` all accepted by Lean and semantics-free for `#eval` results (d27 d30 d31 d32 d35).
* `@[implemented_by g] def f` replaces the *compiled* body of `f` by `g`: `f 1` evaluates `g 1` (d29: Lean `0x65`, nano `0x02`). nano's `attrEnd` accepts any names/commas/spaces. Must reject (M13).
* An attribute list cannot contain a comment hiding `]` in nano; Lean allows `@[inline -- ]⏎]` (d33, nano stricter).
`private def` accepted in both (d17); `protected def` outside a namespace: Lean error, nano rejects (d19); `noncomputable def f` is accepted as a declaration but `#eval`/compilation of `m` then fails (`dependsOnNoncomputable`), so it is not usable in a program; nano rejects (d20); `abbrev`, `theorem`, `#eval`, `set_option … in`, `universe`, `variable`, `where`, `partial def`, `fun`, `let x : T :=`, implicit binders, return type omission, curried `A → B → C` returns: all valid Lean and rejected by nano (stricter, d13–d16 d21–d26 s20–s22 p15, l04). When they are added, the Lean rules are: `partial def` needs `Inhabited` result type and no termination proof (d14: value computed by the compiled loop); `where` binds local defs after the body, visible in the body and each other (d13); return type omitted is inferred (d15).
### 4.1 `namespace` / `section` / `end` / `open`
Lean (Parser/Command.lean:320 `section`, 338 `namespace`, 358 `end`, 745–758 `open`; Elab/BuiltinCommand.lean:101 `elabNamespace`, 106 `elabSection`, 241 `elabEnd`, 312 `elabOpen`):
* `namespace A.B` opens the scopes `A` and `A.B` at once; `end` must name the scope(s) exactly: `end B` for `namespace A.B` is accepted only when followed by `end A`; the name check errors are at BuiltinCommand.lean:183 (no scope), 189 (missing name), 216, 233 (mismatch), 239 (unexpected name on an unnamed section). Missing `end` at end of file is **fine** (s07).
* Everything declared inside `namespace A` is `A.x`; unqualified `x` resolves **only inside** `A` (or after `open A`); after `end A` the short name is unknown (**M4**: s01, s12 — also `def m` declared inside a namespace is `A.m`, so the program has no `m`; nano flattens and accepts).
* `section` has no effect on names. `open A` brings `A.x` into scope until the end of the enclosing scope; `open Nat` etc. is allowed (s18; may create ambiguity with user names). `open Foo` with no such namespace: `unknown namespace`  (M5; s08). `open A in <cmd>` and `open A (f)`, `hiding`, `renaming` are valid Lean; nano's line-eater accepts only the plain form and rejects `in` (SYNTAX_EXP lineOk).
* The name after `end` is parsed with `checkColGt`; a comment between `end` and its name is allowed (s17).
* Shadowing: inside `namespace A`, `def f` shadows root `f` for later uses inside A (s19, nano rejects: duplicate def after flattening).
nano: `lineKw` words drop the rest of their line; the content is only checked to be names/dots/spaces without `in` (`lineOk`). So: `end B` for `namespace A` (s05), extra `end` (s06), `section S … end` (s09), `section … end S` (s10), `open Foo` (s08) are accepted, and flattening makes names inside a namespace visible outside (s01, s12). All five are Lean errors. A faithful rule in nano needs: a scope stack with names, `end` must match, qualified names are prefixes. Until then restrict nano to `namespace`-free programs, or accept `namespace A … end A` only if no def inside is referenced outside (and `m` is not inside).

## 5. Layout (offside rule) — exact column rules

Lean has no global layout rule. Layout exists only where a parser uses `withPosition` (saves the position of the current token) plus `checkColGe`/`checkColGt`/`checkColEq`/`checkLineEq`, which compare the **column of the next token** with the saved one (Basic.lean:1496–1561 `checkColGeFn/GtFn/…`, 1571 `withPosition`, 1583 `withoutPosition`; Parser/Extra.lean:184–204 `many1Indent`/`manyIndent`/`sepByIndent` = `withPosition((colGe p)*)`). The saved position is *dynamic*: parentheses, `@[ ]` and bracketed binders reset it (`withoutPosition`) — so inside `( … )` there is no column constraint relative to anything outside (a5/a6 same).
Rules that matter for nano's syntax (all `col` = zero-based column of the token's first byte):
1. **Application arguments**: every argument must satisfy `colGt` against the saved position (Parser/Term.lean:889–893 `argument := checkWsBefore >> checkColGt "expected to be indented" >> …`). At the top level of a command the saved position is the command start (column of `def`, normally 0): an argument on a following line at col 0 is *not* an argument (parse then fails/continues as a new command). Within `let x := f⏎ y`, the saved position is the `let` token (`withPosition ("let" …)`, Term.lean:551–552); within a match alternative it is the first `|` of the match (matchAlts). Tests: l05 `put []⏎1` (Lean error `Type mismatch`: `put []` alone), o13 (`put []⏎(if…)`), a1 (`let a := rd x⏎0;` inside parens, `0` at col ≤ `let` col → `unexpected token ';'`), a2 (`| 97 => f 1⏎  2⏎  | _ => 3`, `2` at the bar column → error). nano accepts all (M10). Passing: args at col ≥ 1 under a col-0 `def` (a6, a7); binary operators at col 0 (`+ 2`, l07) never need colGt.
2. **Match / loop-def alternatives** (`matchAlts := withPosition (many1Indent (ppLine >> matchAlt))`, Term.lean:266–281): all `|` must be at column **≥ the column of the first `|`**; a later `|` at a smaller column ends the alternatives (then `| …` is unexpected: m10 "unexpected token '|'", d02 "Missing cases"). The right-hand side must start at column ≥ the column of **its own** `|` (`checkColGe`, Term.lean:270; m11, d04: "expected alternative right-hand-side to start in a column greater than or equal to the corresponding '|'"). The first `|` itself may be at any column including 0 (d03, m21 same) and several alternatives may share a line (d05, m12). The same function parses `def f : T → … | 0, … => … | n+1, … => …` (`declValEqns`, Command.lean:184).
3. `if c then t else e` has **no** column rule (a4, o13 variant: `then`/`else` at col 0 fine; a3 inside a `let` too). `else` binds to the nearest `if` (o09); the else branch extends as far right as possible (`else 2 + rd x 1` = `else (2 + …)`, o10); `if` as a binary operand needs parentheses in nano but not in Lean (o11: nano stricter).
4. `let x := v; b` / newline: the separator is `;` or a line break (`optSemicolon`, Term.lean:100–121 `semicolonOrLinebreak = ";" <|> checkLinebreakBefore`). nano requires `;` (l01 l09 nano stricter). `let (a, b) := v; e` is allowed (pattern let; l03 l14). The body of a `let` at col ≤ the `let` col is fine (a8/a9: stricter in nano).
5. `where`, `termination_by`, `decreasing_by`: `where` is parsed after the body with `sepByIndent` (Term.lean:742): `where` decls at the same column.
6. Command boundary: a command ends where the term parser cannot continue; `def a … := v def m …` on one line is fine in Lean (l10), and `def a := v⏎def …` as well; nano: l11 (stricter).
**Proposed nano rule** (single pass, no re-parse): keep per-construct saved columns: command start (col of `def`), `let` token col, first-`|` col, reset to "none" at `(`; check `col(next arg) > saved` for arguments and `col(rhs) ≥ col(own bar)`, `col(bar) ≥ col(first bar)`. The token stream needs one extra word (the column) per token.

## 6. Operators, precedence, typing

### 6.1 Table (Init/Notation.lean:272–294, 376–394, 412–414; all `binop%` unless noted — lines 302–313)
| op | prec | assoc | Lean elaborator |
|---|---|---|---|
| `\|\|\|` | 55 | left | `binop%` |
| `^^^` | 58 | left | `binop%` (nano: no) |
| `&&&` | 60 | left | `binop%` |
| `+` `-` | 65 | left | `binop%` |
| `*` `/` `%` | 70 | left | `binop%` |
| `<<<` `>>>` | 75 | left | **plain** `HShiftLeft.hShiftLeft` (not `binop%`) — §6.4 |
| unary `-` | 75 (arg 75) | prefix | `unop%` (nano: no) |
| `^` | 80 | **right** | `rightact%` (Notation.lean:311; nano: no) |
| `==` `<` `>` `<=` `>=` `=` `!=` | 50 | **non-assoc** (`infix`): `a == b == c` is a parse error (o05 o06 same) | `binrel_no_prop%` (`==`), `binrel%` |
| `&&` `\|\|` | 35 / 30 | left | plain (nano: no) |
| `×` (type) | 35 | right | `Prod` |
| `→` (type) | 25 | right | arrow |
Nano's table `opInfo` (ParSpec.lean) agrees on precedence/associativity for `|||55 &&&60 +65 -65 *70 <<<75 >>>75` and on non-associativity of `==`/`<` (comparison is only allowed as the condition of `if`, as `A (==|<) B`). 120 random trees (`rnd_expr.py`) and o01–o04 agree on results whenever Lean accepts. `if A == B` is `Bool`→`Prop` coercion with `Decidable`; `<` needs `Decidable (a < b)` — fine on UInt64.
Application binds tighter than any operator (o23), `put [] a + 1`-style juxtaposition: nano's prims take **atoms** only; Lean's application takes arguments at precedence `arg` (max): `put [] (a + 1)` needs the parentheses in both.

### 6.2 Literal typing (the main semantic risk) — Lean/Elab/Extra.lean
`binop%/binrel%` trees (Elab/Extra.lean:183–230 `toTree`, 249–314 `analyze`, 415–452 `applyCoe`, 456–470 `toExpr`): leaves are elaborated **without** expected type; a numeral leaf has type `?α` (unknown). If the leaves contain a known type (`UInt64`), unknown leaves are unified with it (so `3 - 4 + rd x 0` is UInt64, n15 same, and `let a := 3; a - 4 + rd x 0` is UInt64, n13 same). If **no leaf has a known type** (`max? = none`) the tree is elaborated with nothing unified, the default instance fires and the numerals become **Nat**: Nat subtraction truncates (`3 - 4 = 0`), Nat never overflows (`18446744073709551615 + 2 = 18446744073709551617`), `1 <<< 64 = 2^64`, `5 < 0 - 1` is `5 < 0`. The *expected* type seeds `max?` (Extra.lean:256–263): so `put [] (3 - 4)` (argument position of a UInt64 parameter) is UInt64 = 255 (n14 same), but `if 3 - 4 == 0` has no expected type (`==` is `binrel_no_prop%`, both sides are one tree) → Nat (n11 n12 y02 y17, **M1**).
Where an all-literal tree gets its type, per position: UInt64 call/`put`/prim argument and `if` branch result: expected UInt64 → UInt64 (n14 y07 y08 same) · `if` condition operands (both sides literal-only): Nat (**M1**) · `let x := lit-tree`: type decided when `x` is first used: `x` later unified with a UInt64 (`b + rd x 3`) → UInt64 (y16 same), used only in a comparison or nowhere → Nat (y02 y15 y17 **M1**), used in `put`/`if`-branch → UInt64 (y18 same) — order dependent! · tuple/pair components: same as `let` (y06) · `match` scrutinee `match 3 - 4 with …` → Nat (y05, M1) · fuel/loop initial state: expected UInt64 → UInt64 (y19 same).
nano: `Ty.lit` = "numeral (UInt64 or Nat)"; any `+ - * ||| &&& <<< >>>` over `.lit` is typed `.s .uw` (ParSpec `pLoop`). So nano always computes literal-only trees in UInt64: wrong wherever Lean says Nat and the value differs: subtraction below 0, any overflow ≥ 2^64 (add, mul, shifts ≥ 64, numerals ≥ 2^64), and the result is then used in `if`/`match`.
Differential tests (nano / Lean): `if 3 - 4 == 0 then 1 else 2` → 02 / 01; `if 1 <<< 64 == 1 then 1 else 2` → 01 / 02; `if 18446744073709551616 == 0 then 1 else 2` → 01 / 02; `if 18446744073709551615 + 2 == 1 then 1 else 2` → 01 / 02; `if 5 < 3 - 4 then 1 else 2` → 01 / 02; `match 3 - 4 with | 0 => 1 | _ => 2` → 02 / 01; `let a := 5; let b := a - 6; if b < 1 then 1 else 2` → 02 / 01; `let a := 5; if a - 6 == 0 then 1 else 2` → 02 / 01.
Rule for the fuzzer/compiler: a **maximal** operator tree whose leaves are all numerals is Nat unless it is directly an argument of a UInt64 position; mixed trees (≥ 1 UInt64 leaf anywhere in the tree, parentheses are transparent) are UInt64.
### 6.3 Fuel numerals and `Nat` (M2)
`f 18446744073709551616 0` passes the numeral as a **Nat** to the `Nat` fuel parameter (no wrap): fuel is 2^64 and the loop runs until its own test stops it (`3`); nano reduces the numeral mod 2^64 = 0 and runs the Z arm (`0`) (n18). Fix: reject numerals ≥ 2^64 everywhere, or at least in fuel position. (Fuel numerals < 2^64 agree, n19.) `len' x` is Nat in both.
### 6.4 Shifts
`x <<< k`, `x >>> k`: `UInt64.shiftLeft a b = a <<< (b % 64)` (Init/Data/UInt/Basic.lean:673, 680): `1 <<< 64 = 1`, `1 <<< 65 = 2`, `8 >>> 66 = 2`, shift by a UInt64 `200` = by 8. nano: rhs must be a numeral and `x <<< 64` agrees (n20 n21 same; shift by a variable is accepted by Lean (n22), rejected by nano). **Elaboration quirk**: `<<<`/`>>>` are *not* `binop%` (Notation.lean:289–290 vs 302–313): the shift is a *leaf* of the surrounding `+ - * ||| &&&` tree whose type is an unresolved mvar until its own numeral rhs is defaulted; elaborating that rhs runs default instances on every pending mvar, which turns an already elaborated **numeral leaf to its left** into `Nat`, and then `HAdd Nat UInt64 _` fails. Exhaustive 3-leaf enumeration (486 trees, leaves `rd x 0`, `7`, `(rd x 1 >>> 2)`, ops `+ * |||`, both bracketings): **Lean rejects exactly when some numeral leaf precedes (in source order) a shift leaf in the same tree** (rows `nns nsn nsv nvs vns` fail 9/9; `nss` 6/9, 5/9; every pattern with all shifts before all numerals, or no numeral, passes). Examples (Lean: error; nano: accepted): `7 + (rd x 1 >>> 2)`, `3 * (rd x 0 >>> 2)`, `65535 * rd x 0 ||| rd x 1 >>> 2`, `1 >>> 64`, `65535 == (rd x 3 >>> 65)` (M12). A shift whose lhs is an all-literal tree is Nat (`put [] (1 >>> 64)` is a type error, D). Passing: `(rd x 3 + rd x 0) >>> 64`, `rd x 0 >>> 2 + 1`, `(rd x 1 >>> 2) + 7`, `rd x 0 >>> 2 >>> 3`, `((rd x 0 + 1) >>> 2) + rd x 1`.
Fix for nano: reject, or rewrite by let-binding the shift (`let t := rd x 1 >>> 2; 7 + t` — a `let` value is its own elaboration, defaulting is applied to `t`'s rhs numeral only after unification… verify with the harness) any shift appearing to the right of a numeral leaf of the same tree.
### 6.5 Truncated subtraction, division, overflow (for the planned `Nat`/`/`/`%`; Lean-only evaluation)
`#eval` on 4.34.1: `(5:Nat)-7 = 0`, `(7:Nat)/0 = 0`, `(7:Nat)%0 = 7`; `(5:UInt64)-7 = 18446744073709551614`, `(7:UInt64)/0 = 0`, `(7:UInt64)%0 = 7`, `(0:UInt64)-1 = 18446744073709551615`; `(4294967296:UInt64)*4294967296 = 0`, `(18446744073709551615:UInt64)+1 = 0`, `(2:UInt64)^64 = 0`; `(300:UInt64).toUInt8 = 44` (so `put` truncates), `(18446744073709551616:Nat).toUInt64 = 0`, `(255:UInt8)+1 = 0`, `(0:UInt8)-1 = 255`; `Nat.log2 0 = 0`; `Int`: `-7/2 = -4`, `-7%2 = 1`, `7/(-2) = -3`, `7%(-2) = 1`, `7/0 = 0`, `7%0 = 7`, `Int.tdiv (-7) 2 = -3` (`/` is Euclidean `Int.ediv`, not C). Cites: Nat: Init/Data/Nat/Div/Basic.lean:180 (`mod_zero`), 273 (`div_zero`); UInt64: Init/Data/UInt/Basic.lean:580–680 (`add sub mul div mod` via BitVec `udiv/umod`; `UInt64.mod 4 0 = 4` doc at 629), `UInt64.ofNat` BasicAux.lean:261. `Nat` ops never overflow; `Nat.sub` truncates; `x / 0 = 0` and `x % 0 = x` for Nat, UInt64 and Int.
Out-of-range prims (nano and Lean agree, Prelude semantics): `rd x i` beyond the end = 0 (p01), index wraps mod 2^64 (`rd x 2^64 = rd x 0`, p08), `bget` OOB = 0 (p02), `bset` OOB = no-op (p03 p04 p07: size unchanged), `put` truncates to a byte (p05). All same.

## 7. Control flow, definitions, match (nano-supported subset)
* `if c then t else e`: Parser `termIfThenElse` Init/Notation.lean:485–493 → `ite` with `Decidable c`; `then`/`else` mandatory; `else if` chains right-nest. Agree (o09–o13, a3 a4).
* `let x := v; b` / `let (a, b) := v; b` (Term.lean:551, 455–487 `letDecl`: `letPatDecl` for patterns): sequential scoping (`let a := 1; let a := a + 1` = 2, i17 same); the pattern `let (a, b)` is a `match`; shadowing a def by a param/let is normal (i16 same); duplicate param names `(a a : T)`: the **later** binder wins in Lean and in nano (i14 i15 same).
* `match e with | p => r | …`: Term.lean:331–333; patterns: numerals (UInt64 literal patterns compare `==` modulo 2^64: `| 18446744073709551618 =>` matches 2, m04 same), `_`, a variable, a tuple pattern. **Redundancy is an error** (Elab/Match.lean:1033–1063 `lean.redundantMatchAlt`): `| 97 => a | 97 => b` and `| 0 => a | 18446744073709551616 => b` are rejected (m02 m03, **M11**), an arm after `_`/variable too (m08: nano rejects, same). **Missing cases are an error**: a literal-only match without `_` (m09 same). nano-stricter (fine): `| 96 + 1 =>`, `| 97 | 98 =>`, a variable arm whose name is a def, pair patterns after the first arm (m16 m17 m18 m22). `match` as the whole body at the end of a def, arms at col 0 or indented: same (m20 m21). Nested unparenthesised match: the inner match swallows the following arms in Lean (m14 Lean: redundant alternative; nano rejects). Parenthesise.
* `def` forms: see §4; recursion: Lean needs structural/wf termination: `| n+1, … => f n …` is structural on the fuel; `f (n+1) …` is rejected (d08 same); callee-before-caller order (d09 same); non-tail self-calls are valid Lean (d10: nano stricter, fine); swapped arm order is valid Lean (d06 nano stricter).
* Entry point: `m : List UInt8 → List UInt8` must exist at root (d11 d12 same, s12 M4).
### nano-stricter set (harmless, listed so that fuzzers do not count them as findings)
CRLF; tabs; `n ≥ 2^64`? (no: nano wraps, see M2); `0x 0b 0o _ e .`; `!= <= > >= && / % ^ ^^^`, unary `-`; `if` as operand; `let` without `;`, typed `let`; `where partial abbrev theorem #eval set_option universe variable fun`; curried def results; `open … in`, `hiding`, qualified names; names with `. ! ? « »` or non-ASCII; `let` pattern deeper than a pair; `match` patterns beyond literal/`_`/var/first-arm pair; loop arms in other order; same-line `def`s (l11).

## 8. Grammar and generator spec for the fuzzers

### 8.1 Oracle
Accept = `lean` exit 0 with no `error` and (for result checks) `#eval m input` bytes. Reject on any elaboration error; **`sorry`/warnings**: warnings are fine, an `#eval` that aborts because the body depends on `sorry` is a rejection. nano accept ⇒ Lean accept ∧ same bytes (`diff.py` classifies `NANO-ACCEPTS-LEAN-REJECTS`, `RESULT-DIFF`). Every case above is a regression test; the files regenerate with `gen_trivia_ops.py`, `gen_match_defs_ns.py`, `rnd_expr.py`.

### 8.2 Token-level generator
Alphabet: identifier chars `[A-Za-z0-9_']`, ops of §2.3 and the following *must be generated deliberately*: (1) every Lean token that has a nano op as proper prefix (`<-`, `<|`, `<=`, `<$>`, `==>`... after `<`/`|`/`=`/`:`/`-`/`+`/`*`/`&`/`>`/`[`), also split by a comment: `<--`, `<-/`, `==-/`, `:=--`, `x/-c-/y`; (2) the 168 reserved words as names in every binder position (`let`, param, def, loop-arm var, pattern var, match var arm); (3) `_`, `'a'`, `'x`, `_x`, `x_`, `x'`, `x''`, a 1-char and a 300-char name; (4) numerals: 0, 1, 255, 256, 2^32, 2^63, 2^64−1, 2^64, 2^64+1, 10^20, `007`, `0x1F`, `1_0`, `1e3`, `1.0`, `5.`, `1a` (reject expected), in UInt64 and in Nat (fuel) positions, in literal-only operator trees; (5) trivia: `--` at EOF without newline, `/-`/`-/` in every nesting depth, `/--/`, `/-/`, `/---/`, `--/`, `/-!-/`, doc/module doc at command and mid-expression positions, unterminated, `\t`, `\r`, `\r\n`, NUL, BOM, NBSP, FF, VT, UTF-8 inside comments (valid and invalid), 1 MB comment; (6) `@[…]` with 0/1/2/N attrs, unknown names, args, string args, before/after `private`, mid-expression, with comment-hidden `]`; (7) namespaces: nesting depth 0..3, dotted names, `end` mismatch/missing/extra, same-line `namespace A def …`, `open` of existing/non-existing/`Nat`, `open … in`, def inside namespace referenced short/qualified/outside, two namespaces with equal member names, `end` name on next line (indented or col 0).
Layout mutations (on any generated program): replace a newline+indent by any of {same col, col 0, col+1, col−1 relative to the construct's saved column}; move `|`, rhs, args, `then`, `else`, `with`; join/split lines at every token boundary.
### 8.3 AST-level generator (type-directed; every node is checked against §6)
```
prog   := defs ; def m (x : List UInt8) : List UInt8 := body
expr_U := lit_U | var | rd x e_U | f args | put-free prims | (expr_U op_U expr_U) | e_U << k | e_U >> k   -- k numeral 0..130 (shift by ≥64 wraps)
        | if cond then expr_U else expr_U | let v := expr_U; expr_U | match expr_U with arms | let (a,b) := (e,e); expr
cond   := e_U (==|<) e_U                       -- UNIFIED tree: mixes of var and literal leaves are UInt64; ALL-literal both sides is Nat (M1)
lit_U  := numeral in {0,1,255,256,2^32,2^63,2^64-1,2^64,2^64+1,...}  mod 2^64 only in UInt64-position
arms   := (n_lit => e)* (_|var => e)           -- distinct n_lit mod 2^64 (else Lean "redundant")
```
Edge nodes to force: (a) literal-only operator trees in cond / let value / tuple / scrutinee (M1) with `-` below zero, `*`/`+` crossing 2^64, `<<<` ≥ 64, numerals ≥ 2^64; (b) a numeral **before** a shift inside one tree (M12) and shift of an all-literal lhs; (c) `let` chains where a literal-bound variable is first used in a comparison vs first used with a UInt64 (order-dependence, §6.2); (d) duplicate match literals incl. mod 2^64 (M11); (e) match as scrutinee-less `_`-only, var-only, pair-only; nested match unparenthesised; (f) loops: fuel numeral ∈ {0,1,len', 2^64−1, 2^64, 2^64+1}, arms swapped/misaligned, arms with the same var names, extra states, tuple states; (g) shadowing: param/let/loop var = def name, = prim name (`rd`, `put` are nano tags, rejected; in Lean legal), duplicate binder names `(a a : T)`; (h) top-of-def forms `def c : UInt64 := k` constants referenced before/after; (i) prims at the edges (§6.5): `rd`/`bget` OOB and index ≥ 2^63/2^64 wrap, `bset` OOB, `put` of 256/2^64−1, empty input, input length ≥ 2^16.
Well-formedness invariant for reporting: a generated program is *Lean-valid-by-construction* only if it avoids M1–M14; the interesting generator output is exactly the programs on the boundary, so run both oracles on everything and only classify.

### 8.4 Budget rules (for the compiler author)
Reject early in the lexer, in this order of cheapness: (1) numerals ≥ 2^64; (2) names in the reserved list or starting with `'`, bare `_` outside binders; (3) `<` followed by `-|$=>`; (4) attribute names not in the allowed set; (5) docs/attributes/`private` only at command level; (6) namespace stack check. In the parser: (7) literal-only tree typing (Nat vs UInt64) — track a boolean "has non-literal leaf" per tree; (8) shift-after-numeral check (same flag, per tree, left to right); (9) layout columns; (10) duplicate match literals.

## 9. Reproduce
```
# oleans for nano specs (once) and the harness
lean -R . -o $O/Nano/Main/Prelude.olean Nano/Main/Prelude.lean   # + Lexer/Lex2Spec, Lexer/DsSpec, Parser/ParSpec  (LEAN_PATH=$O)
python3 gen_trivia_ops.py; python3 gen_match_defs_ns.py; python3 diff.py /tmp/claude-0/lr/cases2   # edit paths at the top
```
Tool versions: Lean 4.34.1 (commit 5045d005), `B2.bin` of `origin/syntax-1`.

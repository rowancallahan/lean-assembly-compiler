# Harvest/H8 — do-notation leaves, proved against Lean 4.34.1

Method as `Nano/LeanEquiv`: theorems are Lean, so they can quote Lean's own definitions. New here: a `do` block written on the
right of a theorem is **elaborated by Lean's do-elaborator**, so `Id.run do …  = nanoRule …` is a kernel-checked statement about
Lean's real desugaring. All files standalone (Lean/Init/Std only). Verified with `lean` 4.34.1 per file (`REVIEW.lean` prints axioms:
only `propext`, `Quot.sound`, `Classical.choice`; no sorry / native_decide). Lean's do **parsers** are `leading_parser` closures (no
`ParserDescr` data), so grammar-level facts are `#guard`s, not theorems.

| feature | Lean def (4.34.1) | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|
| `let mut x := a; x := f x` | Elab/Do/Legacy.lean (elaborator output) | `runAll [.set f, …]` (fold of state updates) | `reassign_lean` | proved+built | `let mut` + reassignment = sequential state threading | S: desugar to nano `let` chain |
| `unless c do x := f x` | Parser/Do.lean:175, Elab/BuiltinDo | `St.unless_ c f` = `if c s then s else f s` | `unless_lean` | proved+built | `unless` | S |
| `if c then x := f x else x := g x` (stmt) | Parser/Do.lean:169 | `St.ifSet` | `if_stmt_lean` | proved+built | statement-level `if` over mutable state | S |
| `if let some y := o then x := f y x` | Parser/Do.lean:160 | `ifLet o f s` (match on `Option`) | `ifLet_lean` | proved+built (Option only) | `if let` for the one pattern nano's match supports | S |
| `let y ← e` in `Id` | Parser/Do.lean:99 | `let y := e` | `bind_id_lean` | proved+built | `←` is `let` when the monad is `Id` | S |
| `for a in xs do x := g a x` | Init/Data/List/Control.lean:447 `List.forIn'` | `List.foldl` | `for_fold_lean` | proved+built | plain `for` over a list | M: needs lists/loops in nano IR |
| `for a in xs do` with `break`/`continue`/`return c` | `forIn`, `ForInStep`, `MProd (Option γ) β` state | `runL` over `Ex.cont/brk/ret` returning `Sum γ β` | `forIn_list_eq` | proved+built | exact exit semantics of the three loop exits, incl. Lean's Option-state encoding of `return` | M |
| `for i in [lo:hi]` | Init/Data/Range/Basic.lean:35 (`Std.Legacy.Range`) | `runL` over `List.range' lo (hi-lo)` | `forIn_range_eq` | proved+built (step 1) | counted loops; `[a:b:s]` same via `List.range' _ _ s` | M |
| `while c x do x := f x` | `Lean.Loop.forIn` (Init/While.lean:95; `partial` `repeatM`) | fuel loop `runW (whileStep c f) n` | `runW_imp_lean`, `while_lean` | proved+built, **subset form**: nano run finishes within its fuel ⇒ Lean's value equal. Uses Lean's public unfolding `Loop.forIn_eq_of_monadTail` (valid for `Id`) | `while`, `repeat`/`break` (same `Loop`); nano must demand a terminating witness (fuel/measure) — Lean itself does not | M: termination witness needed |
| doSeq item list | Parser/Do.lean:52 `getDoElems` | `items` (slot 0 of `doSeqIndent`, slot 1 of `doSeqBracketed`) | `items_eq_lean`, `indent_items` | proved+built | doSeq shape; `{ a; b }` and indented blocks give the same items | S |
| `let mut` flag | Elab/Do/Legacy.lean:1262 `isMutableLet` | `isMut` = slot 1 non-null on `doLet/doLetArrow/doLetElse` | `isMut_eq_lean` | proved+built (`rfl`) | recognising `mut` | S |
| expression statement | Elab/Do/Legacy.lean:823 `isDoExpr?` | `exprOf` | `exprOf_eq_lean` | proved+built (`rfl`) | doExpr shape | S |
| do-keywords (`break continue return while repeat until unless for in mut ← else do`) and `leadPrec`/`argPrec` | `ParserInfo.collectTokens` of `doBreak…doNested` (Parser/Do.lean:241-339) | nano keyword list | `Keywords.lean` `#guard`s | **not kernel-provable**: `symbol` uses `String.trimAscii`, kernel stuck; `native_decide` banned. Interpreter check only | reserved-word list for new syntax (cf. M6) | S as a regression test |
| grammar of `for`/`while`/`return` etc. | `leading_parser` closures (`Parser/Do.lean`) | — | — | **not provable**: closures over `ParserFn` state machines; layout (`many1Indent`, `checkColGe`, `withPosition`) is position-dependent | — | fuzz only |
| `try/catch/finally`, `match` in do, `let rec`, nested actions `(← e)`, `repeat … until` hoisting | Elab/Do (`TermElabM`, `partial`) | — | — | **not provable**: monadic elaborator (`Code`/`ToCodeBlock`), join points, name generation | — | conservative rejection |

## Edge (what no theorem here covers)
* Lean's real do-elaborator is a `TermElabM` program; the `Id.run do …` theorems only fix **its output on those shapes** (state type
  generic, bodies as functions). Combinations (`for` inside `while`, `return` under `if`) need the shape lemmas composed; not done.
* `while`: Lean's loop may diverge; the theorem is conditional on nano's own fuel run finishing.
* Types: all rules are for `Id`; nano's UInt64/Bool typing (M1) is separate.

Check: `lean` per file (dependencies: none beyond Lean core), or `lake build Harvest.H8.REVIEW` with the `Harvest` lib in `lakefile.toml` (this branch only).

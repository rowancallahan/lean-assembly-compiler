/- Harvest/H4/Reserved: candidate list of Lean 4.34.1 reserved words (identifier-shaped tokens) and a nano-style identifier
rule that rejects each; provenance of part of the list from Lean's own `ParserDescr` constants (kernel-checked).
Standalone: imports only `Lean`.  `isW`/`isD`/`kwTable` are COPIES of Nano/Lexer/Lex2Spec.lean:18-37 (`Link.lean` proves
the copies equal the originals when built inside the nano tree).
`reserved` = the 190 words found rejected as `let`/param/def names by Lean 4.34.1 (Testing/nano/v2self/fuzz/lean_rules/
lean_reserved_words.txt on branch lean-rules, §3 of LEAN_RULES.md); it is DATA obtained at run time from the token table.
What is proved: (1) nano's rule rejects every listed word, and still accepts `w ++ "1"` / `w ++ "'"` (Lean: `isToken`
requires the token to be at least as long as the identifier, Parser/Basic.lean:934-941); (2) every identifier-shaped
`ParserDescr.symbol` atom of every Init notation/syntax constant (73 constants, listed) is in `reserved`.
What is NOT provable: completeness against builtin (non-descriptor) parsers `def let fun match do ...` (their tokens are
closures over `String.trimAscii`, not kernel-reducible) and against the runtime token table. -/
import Lean
namespace H4
open Lean

def isW (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || b == 95 || b == 39 || (48 ≤ b && b ≤ 57)
def isD (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- nano's keyword/prim spellings (Lex2Spec.kwTable, tags dropped) -/
def kwWords : List String :=
  ["def", "let", "UInt64", "if", "then", "else", "Nat", "Buf", "List", "UInt8", "len'", "rd", "len", "put", "bnew",
   "bsize", "bget", "bset", "bpush"]

/-- candidate reserved list -/
def reserved : List String :=
  ["Prop",
  "Sort",
  "StateRefT",
  "Type",
  "_",
  "abbrev",
  "add_decl_doc",
  "assert!",
  "assert_not_exists",
  "assert_not_imported",
  "at",
  "attribute",
  "axiom",
  "bif",
  "binder_predicate",
  "break",
  "builtin_cbv_simproc",
  "builtin_cbv_simproc_decl",
  "builtin_dsimproc",
  "builtin_dsimproc_decl",
  "builtin_grind_propagator",
  "builtin_initialize",
  "builtin_simproc",
  "builtin_simproc_decl",
  "by",
  "by?",
  "by_elab",
  "calc",
  "catch",
  "cbv_eval",
  "cbv_simproc",
  "cbv_simproc_decl",
  "class",
  "coinductive",
  "coinductive_fixpoint",
  "continue",
  "dbg_trace",
  "debug_assert!",
  "declare_bitwise_int_theorems",
  "declare_bitwise_uint_theorems",
  "declare_int_theorems",
  "declare_simp_like_tactic",
  "declare_syntax_cat",
  "declare_uint_theorems",
  "decreasing_by",
  "def",
  "deprecated_module",
  "deprecated_syntax",
  "deriving",
  "do",
  "docs_to_verso",
  "dsimproc",
  "dsimproc_decl",
  "elab",
  "elab_rules",
  "else",
  "end",
  "eval_prec",
  "eval_prio",
  "example",
  "exists",
  "export",
  "extends",
  "f!",
  "finally",
  "for",
  "forall",
  "from",
  "fun",
  "generalizing",
  "grind_annotated",
  "grind_pattern",
  "grind_propagator",
  "have",
  "haveI",
  "hiding",
  "idbg",
  "if",
  "import",
  "in",
  "include",
  "include_str",
  "inductive",
  "inductive_fixpoint",
  "inferInstanceAs",
  "infix",
  "infixl",
  "infixr",
  "init_grind_norm",
  "init_quot",
  "initialize",
  "instance",
  "leading_parser",
  "let",
  "letI",
  "let_delayed",
  "let_expr",
  "let_fun",
  "let_tmp",
  "local",
  "logNamedError",
  "logNamedErrorAt",
  "logNamedWarning",
  "logNamedWarningAt",
  "macro",
  "macro_rules",
  "match",
  "match_expr",
  "matches",
  "max_prec",
  "meta",
  "mod_cast",
  "mut",
  "mutual",
  "namespace",
  "nat_lit",
  "no_index",
  "nofun",
  "nomatch",
  "noncomputable",
  "nonrec",
  "norm_cast_add_elim",
  "notation",
  "omit",
  "opaque",
  "open",
  "panic!",
  "partial",
  "partial_fixpoint",
  "postfix",
  "prefix",
  "println!",
  "private",
  "protected",
  "public",
  "recommended_spelling",
  "register_error_explanation",
  "register_sym_dsimp",
  "register_sym_simp",
  "register_tactic_tag",
  "register_try?_tactic",
  "renaming",
  "repeat",
  "return",
  "run_cmd",
  "run_elab",
  "run_meta",
  "s!",
  "scoped",
  "seal",
  "section",
  "set_library_suggestions",
  "set_option",
  "show",
  "show_term",
  "show_term_elab",
  "simproc",
  "simproc_decl",
  "sorry",
  "structure",
  "suffices",
  "syntax",
  "tactic_alt",
  "tactic_extension",
  "tactic_name",
  "tactic_tag",
  "termination_by",
  "termination_by?",
  "then",
  "theorem",
  "throwNamedError",
  "throwNamedErrorAt",
  "trailing_parser",
  "try",
  "unif_hint",
  "universe",
  "unless",
  "unlock_limits",
  "unreachable!",
  "unsafe",
  "unseal",
  "until",
  "using",
  "using!",
  "variable",
  "where",
  "while",
  "with",
  "with_weak_namespace",
  "without_expected_type"]

/-- the identifier rule: a maximal word run, not digit-led, not quote-led, not a nano keyword, not reserved -/
def identOK (w : List UInt8) : Bool :=
  match w with
  | [] => false
  | c :: _ => w.all isW && !isD c && c != 39 && !(kwWords.map bytes).contains w && !(reserved.map bytes).contains w

/-- **every reserved word is rejected as a name** by `identOK` -/
theorem reserved_not_ident : reserved.all (fun s => identOK (bytes s) == false) = true := by decide +kernel

/-- ... and each is either all word bytes or contains `!`/`?` (never one nano word) -/
theorem reserved_wordlike_or_punct :
    reserved.all (fun s => (bytes s).all isW || (bytes s).any (fun b => b == 33 || b == 63)) = true := by
  decide +kernel

/-- the rule is not over-rejecting: `w1` and `w'` are names unless they contain `!`/`?` -/
theorem reserved_ext_ok :
    reserved.all (fun s => !(bytes s).all isW || (identOK (bytes s ++ [49]) && identOK (bytes s ++ [39]))) = true := by
  decide +kernel

/-- each reserved word is exactly shaped like a Lean identifier (`isIdFirst`, then `isIdRest`), so the only thing that
makes Lean reject it as a name is the token table -/
theorem reserved_lean_shaped :
    reserved.all (fun s => match s.toList with
      | [] => false
      | c :: cs => Lean.isIdFirst c && cs.all Lean.isIdRest) = true := by decide +kernel

/-! ## provenance of part of `reserved` from Lean's own notation descriptors -/

/-- the symbol atoms of a description, spaces removed (as `LeanEquiv.symBytes`) -/
def symAtoms : ParserDescr → List (List Char)
  | .node _ _ d | .unary _ d | .trailingNode _ _ _ d => symAtoms d
  | .binary _ a b => symAtoms a ++ symAtoms b
  | .symbol s => [s.toList.filter (· != ' ')]
  | _ => []

def identAtom (a : List Char) : Bool :=
  match a with
  | [] => false
  | c :: cs => c.isAlpha && (c :: cs).all (fun c => c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?')

/-- every Init syntax/notation constant that has an identifier-shaped symbol (generated by scanning `import Lean`), except
`Lean.withAnnotateTerm` (`scoped syntax`: its token `with_annotate_term` is active only after `open Lean`, so it is NOT
reserved by default: `def f (with_annotate_term : Nat) := ..` parses) -/
def initDescrs : List ParserDescr :=
  [Lean.Grind.grindLintCheck,
  Lean.Parser.Command.classAbbrev,
  Lean.Parser.Command.grindAnnotated,
  Lean.Parser.Command.registerSymDSimp,
  Lean.Parser.Command.registerSymSimp,
  Lean.Parser.Command.registerTryTactic,
  Lean.Parser.Sym.Simp.rewriteInline,
  Lean.Parser.Sym.Simp.rewriteSet,
  Lean.Parser.Tactic.Conv.conv,
  Lean.Parser.Tactic.Grind.setConfig,
  Lean.Parser.Tactic.Grind.setOption,
  Lean.Parser.Tactic.apply?,
  Lean.Parser.Tactic.by?,
  Lean.Parser.Tactic.cases,
  Lean.Parser.Tactic.declareSimpLikeTactic,
  Lean.Parser.Tactic.exact?,
  Lean.Parser.Tactic.funInduction,
  Lean.Parser.Tactic.impossible,
  Lean.Parser.Tactic.induction,
  Lean.Parser.Tactic.injection,
  Lean.Parser.Tactic.letrec,
  Lean.Parser.Tactic.normCastAddElim,
  Lean.Parser.Tactic.rcases,
  Lean.Parser.Tactic.showTermElab,
  Lean.Parser.Tactic.tacDepIfThenElse,
  Lean.Parser.Tactic.tacIfThenElse,
  Lean.Parser.checkTactic,
  Lean.Parser.checkTacticFailure,
  Lean.Parser.commandSeal__,
  Lean.Parser.commandUnseal__,
  Lean.Parser.«command_Builtin_cbv_simproc_decl_(_):=_»,
  Lean.Parser.«command_Builtin_dsimproc_decl_(_):=_»,
  Lean.Parser.«command_Builtin_grind_propagator____:=_»,
  Lean.Parser.«command_Builtin_simproc_decl_(_):=_»,
  Lean.Parser.«command_Cbv_simproc_decl_(_):=_»,
  Lean.Parser.«command_Dsimproc_decl_(_):=_»,
  Lean.Parser.«command_Grind_propagator___(_):=_»,
  Lean.Parser.«command_Simproc_decl_(_):=_»,
  Lean.Parser.«command__Builtin_cbv_simproc____(_):=_»,
  Lean.Parser.«command__Builtin_dsimproc__[_]_(_):=_»,
  Lean.Parser.«command__Builtin_simproc__[_]_(_):=_»,
  Lean.Parser.«command__Cbv_simproc____(_):=_»,
  Lean.Parser.«command__Dsimproc__[_]_(_):=_»,
  Lean.Parser.«command__Simproc__[_]_(_):=_»,
  Lean.byElab,
  Lean.calc,
  Lean.guardMsgsCmd,
  Lean.guardPanicCmd,
  Lean.includeStr,
  Lean.infoTreesCmd,
  Lean.modCast,
  Lean.runCmd,
  Lean.runElab,
  Lean.runMeta,
  Lean.setLibrarySuggestionsCmd,
  Lean.termEval_prec_,
  Lean.termEval_prio_,
  Lean.«command__Unif_hint____Where_|_-⊢__»,
  Lean.«term_Matches_|»,
  Std.termF!_,
  boolIfThenElse,
  commandDeclare_bitwise_int_theorems__,
  commandDeclare_bitwise_uint_theorems__,
  commandDeclare_int_theorems__,
  commandDeclare_uint_theorems__,
  rawNatLit,
  termDepIfThenElse,
  termIfLet,
  termIfThenElse,
  termMax_prec,
  termPrintln!__,
  termS!_,
  termWithout_expected_type_,
  «termExists_,_»]

/-- **provenance**: each identifier-shaped symbol of each of those 73 Init descriptors is reserved -/
theorem init_atoms_reserved :
    initDescrs.all (fun d => (symAtoms d).all (fun a => !identAtom a || (reserved.map String.toList).contains a)) = true := by
  decide +kernel

end H4

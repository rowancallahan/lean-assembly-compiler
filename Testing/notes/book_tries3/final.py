import json,csv,collections,re,sys,os
S=os.environ['BS3_ROOT']
rows=json.load(open(S+'/rows.json')); anyc=json.load(open(S+'/anyc.json'))
OUT=sys.argv[1]
GOOD=('compiled','compiled on main (hand directive)','callee inlined in a compiled function')
def loc(r): return f"`{r['file'].replace('Examples/','')}:{r['line']}`"
def chap(f):
    f=f.replace('Examples/','')
    for k,v in [('Intro','1 Getting to Know Lean'),('HelloWorld','2 Hello, World!'),('Cat','2 Hello, World!'),('Props','3 Propositions, Proofs, Indexing'),('Classes','4 Overloading and Type Classes'),('MonadTransformers','7 Monad Transformers'),('FunctorApplicativeMonad','6 Functor, Applicative, Monad'),('Monads','5 Monads'),('DependentTypes','8 Dependent Types'),('ProgramsProofs','9 Programming, Proving, Performance'),('Induction','9 Programming, Proving, Performance'),('Universes','8 Dependent Types (universes)'),('ExampleSupport','support'),('douglib','support / other'),('Strings','other'),('SpecialTypes','other')]:
        if f.startswith(k): return v
    return 'other'
# CSV
with open(OUT+'/book_survey3.csv','w',newline='') as fh:
    w=csv.writer(fh); w.writerow(['chapter','file','line','end_line','name','status','front_end_or_command','blocker','message','survey2_status','body_hash'])
    for r in rows:
        w.writerow([chap(r['file']),r['file'],r['line'],r['end'],r['name'],r['status'],r.get('cmd',''),r.get('bucket',''),r.get('msg',''),r['old'],r['body']])
c=collections.Counter(r['status'] for r in rows)
fun=[r for r in rows if r['status'] in GOOD or r['status'] in('blocked','not run: def does not elaborate in isolation')]
comp=[r for r in rows if r['status'] in GOOD]
blk=[r for r in rows if r['status']=='blocked']
nr=[r for r in rows if r['status'].startswith('not run')]
dist=lambda L: len({r['body'] for r in L})
md=[]
A=md.append
A("# Book survey 3: all pure functions of \"Functional Programming in Lean\" against current `main`\n")
A("Source: `github.com/leanprover/fp-lean` @0abeea5, `examples/` (57 `.lean` files, 37 example modules; same commit as `BOOK_SURVEY.md`). Compiler: `main` @ce989e1 (front ends `frontx_compile`, `frontx_view`, `frontx_ind`, `wa_compile`; NOTES §15-21), Lean 4.29.0, Sail model `opencompl/sail-riscv-lean` built from scratch. Data: `book_survey3.csv` (one row per top-level `def`/`abbrev`), scripts: `book_tries3/`. Compiler sources are untouched.\n")
A("## Totals\n")
A(f"| | rows | distinct bodies |\n|---|---|---|")
A(f"| top-level `def`/`abbrev` in the 37 example modules + `ExampleSupport.lean` | {len(rows)} | |")
A(f"| not book functions: Lean elaborator code of `ExampleSupport.lean` | {c['meta (Lean elaborator code, not book functions)']} | |")
A(f"| IO / effects (skipped, out of scope) | {c['IO (skipped)']} | |")
A(f"| not a function (constants, types, `abbrev`s of types: nothing to compile) | {c['not a function (constant / type)']} | |")
A(f"| **pure functions (the survey's population)** | **{len(fun)}** | **{dist(fun)}** |")
A(f"| &nbsp;&nbsp;compiled verbatim, default command of the right front end (this survey's harness) | {c['compiled']} | {dist([r for r in rows if r['status']=='compiled'])} |")
A(f"| &nbsp;&nbsp;compiled verbatim on `main` with a hand-given directive or entry (`using`, `with`, `from`, `frontx_ind … using`, wrapper entry), found in `Riscv/Frontx/*.lean` | {c['compiled on main (hand directive)']} | {dist([r for r in rows if r['status']=='compiled on main (hand directive)'])} |")
A(f"| &nbsp;&nbsp;standalone attempt fails, but the def is inlined into a compiled function | {c['callee inlined in a compiled function']} | 1 |")
A(f"| **compiled (the three lines above)** | **{len(comp)}** | **{dist(comp)}** |")
A(f"| blocked: a front end rejects it (message and blocker below) | {len(blk)} | {dist(blk)} |")
A(f"| not run: the verbatim def does not elaborate in isolation (book's own broken/illustrative examples, or context my extractor did not carry; see below) | {len(nr)} | {dist(nr)} |")
A(f"\nThe 117 `instance` commands are not rows: an instance has no entry point (`Add Pos` is compiled when `Pos.mul` is, `+` calls it). Rates: compiled / pure functions = {len(comp)}/{len(fun)} = {100*len(comp)//len(fun)}% by rows, {dist(comp)}/{dist(fun)} by distinct bodies (the book restates `length`, `halve`, `even`, ... in several namespaces).\n")
A("## Method (what \"verbatim\" and \"right front end\" mean here)\n")
A("1. `extract.py` splits each file into top-level commands with `file:line-end`; drops the book's `discarding … stop discarding` (intentional errors), `evaluation steps` blocks, `#check_msgs`, docstrings and comments. The def text is copied unchanged, including `open … in` prefixes (except `open SubVerso.Examples in`).")
A("2. `gen.py` writes one Lean file per def: the def, plus the transitive closure of the book declarations it names (same file and the example modules it imports; inductives, structures, helper defs, instances of included types, namespaces it opens), each in its original `namespace`/`open`/`variable` scope, all inside `namespace Proven.Frontx.Run`. Then the compile command.")
A("3. `run.py` tries, in this order, the first that succeeds wins: `frontx_compile f`; if `List` is in the signature `frontx_view f` + `frontx_compile f.view from f.view.eq measure …` (0-2 extra arguments), and the same through the callee of a one-line wrapper (`def sum xs := sumHelper 0 xs`); if a user inductive/structure is in the signature `frontx_ind_type` (type parameters := `Nat`) + `frontx_ind f on T [using R]`; if `Array` is in it `wa_compile f`. Success = the compiler's own success line after a marker, no error after the marker, no `sorry`, no panic. Generated theorems are the compiler's (no hand proofs, none of the compiled rows needed a `requires`/`with`/`using` hint).")
A("4. Things the default commands cannot guess (`requires`, `with` invariants, `using` lemma, `from … spec`, `frontx_tailcopy`, glue entries) are taken from the files already on `main` (`gt.py`): a book def counts as `compiled on main (hand directive)` when a def in `Riscv/Frontx/*.lean` has the same body text (comments/whitespace/qualifiers normalised) and a `frontx_*` command on it. I built those 12 modules here (`lake build`, 254 jobs, no error) but did not re-derive the directives.")
A("5. Blockers: the first error message of the most specialised failing attempt + the printed signature, mapped to one bucket by a fixed rule list (`survey3.py`, order = table order). A row has exactly one primary bucket; the second table counts every feature present in the source of each non-compiled row. Both are heuristics.\n")
A("## Compiled\n")
A("| book def | compiled by | provenance of directive |\n|---|---|---|")
for r in comp:
    cmd=r.get('cmd','')
    how={'compile':'`frontx_compile`','ind':'`frontx_ind`','wa':'`wa_compile`'}.get(cmd)
    if how is None:
        how='`frontx_view`+`frontx_compile`' if cmd.startswith('view') else ('callee of the wrapper through `frontx_view`' if cmd.startswith('helper') else cmd)
    A(f"| {loc(r)} `{r['name']}` | {how} | |" if r['status']=='compiled' else f"| {loc(r)} `{r['name']}` | {cmd.split('  [')[0]} | {cmd.split('  [')[1].rstrip(']') if '  [' in cmd else 'inlined into a compiled function'} |")
A("")
A("## Blockers, ranked (primary bucket per blocked row; "+str(len(blk))+" rows)\n")
A("| # | feature | rows | examples |\n|---|---|---|---|")
bb=collections.defaultdict(list)
for r in blk: bb[r['bucket']].append(r)
for i,(b,l) in enumerate(sorted(bb.items(),key=lambda x:-len(x[1])),1):
    A(f"| {i} | {b} | {len(l)} | "+', '.join(f"`{r['name']}` {loc(r)}" for r in l[:4])+" |")
A("\nSecond view, every feature present (not exclusive) over the "+str(len(blk)+len(nr))+" non-compiled rows (blocked + not run): "+', '.join(f"{k} {v}" for k,v in sorted(anyc.items(),key=lambda x:-x[1]))+".\n")
A("### Not run (verbatim def does not elaborate in isolation): "+str(len(nr))+" rows\n")
def nrcause(m):
    if re.search(r'termination|Missing cases|Type mismatch|failed to synthesize instance of type class\s+(OfNat|HMul|BEq)|Failed to infer|Invalid pattern|metavariables|expected token|cannot be mutated|failed to prove index|rfl|Application type mismatch|Fields missing|placeholder|Type of sort|stuck at',m): return 'the book shows this def failing (termination, type error, missing instance, `Oops` variants) or uses book notation that needs `ExampleSupport` macros'
    return 'context my closure did not carry (a later-defined structure/field, `c!` macro, `Pure (State Nat)` instance, scope nesting): needs hand-made context, **not counted as blocked**'
cc=collections.Counter(nrcause(r['msg']) for r in nr); 
for k,v in cc.items(): A(f"- {v}: {k}")
A("")
A("## Delta vs `BOOK_SURVEY.md` (survey 2, `booksurvey2`)\n")
old_c=[r for r in rows if r['old'] in('machine-thm','source-thm')]
kept=[r for r in old_c if r['status'] in GOOD]; lost=[r for r in old_c if r['status'] not in GOOD]
new=[r for r in comp if r['old'] not in('machine-thm','source-thm')]
A(f"Survey 2 (read from `main`, not rebuilt) listed 38 matching rows as compiled verbatim on `main` (15 machine theorem, 23 source theorem; its CSV has 39, one of them (`Div.lean:26`) is the book's non-terminating `div`, which this survey's extractor drops with the `discarding` region) and 7 as `not-on-main`, and 35 B rows `likely-untried` (34 matched here) (judged by reading, never run). Now: **{len(comp)} compiled rows** ({dist(comp)} distinct bodies), of which {len(kept)} were already listed and **{len(new)} are new**; {len(lost)} listed rows are not in the compiled set (below).\n")
A("| survey 2 status | rows | compiled now | still blocked / not run / other |\n|---|---|---|---|")
for st in ('machine-thm','source-thm','not-on-main','likely-untried'):
    L=[r for r in rows if r['old']==st]
    A(f"| {st} | {len(L)} | {sum(r['status'] in GOOD for r in L)} | {sum(r['status'] not in GOOD for r in L)} |")
A(f"| (no survey 2 verdict B) | {sum(not r['old'] for r in rows if r['status'] in GOOD)} compiled now | | |")
A("")
A("Listed in survey 2 and not compiled now:\n")
for r in lost: A(f"- {loc(r)} `{r['name']}`: {r['status']}"+(f" ({r.get('msg','')[:100]})" if r.get('msg') else ''))
A("\nSurvey 2 rows `not-on-main` or `likely-untried` that are still blocked: "+', '.join(f"{loc(r)} `{r['name']}` ({r.get('bucket','').split(' (')[0] or r['status']})" for r in rows if r['old'] in('not-on-main','likely-untried') and r['status'] not in GOOD)+".\n")
A("## Newly compiling functions ("+str(len(new))+" rows; the front end is the one that worked)\n")
A("| book def | status | front end | survey 2 |\n|---|---|---|---|")
for r in new:
    fe=r.get('cmd','').split('  [')[0] or '(callee)'
    fe={'compile':'`frontx_compile`','ind':'`frontx_ind`'}.get(fe,'`frontx_view`' if fe.startswith('view') else ('`frontx_view` on callee' if fe.startswith('helper') else fe))
    A(f"| {loc(r)} `{r['name']}` | {'on main, hand directive' if 'main' in r['status'] else ('inlined' if 'inlined' in r['status'] else 'default command')} | {fe} | {r['old'] or 'C or not listed'} |")
A("")
A("## By chapter\n")
A("| chapter | pure functions | compiled | blocked | not run |\n|---|---|---|---|---|")
ch=collections.OrderedDict()
for r in fun: ch.setdefault(chap(r['file']),[]).append(r)
for k in sorted(ch):
    L=ch[k]; A(f"| {k} | {len(L)} | {sum(r['status'] in GOOD for r in L)} | {sum(r['status']=='blocked' for r in L)} | {sum(r['status'].startswith('not run') for r in L)} |")
A("")
open(OUT+'/BOOK_SURVEY3.part.md','w').write('\n'.join(md))
print(len(new),len(kept),len(lost))

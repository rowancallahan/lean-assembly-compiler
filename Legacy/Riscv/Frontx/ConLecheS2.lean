import Legacy.Riscv.Frontx.ExprExamples
import Legacy.Riscv.Frontx.IndGate
set_option maxErrors 100000
open Proven.Frontx.ExprEx

-- ConLeche/Cached/ExprOpsC.lean:116
section
namespace ConLeche.Expr
/-! ## The substitution walks (tasks #314, #316, #317)

ONE walk per operation — `instantiate1XP`, `instantiateLiftXP`,
`instantiateListXP`, `instantiateRevXP`, `abstract1XP`,
`abstractRangeXP`, `instLevelParamsXP` — and ONE memo discipline.  The
design, as landed:

* **Memoise only what is shared.**  At every compound node past the
  cutoff the walk asks `withExclusive`
  (`ConLeche/Kernel/Exclusive.lean`) whether the node is an EXCLUSIVE
  object — single-threaded, reference count 1.  An exclusive node
  cannot be reached twice, so it is rebuilt with the memo untouched:
  no key, no probe, no insert.  A shared node (count `> 1`,
  multi-threaded, or persistent — the stream's index) is
  probed and, on a miss, recorded after the rebuild.  The table is
  created at the first shared compound node (`none` until then); the
  root is never probed (it cannot be reached again within its own
  walk).  The official kernel's `replace_fn` caches exactly the
  `!is_likely_unshared(e)` nodes.
* **Key the memo by address and cursor.**  The key is the node's
  address, read by `withPtrAddr` (`Expr.withAddr`) at the top of the
  shared step, packed with the cursor into one `Nat` (`pkey`) — a
  scalar, no allocation, no structural hash.  The table is a
  `Std.HashMap` on that key.
* **Validate a hit by pointer identity.**  A probe that returns an
  entry is believed only after `Expr.ptrDec` (`withPtrEq`, the
  pointer comparison at runtime and the derived structural decision
  in the model) says the stored node IS the current one, and the
  cursors compare equal.  The address is therefore never trusted: a
  wrong key can only cost a rebuild, never a value.
* **Every entry is self-proving.**  A `PEnt` stores its node, its
  rebuild, its cursor and the proof `val = s node depth`.  So there is
  **no table invariant** — the table may be anything, may grow and may
  overwrite — and a validated hit yields the proof the walk's result
  type demands by rewriting along the two equalities.  This is the
  `BeqMap`/`EqPair`/`probeHit` shape of `Expr.beqGoX`, applied to the
  walks.
* **No cutoff.**  The walk is exact: it memoises every shared compound
  node it meets, for as long as the walk lasts, and nothing bounds the
  table.  The node budget of task #313 — a heuristic that stopped
  memoising after 256 nodes and restarted — is gone (task #317).

**The borrowed-parameter convention is a REQUIREMENT, not an
optimisation.**  The node is borrowed (`@&`) all the way down, and so
is the replacement.  An owned parameter is a reference of its own, and
the count `withExclusive` reads would then be "in-tree references
+ 1" — every child of a held root would answer shared, and the memo
would degenerate to the always-memoised walk.  Borrowed, the count is
the number of references INSIDE the term (plus the caller's at the
root, which is never asked), which is the question the memo exists to
answer.  **How this is checked**: by reading the generated C of every
walk (`.lake/build/ir/ConLeche/Cached/ExprOpsC.c`) for a surviving
`lean_inc_ref` of the node before `lean_is_exclusive_obj` — the IR
audits of the task #314 and #316 records (DESIGN.md).  A change to
these walks that drops a `@&` or lets a `let`, a closure or a `Prod`
hold the node across the check is silently correct and measurably
slower; the audit is what catches it.

**Verification is intrinsic** (the `Expr.beqGoX` shape): a walk returns
a `Squash` of the rebuilt term with its proof of equality to the PLAIN
descent (`*P`, the reference — `Verify/Cached/OpsC.lean` proves each
`*P` equal to the specification) beside the memo, which is
unobservable.  The result is a `Subsingleton`, which is the obligation
`withExclusive` and `withPtrAddr` each ask of their continuation — so
the wrapper's theorem holds whatever the reference count and the
address are, by the primitives' contracts, never by a case analysis on
either.  Each walk's `enter*P` is the child step: the cutoff, the
compound test, then the exclusivity read; its `rec` argument is the
descent itself, inlined, so the recursive call is applied to the
subterm and termination is the walk's own.

Nothing here adds to the trust surface beyond the one allowlisted
escape: `withPtrAddr` and `withPtrEq` are `Init.Util`'s (and the tree
already relies on both, in `Expr.beqGoX` and `Name.decEqPtr`), and
`withExclusive` is `ConLeche/Kernel/Exclusive.lean`'s — the walks' one
`unsafe`-implemented primitive, whose module docstring is the
justification `tests/trust-surface.sh` points at. -/
/-- The nodes a memo entry can save a descent of. -/
@[inline] def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false
end ConLeche.Expr
end
frontx_ind ConLeche.Expr.isCompound on TExpr


-- ConLeche/Cached/ExprOpsC.lean:1298
section
namespace ConLeche.Expr
/-! ## The `Bool`-valued walks

The scope, definedness and resolution guards are the substitution
walks' design over a `Bool`, and the tree has ONE memo discipline for
every traversal memo in it (task #319; `Expr.beqGoX` is the third
instance).  Each guard used to create a `Std.HashMap` per call, keyed
STRUCTURALLY on the node (and, for the scope walk, the cursor), and
record EVERY node it decided — a probe that compared the stored node
with the query by `Expr.beq`, and an entry for every leaf.  Instead:

* **memoise only what is shared** — at every compound child past the
  cutoff, `withExclusive` (`ConLeche/Kernel/Exclusive.lean`) on the
  node (borrowed); an exclusive node is descended with the memo
  untouched (no key, no probe, no insert), a shared one is probed and
  recorded on a miss.  A node with one reference cannot be reached
  again, so recording it is pure loss;
* **key by address and cursor** — `withPtrAddr` (`Expr.withAddr`) at
  the top of the shared step, packed with the cursor into one `Nat`
  (`pkey`), under the mixing hash of `PKey`.  No structural hash and
  no `Expr.beq` on any probe;
* **validate a hit by pointer identity** — `Expr.ptrDec` on the
  stored node against the current one, plus a cursor compare.  The
  address is never trusted: a wrong key can only cost a descent,
  never a value;
* **every entry is self-proving** — a `BEnt` carries its node, its
  cursor, its decision and the proof `val = s node depth`, so there
  is **no table invariant** and no lemma about the table at all;
* **no cutoff beyond the walk's own** (`fvarB`, `hasLP`, and none at
  all for `constsResolveFC`): every shared compound node the walk
  meets is memoised, for as long as the call lasts.

A walk's result is a `Squash` of `{ r : Bool // r = <the plain
descent> }` beside the memo — a `Subsingleton`, which is the
obligation `withExclusive` and `withPtrAddr` each ask of their
continuation — and the wrapper reads the decision off it with
`resBool`.  The plain descents (`*P`) carry the cutoff and are proved
equal to their `ConLeche.Expr` specifications in
`ConLeche/Verify/Cached/{OpsC,GuardsC}.lean`.  **The borrowed
parameter is a requirement, not an optimisation**, for the reason the
substitution walks' section states.

The one walk of this file that is NOT of this shape is
`fvarLeavesGoC`, whose memo is a visited SET; its docstring says
why. -/
/-- The nodes a `Bool` memo entry can save a descent of: the compound
nodes, and `fvar` — every walk of this section descends into the
ANNOTATION, so the cached fvar range does not decide an `fvar` node. -/
@[inline] def isCompoundF : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. | .fvar .. => true
  | _ => false
end ConLeche.Expr
end
frontx_ind ConLeche.Expr.isCompoundF on TExpr


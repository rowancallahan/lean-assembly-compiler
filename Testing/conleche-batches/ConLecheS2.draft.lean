-- DRAFT, does not elaborate (see Testing/notes/frontx/CONLECHE_S2.md). Kept outside Riscv.Frontx so the Frontx lake target is unaffected.
import Riscv.Frontx.ExprExamples
import Riscv.Frontx.IndGate
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet

set_option maxErrors 100000

-- batch A (Testing/conleche-batches/batchA.lean, branch conleche-batch-b2), body verbatim
set_option maxErrors 100000
-- Batch A: con-leche Name/Expr functions (ConLeche/Kernel/Expr.lean, ConLeche/Kernel/ExprOps.lean)
-- Source: origin/conleche-depth Testing/conleche-depth/out/F2.lean.txt (con-leche @6810492c1), lines copied verbatim.
-- Listed targets: Testing/notes/CONLECHE_TARGETS.md (origin/conleche-targets). Dependencies copied in F2 order.

namespace ConLeche
-- ConLeche/Kernel/Expr.lean:1292
section
namespace Expr
/-- The executed structural equality.  Definitionally `decide (a = b)`,
hence definitionally the `BEq` any `DecidableEq` type has, with
`beqMemo` substituted by the compiler on the `@[csimp]` equation
below. -/
def beq (a b : Expr) : Bool := decide (a = b)
end Expr
end

-- ConLeche/Kernel/PtrDecEq.lean:28
/-- `withPtrEqDecEq a b k`: the pointer test, then `k ()`. -/
@[inline] def ptrDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) :
    Decidable (a = b) :=
  withPtrEqDecEq a b k

-- ConLeche/Kernel/Exclusive.lean:94
set_option linter.unusedVariables.funArgs false in
/-- The compiled `withExclusive`: the continuation on the object's real
exclusivity.  Inlined into its caller, so the object reaches the
`@[extern]` check as the caller's own variable — BORROWED by the
check's signature — and the call adds no reference; the continuation
receives only the `Bool`.  (`implemented_by` demands the exact type of
`withExclusive`, so `a` carries no `@&` here; the borrow that matters
is `isExclusiveUnsafe`'s.) -/
@[inline] unsafe def withExclusiveUnsafe {α : Type u} {β : Type v} (a : α)
    (k : Bool → β) (h : k true = k false) : β :=
  k (isExclusiveUnsafe a)

-- ConLeche/Kernel/Exclusive.lean:108
@[implemented_by withExclusiveUnsafe]
def withExclusive {α : Type u} {β : Type v} (a : α) (k : Bool → β)
    (h : k true = k false) : β :=
  k false

-- ConLeche/Kernel/Exclusive.lean:114
/-- `withExclusive` into a subsingleton: the obligation is
`Subsingleton.elim` (the `Expr.withAddr` shape). -/
@[inline] def withExcl {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : Bool → β) : β :=
  withExclusive a k (Subsingleton.elim _ _)

-- ConLeche/Kernel/Expr.lean:241
/-- Saturation value of the two 15-bit range fields: a stored
`satRange` reads as "at least `satRange`". -/
def satRange : Nat := 32767

-- ConLeche/Kernel/Expr.lean:254
/-- Loose-bvar-bound field of a packed word (bits 30…16). -/
@[inline] def bvarOfData (w : UInt64) : UInt64 := w / 65536 % 32768

-- ConLeche/Kernel/Expr.lean:257
/-- Fvar-range field of a packed word (bits 15…1). -/
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768

-- ConLeche/Kernel/Expr.lean:260
/-- Has-level-param field of a packed word (bit 0). -/
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1

namespace Expr
-- ConLeche/Kernel/Expr.lean:482
/-- Has-level-param: is level instantiation ever non-trivial here?
One bit, so this read is *exact*. -/
@[inline] def hasLP (e : Expr) : Bool := lpOfData e.data
-- frontx_ind Expr.hasLP on TExpr

-- ConLeche/Kernel/Expr.lean:485
/-- The stored loose-bvar bound, saturating at `satRange`. -/
@[inline] def bvarBRaw (e : Expr) : Nat := (bvarOfData e.data).toNat
-- frontx_ind Expr.bvarBRaw on TExpr

-- ConLeche/Kernel/Expr.lean:488
/-- The stored fvar range, saturating at `satRange`. -/
@[inline] def fvarBRaw (e : Expr) : Nat := (fvarOfData e.data).toNat
-- frontx_ind Expr.fvarBRaw on TExpr

-- ConLeche/Kernel/Expr.lean:790
/-- `true` for the nodes whose comparison recurses.  The memo is
consulted and written **only** at these: a `bvar`, `sort`, `const` or
`lit` pair is decided without a descent, so an entry for it can never
save a walk and every one of them costs a probe, a bucket cons cell
and, at the end of the call, its `lean_dec_ref`.  Leaves are the
majority of the nodes of a real term. -/
@[inline] def beqRecursive : Expr → Bool
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false
-- frontx_ind Expr.beqRecursive on TExpr

-- ConLeche/Kernel/Expr.lean:795
/-- Is the expression an application?  The spine test of `beqGoX`. -/
@[inline] def beqIsApp : Expr → Bool
  | .app .. => true
  | _ => false
-- frontx_ind Expr.beqIsApp on TExpr

-- ConLeche/Kernel/Expr.lean:804
/-- A memo entry: the pair of objects a completed descent proved
equal, the addresses the descent saw them at, and the proof.  The
proof is erased; the addresses are the probe's cheap filter; the
objects are what the probe verifies against (`probeHit`) — and
holding them is what keeps their addresses theirs. -/
structure EqPair where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : fst = snd

-- ConLeche/Kernel/Expr.lean:813
/-- The default a probe reads on a miss: no object has address `0`,
so its filter never passes at runtime. -/
def EqPair.dflt : EqPair := ⟨.bvar 0, .bvar 0, 0, 0, rfl⟩

-- ConLeche/Kernel/Expr.lean:816
/-- The memo: keyed on the packed address pair (`beqKey`). -/
abbrev BeqMap := Std.HashMap Nat EqPair

-- ConLeche/Kernel/Expr.lean:824
/-- The memo key of a pair of addresses, packed into ONE small `Nat`:
a `Nat × Nat` key would be a `Prod` cell allocated on every probe and
every write, while a `Nat` below `2^62` is a tagged scalar and costs
nothing.  The packing need not be injective — the probe verifies the
stored pair itself — so a collision between distinct pairs costs an
entry, never an answer. -/
@[inline] def beqKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

-- ConLeche/Kernel/Expr.lean:830
/-- `withPtrAddr` into a subsingleton: its side condition — the
continuation's result does not depend on the address — is then
`Subsingleton.elim`. -/
@[inline] def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

-- ConLeche/Kernel/Expr.lean:840
/-- **The specification of expression equality**: the structural
decision, the one the kernel, `by decide` and `#guard` reduce (the
instance below).  No `deriving DecidableEq` (task #554): compiled code
runs `decEqPtr` in its place (`decEq_eq_decEqPtr`), and the only
compiled reference to this body is `ptrDecStruct`'s pure-model fallback,
which compiled code never reaches. -/
def decEq : (a b : Expr) → Decidable (a = b)
  | .bvar x0, .bvar y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .fvar x0 x1, .fvar y0 y1 =>
    if h0 : x0 = y0 then
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .sort x0, .sort y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .const x0 x1, .const y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0; subst h1; rfl)
      else isFalse (fun e => h1 (by injection e <;> assumption))
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .app x0 x1, .app y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .lam x0 x1, .lam y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .forallE x0 x1, .forallE y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .letE x0 x1 x2, .letE y0 y1 y2 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        match decEq x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .lit x0, .lit y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .proj x0 x1 x2, .proj y0 y1 y2 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        match decEq x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
      else isFalse (fun e => h1 (by injection e <;> assumption))
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .bvar .., .fvar .. | .bvar .., .sort .. | .bvar .., .const ..
  | .bvar .., .app .. | .bvar .., .lam .. | .bvar .., .forallE ..
  | .bvar .., .letE .. | .bvar .., .lit .. | .bvar .., .proj ..
  | .fvar .., .bvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .const ..
  | .sort .., .app .. | .sort .., .lam .. | .sort .., .forallE ..
  | .sort .., .letE .. | .sort .., .lit .. | .sort .., .proj ..
  | .const .., .bvar .. | .const .., .fvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .proj ..
  | .app .., .bvar .. | .app .., .fvar .. | .app .., .sort ..
  | .app .., .const .. | .app .., .lam .. | .app .., .forallE ..
  | .app .., .letE .. | .app .., .lit .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .sort ..
  | .lam .., .const .. | .lam .., .app .. | .lam .., .forallE ..
  | .lam .., .letE .. | .lam .., .lit .. | .lam .., .proj ..
  | .forallE .., .bvar .. | .forallE .., .fvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .proj ..
  | .letE .., .bvar .. | .letE .., .fvar .. | .letE .., .sort ..
  | .letE .., .const .. | .letE .., .app .. | .letE .., .lam ..
  | .letE .., .forallE .. | .letE .., .lit .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .sort ..
  | .lit .., .const .. | .lit .., .app .. | .lit .., .lam ..
  | .lit .., .forallE .. | .lit .., .letE .. | .lit .., .proj ..
  | .proj .., .bvar .. | .proj .., .fvar .. | .proj .., .sort ..
  | .proj .., .const .. | .proj .., .app .. | .proj .., .lam ..
  | .proj .., .forallE .. | .proj .., .letE .. | .proj .., .lit .. =>
    isFalse (fun e => Expr.noConfusion e)

-- ConLeche/Kernel/Expr.lean:949
/-- Identity, decided, inside the equality itself: the pointer test at
runtime, the structural decision in the pure model.  The equality's own
probes (`enterBeq`'s `pa == pb`, `probeHit`'s passed filter) reach it
on equal addresses only, where the runtime pointer test answers
`isTrue` and the fallback is not run; it is the one compiled reference
to the structural `decEq`, which `decEqPtr` does not exist yet to
replace.  Code outside the equality uses `ptrDec`. -/
@[inline] def ptrDecStruct (a b : Expr) : Decidable (a = b) :=
  ConLeche.ptrDecEq a b (fun _ => decEq a b)

-- ConLeche/Kernel/Expr.lean:960
/-- Does the entry at `key` identify the pair `(a, b)`?  The stored
addresses are the filter; the stored objects, tested by identity, are
the verification, and the proof behind a `true` is the entry's own.
At runtime a passed filter is an identity match, so `ptrDecStruct` decides
by pointer and never walks.  Not inlined, with everything borrowed: the
structural fallback inside `ptrDecStruct` takes its terms owned, and a
term that is an owned argument in `beqGoX` would make the descent's own
parameters owned (see `BeqSt.recordEq`). -/
@[noinline] def probeHit (m : @& BeqMap) (key : Nat) (pa pb : USize) (a b : @& Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key EqPair.dflt
  if p.pa == pa && p.pb == pb then
    match ptrDecStruct p.fst a, ptrDecStruct p.snd b with
    | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
    | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

/-! ### The memo discipline: memoise only what is shared (task #319)

The memo is the substitution walks' (`ConLeche/Cached/ExprOpsC.lean`,
"The substitution walks"), and the tree has ONE such discipline: at
every recursive child position `withExclusive`
(`ConLeche/Kernel/Exclusive.lean`) reads the count of the BORROWED
node, and only a pair whose two nodes are both SHARED is probed and
recorded — a pair with an exclusive side cannot be queried again
within this comparison, so it costs no key, no probe and no entry.
This is the official kernel's `expr_eq_fn::check_cache` guard
(`src/kernel/expr_eq_fn.cpp`: `if (is_shared(a) && is_shared(b))` in
front of the probe and the write), which the task #240 record could
not port because a Lean walk saw its arguments owned; task #317's
`withExclusive` reads a borrowed node's count, and `beqGoX`'s terms
are borrowed already.

The child step `enterBeq` plays `enter*P`'s part: the pointer test,
the computed-word test, the leaf test, then the two exclusivity
reads.  There is NO cutoff — the node budget that used to keep the
table away from small comparisons was the tree's second heuristic
cutoff after the walks' and went with it (task #319) — so the table
appears at the first shared/shared pair proved equal, the root pair
is never asked (it reaches `beqGoX` past `beqMemo`'s pointer and word
tests and cannot recur), and nothing bounds the table but the
comparison's own end.  The entries are `EqPair`s (the pair, its two
addresses, and its proof), the key is the packed address pair
(`beqKey`), and a hit is validated by identity on BOTH stored objects
(`probeHit`) — self-proving entries, so there is no table invariant
and no lemma about the table at all.  Every branch returns its state
(`BeqSt`: `fail`, or the memo) with the proof that it is not `fail`
exactly when its own `a`, `b` are equal, behind the quotient; the
per-node result is the state object itself, so the descent allocates
only the memo's entries, as official's `apply` returning a `bool`
(task #574).  `beqMemo_eq` is three lines, as it always was.

The table is `Std.HashMap`, created at the first recorded pair.
Official's `ptr_pair_set` (`src/kernel/ptr_pair_set.h`) keeps its first
16 slots inline in the `expr_eq_fn` object and allocates only on growth;
a Lean value has no caller frame to live in, so its twin would be the
first pairs as scalar fields of `BeqSt` itself.  `BeqSt.table`'s field,
`BeqSt.record` and `probeHit` are the only places the table type
appears (task #574 record, DESIGN.md). -/
-- frontx_ind Expr.probeHit on TExpr

-- ConLeche/Kernel/Expr.lean:1022
/-- The state the descent threads, verdict and memo in one word: `fail`
once a pair proved unequal (a `false` aborts the whole comparison, so
the memo is dead from then on), `empty` before the first recorded pair,
`table m` after it.  `fail` and `empty` are scalars and a pass-through
returns the state it was given, so a node's comparison allocates
nothing but the memo's own growth — the official kernel's `apply`
returns a `bool` beside a member `m_cache` (`src/kernel/expr_eq_fn.cpp`).
The table type is this constructor's field: a different memo
representation replaces `BeqMap` here and in `BeqSt.record`/`probeHit`
and nowhere else. -/
inductive BeqSt where
  | fail
  | empty
  | table (m : BeqMap)

-- ConLeche/Kernel/Expr.lean:1028
section
/-- Is the comparison still going (no unequal pair found)? -/
@[inline] def BeqSt.ok : BeqSt → Bool
  | .fail => false
  | _ => true
end

-- ConLeche/Kernel/Expr.lean:1034
section
/-- The write-back: the entry under its key, in the table or in a
fresh one.  Never `fail`: it is applied to a completed `true` only. -/
@[inline] def BeqSt.record (st : BeqSt) (key : Nat) (p : EqPair) : BeqSt :=
  match st with
  | .table m => .table (m.insert key p)
  | _ => .table (({} : BeqMap).insert key p)
end

-- ConLeche/Kernel/Expr.lean:1039
theorem BeqSt.record_ok (st : BeqSt) (key : Nat) (p : EqPair) :
    (st.record key p).ok = true := by
  cases st <;> rfl

-- ConLeche/Kernel/Expr.lean:1049
/-- The write-back of a proved-equal pair at its addresses: the entry
built here, from BORROWED terms.  Not inlined: in `beqGoX` the child
terms are also passed on in tail calls, and a term that is a
constructor argument there is owned, which would make the descent's
own parameters owned (the compiler keeps a self tail call by owning
the parameter an owned argument is passed to). -/
@[noinline] def BeqSt.recordEq (st : BeqSt) (a b : @& Expr) (pa pb : USize) (h : a = b) :
    BeqSt :=
  st.record (beqKey pa pb) ⟨a, b, pa, pb, h⟩
-- frontx_ind Expr.BeqSt.recordEq on TExpr

-- ConLeche/Kernel/Expr.lean:1057
/-- A state the descent may enter a node with: one that is not `fail`.
A subtype, so the proof is erased and the descent's parameter is the
`BeqSt` itself (an extra `Prop` parameter would make the compiler split
off a reduced-arity copy, which drops the terms' borrow annotations). -/
abbrev BeqOk := { s : BeqSt // s.ok = true }

-- ConLeche/Kernel/Expr.lean:1064
/-- The result as the descent returns it: the state, with the proof
that it is not `fail` exactly when the pair is equal, behind a quotient
identifying all of them, so that it is a subsingleton — the decision is
fixed by the proof and the memo is unobservable.  Subtype and quotient
are erased by the compiler: at runtime this is the `BeqSt` itself. -/
abbrev BeqOutX (a b : Expr) := Squash { s : BeqSt // s.ok = true ↔ a = b }
-- frontx_ind Expr.BeqOutX on TExpr

-- ConLeche/Kernel/Expr.lean:1067
section
/-- An equal pair: the state passes through. -/
@[inline] def BeqOutX.yes {a b : Expr} (st : BeqOk) (h : a = b) : BeqOutX a b :=
  Quot.mk _ ⟨st.1, fun _ => h, fun _ => st.2⟩
end

-- ConLeche/Kernel/Expr.lean:1071
section
/-- An unequal pair: `fail`, and the memo is dropped. -/
@[inline] def BeqOutX.no {a b : Expr} (h : ¬ a = b) : BeqOutX a b :=
  Quot.mk _ ⟨.fail, fun e => Bool.noConfusion e, fun e => absurd e h⟩
end

-- ConLeche/Kernel/Expr.lean:1083
/-- A child's result read as the parent's: the same state, the proof
moved along an equivalence of the two equalities (erased). -/
@[inline] def BeqOutX.cast {a b c d : Expr} (r : BeqOutX a b) (e : (a = b) ↔ (c = d)) :
    BeqOutX c d :=
  Squash.lift r fun r => Quot.mk _ ⟨r.1, r.2.trans e⟩
-- frontx_ind Expr.BeqOutX.cast on TExpr

-- ConLeche/Kernel/Expr.lean:1094
/-- The child step of `beqGoX`: pointer identity, the computed word,
the leaf test, then the exclusivity of each side — an exclusive side
means the pair cannot recur and the descent runs with the memo
untouched; a shared/shared pair is probed, and recorded on a completed
`true`.  The terms are borrowed, so the counts read are the counts of
the references inside the terms (the requirement stated in
`ConLeche/Cached/ExprOpsC.lean`; the check is the IR audit). -/
@[inline] def enterBeq (st : BeqOk) (a b : @& Expr)
    (rec : BeqOk → BeqOutX a b) : BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDecStruct a b) st
  else if h : a.data != b.data then
    .no (fun e => by subst e; simp at h)
  else if !beqRecursive a then rec st
  else withExcl a fun ea =>
    if ea then rec st
    else withExcl b fun eb =>
    if eb then rec st
    else
      let hit : { h : Bool // h = true → a = b } :=
        match st.1 with
        | .table m => probeHit m (beqKey pa pb) pa pb a b
        | _ => ⟨false, fun h => Bool.noConfusion h⟩
      if hh : hit.1 then .yes st (hit.2 hh)
      else Squash.lift (rec st) fun r =>
        if h : r.1.ok then
          .yes ⟨r.1.recordEq a b pa pb (r.2.mp h), BeqSt.record_ok ..⟩ (r.2.mp h)
        else Quot.mk _ r

-- ConLeche/Kernel/Expr.lean:1134
/-- The memoised structural descent, the official kernel's
`expr_eq_fn::apply` (`src/kernel/expr_eq_fn.cpp`): the constructor
cases with the child step (`enterBeq`) in front of every recursive call,
every branch returning its decision for its own `a`, `b` (the module
docstring above says why that is the whole proof).  An application
compares its LAST argument first and then walks down the spine: when
both functions are applications again the descent continues on them
directly — a partial application is neither probed nor recorded nor
word-tested, official's `while (true)` loop over `app_fn` — and the
heads go through the child step.  A `false` aborts the comparison at
every level (`fail`), so no unequal pair is ever re-queried and only
proved-equal pairs are stored.  The root pair reaches it past
`beqMemo`'s pointer and word tests and is never asked.  The terms are
borrowed (`@&`): the write-back is the only consumer that stores
them, and owned terms cost a reference-count pair per node — and the
exclusivity read would then answer `false` at every node
(`ConLeche/Kernel/Exclusive.lean`, "The borrowed-parameter
requirement"). -/
def beqGoX (st : BeqOk) (a b : @& Expr) : BeqOutX a b :=
  match a, b with
  | .bvar i, .bvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.bvar.inj e))) st
  | .fvar i t, .fvar j u =>
    if h : i = j then
      (enterBeq st t u fun s => beqGoX s t u).cast
        ⟨fun h' => by subst h; subst h'; rfl, fun e => (Expr.fvar.inj e).2⟩
    else .no (fun e => h (Expr.fvar.inj e).1)
  | .sort u, .sort v =>
    .mk (if h : u == v then isTrue (by rw [beq_iff_eq.mp h])
         else isFalse (fun e => h (beq_iff_eq.mpr (Expr.sort.inj e)))) st
  | .const n us, .const m vs =>
    .mk (if h : n == m && us == vs then
           isTrue (by
             have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
             have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
             rw [h1, h2])
         else isFalse (fun e => h (by
           obtain ⟨h1, h2⟩ := Expr.const.inj e
           subst h1; subst h2; simp))) st
  | .app f x, .app g y =>
    Squash.lift (enterBeq st x y fun s => beqGoX s x y) fun r₁ =>
      if h₁ : r₁.1.ok then
        have hx : x = y := r₁.2.mp h₁
        let rf : BeqOutX f g :=
          if hf : f.beqIsApp then
            if hg : g.beqIsApp then beqGoX ⟨r₁.1, h₁⟩ f g
            else .no (fun e => by subst e; exact hg hf)
          else enterBeq ⟨r₁.1, h₁⟩ f g fun s => beqGoX s f g
        rf.cast ⟨fun h' => by subst hx; subst h'; rfl, fun e => (Expr.app.inj e).1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.app.inj e).2))
  | .lam t b, .lam t' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
          ⟨fun h' => by subst ht; subst h'; rfl, fun e => (Expr.lam.inj e).2⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.lam.inj e).1))
  | .forallE t b, .forallE t' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
          ⟨fun h' => by subst ht; subst h'; rfl, fun e => (Expr.forallE.inj e).2⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.forallE.inj e).1))
  | .letE t v b, .letE t' v' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        Squash.lift (enterBeq ⟨r₁.1, h₁⟩ v v' fun s => beqGoX s v v') fun r₂ =>
          if h₂ : r₂.1.ok then
            have hv : v = v' := r₂.2.mp h₂
            (enterBeq ⟨r₂.1, h₂⟩ b b' fun s => beqGoX s b b').cast
              ⟨fun h' => by subst ht; subst hv; subst h'; rfl, fun e => (Expr.letE.inj e).2.2⟩
          else .no (fun e => h₂ (r₂.2.mpr (Expr.letE.inj e).2.1))
      else .no (fun e => h₁ (r₁.2.mpr (Expr.letE.inj e).1))
  | .lit l, .lit l' =>
    .mk (if h : l = l' then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.lit.inj e))) st
  | .proj s i e, .proj s' i' e' =>
    if h : s == s' && i == i' then
      (enterBeq st e e' fun s => beqGoX s e e').cast
        ⟨fun h' => by
          have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
          have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
          rw [h1, h2, h'],
         fun e => (Expr.proj.inj e).2.2⟩
    else .no (fun e => h (by
      obtain ⟨h1, h2, _⟩ := Expr.proj.inj e
      subst h1; subst h2; simp))
  | .bvar .., .fvar .. | .bvar .., .sort .. | .bvar .., .const ..
  | .bvar .., .app .. | .bvar .., .lam .. | .bvar .., .forallE ..
  | .bvar .., .letE .. | .bvar .., .lit .. | .bvar .., .proj ..
  | .fvar .., .bvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .const ..
  | .sort .., .app .. | .sort .., .lam .. | .sort .., .forallE ..
  | .sort .., .letE .. | .sort .., .lit .. | .sort .., .proj ..
  | .const .., .bvar .. | .const .., .fvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .proj ..
  | .app .., .bvar .. | .app .., .fvar .. | .app .., .sort ..
  | .app .., .const .. | .app .., .lam .. | .app .., .forallE ..
  | .app .., .letE .. | .app .., .lit .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .sort ..
  | .lam .., .const .. | .lam .., .app .. | .lam .., .forallE ..
  | .lam .., .letE .. | .lam .., .lit .. | .lam .., .proj ..
  | .forallE .., .bvar .. | .forallE .., .fvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .proj ..
  | .letE .., .bvar .. | .letE .., .fvar .. | .letE .., .sort ..
  | .letE .., .const .. | .letE .., .app .. | .letE .., .lam ..
  | .letE .., .forallE .. | .letE .., .lit .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .sort ..
  | .lit .., .const .. | .lit .., .app .. | .lit .., .lam ..
  | .lit .., .forallE .. | .lit .., .letE .. | .lit .., .proj ..
  | .proj .., .bvar .. | .proj .., .fvar .. | .proj .., .sort ..
  | .proj .., .const .. | .proj .., .app .. | .proj .., .lam ..
  | .proj .., .forallE .. | .proj .., .letE .. | .proj .., .lit .. =>
    .no (fun e => Expr.noConfusion e)
termination_by structural a
-- frontx_ind Expr.beqGoX on TExpr

-- ConLeche/Kernel/Expr.lean:1339
/-- Size of the static `bvar` pool. -/
def bvarPoolSize : Nat := 4096

-- ConLeche/Kernel/Expr.lean:1342
@[inherit_doc bvarPoolSize]
def bvarPool : Array Expr := (Array.range bvarPoolSize).map Expr.bvar

-- ConLeche/Kernel/Expr.lean:1346
/-- The `bvar` smart constructor: the pooled node below `bvarPoolSize`,
a fresh one above it.  Same value either way (`mkBvar_eq`). -/
@[inline] def mkBvar (i : Nat) : Expr :=
  if h : i < bvarPool.size then bvarPool[i] else .bvar i
-- frontx_ind Expr.mkBvar on TExpr

end Expr
end ConLeche
namespace ConLeche.Expr
-- ConLeche/Kernel/ExprOps.lean:27
/-- Replace `bvar d` by `v` in `e`, where `d` counts the binders passed on
the way (callers start at the default `d = 0`).  `v` must be closed with
respect to bound variables (an `fvar`, a constant, …); it is not shifted.
Loose `bvar`s above `d` are lowered by one. -/
def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1 f v d) (instantiate1 a v d)
  | .lam ty body => .lam (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .forallE ty body => .forallE (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .letE ty val body =>
    .letE (instantiate1 ty v d) (instantiate1 val v d) (instantiate1 body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1 e v d)
-- frontx_ind Expr.instantiate1 on TExpr

-- ConLeche/Kernel/ExprOps.lean:46
/-- Are all bound-variable references bound within the expression (below
`k` at the root)?  Input declarations must satisfy `looseBVarsBounded 0`.
The pure walk is the specification; the executed function is the
`O(1)` loose-bvar field read (`looseBVarsBoundedFast`, `@[csimp]`
below, task #210 Part B). -/
def looseBVarsBounded (k : Nat) : Expr → Bool
  | .bvar i => i < k
  | .fvar _ _ => true
  | .sort _ | .const _ _ | .lit _ => true
  | .app f a => looseBVarsBounded k f && looseBVarsBounded k a
  | .lam ty body | .forallE ty body =>
    looseBVarsBounded k ty && looseBVarsBounded (k + 1) body
  | .letE ty val body =>
    looseBVarsBounded k ty && looseBVarsBounded k val && looseBVarsBounded (k + 1) body
  | .proj _ _ e => looseBVarsBounded k e
-- frontx_ind Expr.looseBVarsBounded on TExpr

-- ConLeche/Kernel/ExprOps.lean:60
/-- Does the expression contain any free variable (`fvar`)?  Input
declarations must be `fvar`-free; the checker introduces `fvar`s only
internally when opening binders. -/
def hasFvar : Expr → Bool
  | .bvar _ | .sort _ | .const .. | .lit _ => false
  | .fvar .. => true
  | .app f a => hasFvar f || hasFvar a
  | .lam ty body | .forallE ty body => hasFvar ty || hasFvar body
  | .letE ty val body => hasFvar ty || hasFvar val || hasFvar body
  | .proj _ _ e => hasFvar e

/-! ## Derived-field spec functions, and their exactness

The four `@[computed_field]`s of `Expr` (`ConLeche/Kernel/Expr.lean`) are
declared by their recurrences; these are the same recurrences written
as ordinary definitions, together with the equivalences that make a
field read justify the traversal cutoff it guards.  Self-contained:
they mention nothing but `Expr`.  The cached engine's field facts
(`ConLeche/Verify/Cached/Erase.lean`) are stated against them. -/
-- frontx_ind Expr.hasFvar on TExpr

-- ConLeche/Kernel/ExprOps.lean:153
/-- Memoized `bvarBound` (the saturated branch's exact recomputation). -/
def bvarBoundGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .bvar i => (i + 1, memo)
      | .fvar _ _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := bvarBoundGo memo f
        let (ra, memo) := bvarBoundGo memo a
        (max rf ra, memo)
      | .lam ty body | .forallE ty body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rb, memo) := bvarBoundGo memo body
        (max rt (rb - 1), memo)
      | .letE ty val body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rv, memo) := bvarBoundGo memo val
        let (rb, memo) := bvarBoundGo memo body
        (max (max rt rv) (rb - 1), memo)
      | .proj _ _ sub => bvarBoundGo memo sub
    (r, memo.insert e r)

-- ConLeche/Kernel/ExprOps.lean:179
@[inherit_doc bvarBoundGo]
def bvarBoundMemo (e : Expr) : Nat := (bvarBoundGo {} e).1

-- ConLeche/Kernel/ExprOps.lean:183
/-- Memoized `fvarRange` (the saturated branch's exact
recomputation). -/
def fvarRangeGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .fvar idx _ => (idx + 1, memo)
      | .bvar _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := fvarRangeGo memo f
        let (ra, memo) := fvarRangeGo memo a
        (max rf ra, memo)
      | .lam ty body | .forallE ty body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rb, memo) := fvarRangeGo memo body
        (max rt rb, memo)
      | .letE ty val body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rv, memo) := fvarRangeGo memo val
        let (rb, memo) := fvarRangeGo memo body
        (max (max rt rv) rb, memo)
      | .proj _ _ sub => fvarRangeGo memo sub
    (r, memo.insert e r)

-- ConLeche/Kernel/ExprOps.lean:209
@[inherit_doc fvarRangeGo]
def fvarRangeMemo (e : Expr) : Nat := (fvarRangeGo {} e).1

-- ConLeche/Kernel/ExprOps.lean:214
/-- **The loose-bvar bound the checker reads**: the packed field, or —
on the saturated branch alone — the exact memoized recomputation.
Equal to `Expr.bvarBound` unconditionally (`bvarB_eq`). -/
@[inline] def bvarB (e : Expr) : Nat :=
  let r := e.bvarBRaw
  if r == satRange then bvarBoundMemo e else r
-- frontx_ind Expr.bvarB on TExpr

-- ConLeche/Kernel/ExprOps.lean:221
/-- **The fvar range the checker reads**: the packed field, or — on the
saturated branch alone — the exact memoized recomputation.  Equal to
`Expr.fvarRange` unconditionally (`fvarB_eq`). -/
@[inline] def fvarB (e : Expr) : Nat :=
  let r := e.fvarBRaw
  if r == satRange then fvarRangeMemo e else r


/-! ### The range fields are exact; `looseBVarsBounded` and `hasFvar` read them (task #210 Part B)

Moved here from `Verify/Cached/Erase.lean` (task #172 B3a) so that the
executed `looseBVarsBounded` and `hasFvar` can be the `O(1)` field
reads: the tree walks did not finish on task #215's `tower_struct` (a
depth-60 DAG tower in a structure field), where the recursor-generation
checks ask them of the block's types.  Swapped in by `@[csimp]`, as the
memoized walks below: kernel-checked, no trust point, the pure walks
stay the specs.  They come before every executed walk in this file
because those read the loose-bvar bound as their cutoff. -/
-- frontx_ind Expr.fvarB on TExpr

-- ConLeche/Kernel/ExprOps.lean:677
/-- Bump every loose bound variable `≥ cutoff` by `amount`.  Used to
transport a constructor-telescope field domain (parameters, then prior
fields) into a recursor-rule telescope (parameters, motive, minors,
then prior fields): parameter references must skip the extra motive
and minor binders, and by the zeta expansion's substitution to carry
open let-values under binders. -/
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam ty body =>
    .lam (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .forallE ty body =>
    .forallE (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .letE ty v body =>
    .letE (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)
-- frontx_ind Expr.liftLooseBVars on TExpr

-- ConLeche/Kernel/ExprOps.lean:739
/-- Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping
`k` under binders — the inverse of `instantiate1` with a fresh variable
(`fvar` type annotations are not descended into; a well-scoped term has no
`fvar d` inside another variable's annotation). -/
def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx ty => if idx = d then .bvar k else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstract1 f d k) (abstract1 a d k)
  | .lam ty body => .lam (abstract1 ty d k) (abstract1 body d (k + 1))
  | .forallE ty body => .forallE (abstract1 ty d k) (abstract1 body d (k + 1))
  | .letE ty val body =>
    .letE (abstract1 ty d k) (abstract1 val d k) (abstract1 body d (k + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstract1 e d k)
-- frontx_ind Expr.abstract1 on TExpr

-- ConLeche/Kernel/ExprOps.lean:788
/-- Full node count, including `fvar` type annotations.  Termination
measure for predicates that recurse into annotations (but never into
instantiated bodies). -/
def sizeF : Expr → Nat
  | .bvar _ | .sort _ | .const .. | .lit _ => 1
  | .fvar _ ty => sizeF ty + 1
  | .app f a => sizeF f + sizeF a + 1
  | .lam ty body | .forallE ty body => sizeF ty + sizeF body + 1
  | .letE ty val body => sizeF ty + sizeF val + sizeF body + 1
  | .proj _ _ e => sizeF e + 1
-- frontx_ind Expr.sizeF on TExpr

-- ConLeche/Kernel/ExprOps.lean:821
/-- Scope check: every reachable `fvar` index is below `d`,
hereditarily through annotations (the `Bool` mirror of the
verification-side `WScoped`).

Not on any per-memo-op path (task #43): the executed knot's cache
operations run unguarded, justified by the proven call discipline
(`ConLeche/Verify/Cached/DiscC*.lean`).  Remaining executable call sites are the
scope guards on checker-fabricated terms in `ConLeche/Kernel/Core.lean`
(the stuck-major rescues in `majorToCtor`), each O(small
fabricated term) once per fabrication.  TODO(cleanup, task #26):
interning should cache the fvar range per node, making those O(1). -/
def wscopedB : (d : Nat) → Expr → Bool
  | d, .fvar idx ty => idx < d && wscopedB idx ty
  | d, .app f a => wscopedB d f && wscopedB d a
  | d, .lam ty body => wscopedB d ty && wscopedB d body
  | d, .forallE ty body => wscopedB d ty && wscopedB d body
  | d, .letE ty val body =>
    wscopedB d ty && wscopedB d val && wscopedB d body
  | d, .proj _ _ e => wscopedB d e
  | _, .bvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => true
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]
-- frontx_ind Expr.wscopedB on TExpr

-- ConLeche/Kernel/ExprOps.lean:836
/-- Is the expression a ∀? -/
def isForallE : Expr → Bool
  | .forallE .. => true
  | _ => false
-- frontx_ind Expr.isForallE on TExpr

-- ConLeche/Kernel/ExprOps.lean:842
/-- Two λs (`lam = true`) or two ∀s (`lam = false`): their domains and
bodies (the descent of the binder-telescope comparison, `defeqBinders`). -/
def binderPair? : Bool → Expr → Expr → Option (Expr × Expr × Expr × Expr)
  | true, .lam t₁ b₁, .lam t₂ b₂ => some (t₁, b₁, t₂, b₂)
  | false, .forallE t₁ b₁, .forallE t₂ b₂ => some (t₁, b₁, t₂, b₂)
  | _, _, _ => none
-- frontx_ind Expr.binderPair? on TExpr

-- ConLeche/Kernel/ExprOps.lean:848
/-- The head of an application spine. -/
def getAppFn : Expr → Expr
  | .app f _ => getAppFn f
  | e => e
-- frontx_ind Expr.getAppFn on TExpr

-- ConLeche/Kernel/ExprOps.lean:853
/-- The arguments of an application spine, outermost last. -/
def getAppArgs : Expr → List Expr
  | .app f a => getAppArgs f ++ [a]
  | _ => []
-- frontx_ind Expr.getAppArgs on TExpr

-- ConLeche/Kernel/ExprOps.lean:858
/-- Apply to a list of arguments. -/
def mkAppN (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => mkAppN (.app f a) as
-- frontx_ind Expr.mkAppN on TExpr

-- ConLeche/Kernel/ExprOps.lean:880
/-- The body of a syntactic `∀`-telescope (the expression itself when
it is not a `∀`). -/
def piResult : Expr → Expr
  | .forallE _ b => piResult b
  | e => e
-- frontx_ind Expr.piResult on TExpr

-- ConLeche/Kernel/ExprOps.lean:905
/-- The type annotation of a free-variable leaf (the expression itself
otherwise; used to read the domains off an opened telescope's
variables). -/
def fvarTypeD : Expr → Expr
  | .fvar _ ty => ty
  | e => e
-- frontx_ind Expr.fvarTypeD on TExpr

end ConLeche.Expr

-- batch B (Testing/conleche-batches/batchB.lean, branch conleche-batch-b), body verbatim
set_option maxErrors 100000
-- Testing/conleche-batches/batchB.lean: con-leche Expr/Name/List/Option functions (source: Testing/conleche-depth/out/F2.lean.txt, con-leche @6810492c1)
-- Each block: provenance line, then the definition copied verbatim, with its enclosing namespace/open/variable/set_option context.
-- Dependencies (verbatim callees) appear before their callers. `-- frontx_ind` lines are commented out until Expr lands.

-- ConLeche/Kernel/Level.lean:228
section
namespace ConLeche
/-- No duplicates in a list of names. -/
def Name.nodup : List Name → Bool
  | [] => true
  | n :: ns => !ns.contains n && Name.nodup ns
end ConLeche
end
-- frontx_ind Name.nodup on TExpr

-- ConLeche/Kernel/Level.lean:45
section
namespace ConLeche.Level
/-- Are all parameters of `l` among `params`? -/
def allParamsDefined (params : List Name) : Level → Bool
  | .zero => true
  | .succ l => allParamsDefined params l
  | .max l r | .imax l r => allParamsDefined params l && allParamsDefined params r
  | .param n => params.contains n
end ConLeche.Level
end

-- ConLeche/Kernel/Level.lean:254
section
namespace ConLeche
/-- Are all level parameters occurring in `e` among `params`?  Binder
prop-ness data included (task #161): their parameters are level
parameters of the term — `instantiateLevelParams` substitutes into
them, and its composition law needs them covered exactly as it needs
the levels'. -/
def Expr.allLevelParamsDefined (params : List Name) : Expr → Bool
  | .bvar _ => true
  | .fvar _ t => t.allLevelParamsDefined params
  | .sort u => u.allParamsDefined params
  | .const _ us => us.all (Level.allParamsDefined params)
  | .app f a => f.allLevelParamsDefined params && a.allLevelParamsDefined params
  | .lam t b | .forallE t b =>
    t.allLevelParamsDefined params && b.allLevelParamsDefined params
  | .letE t v b => t.allLevelParamsDefined params && v.allLevelParamsDefined params
      && b.allLevelParamsDefined params
  | .lit _ => true
  | .proj _ _ e => e.allLevelParamsDefined params
end ConLeche
end
-- frontx_ind Expr.allLevelParamsDefined on TExpr

-- ConLeche/Kernel/Env.lean:385
section
namespace ConLeche
/-- **The length of a syntactic Π-telescope ending in a SORT**:
`some n` when the expression is `n` Π binders with a `.sort`
residual, `none` when the residual is anything else — a constant that
only *unfolds* to a telescope, say (task #195).  A spine walk: one
child per step, never a tree.

The distinction is what makes `indParamsOk` one-sided.  Official's
telescope loop (`check_inductive_types`, `inductive.cpp`) reduces the
residual to weak head normal form before every binder; at a `.sort`
residual that reduction is the identity and no further binder can
appear, so `n` is exactly the number of binders official counts. -/
def Expr.piSortTeleLen? : Expr → Option Nat
  | .forallE _ body => (Expr.piSortTeleLen? body).map (· + 1)
  | .sort _ => some 0
  | _ => none
end ConLeche
end
-- frontx_ind Expr.piSortTeleLen? on TExpr

-- ConLeche/Kernel/PropRead.lean:43
section
namespace ConLeche
namespace Expr
/-!
# Fast prop-ness off the head symbol (task #168)

Two pure readers that answer "is this type a proposition?" / "is this
term a proof?" from the **head symbol, the arity and the residual sorts of stored
types** — no inference, no reduction, no memo.

Prop-ness is invariant under application: `zeronessOf (imax u v) =
zeronessOf v`, so the zero-ness of the sort of the type of `c a⃗` is
that of `c`'s *stored* type at every arity, over-application included.
The datum a head-symbol reader needs is therefore **one `PropWhen` per
constant** — the zero-ness of the sort of its type, read off the
residual sort of its stored type and instantiated at the use's levels
by `substPW`.

Both readers are three-valued (`some pw` = the datum, `none` = unknown,
fall back to inference).  The kernel's verdict on a datum is exactly the
slow path's `Level.isEquiv u .zero`: `pw == (.ifAllZero [])` ⟺ the
sort is zero at every valuation.

The **"definitely not a proof" arm** (`notProofFast`) needs no model theorem: refusing the
proof-irrelevance shortcut is always sound; its obligation is
kernel-level agreement with the slow path, which the landing census
records (DESIGN.md, task #168).  The **"definitely a proof" arm** is
justified by the squash regime (`prf_of_isProofFast`,
`ConLeche/Model/Rules/ProofFastSound.lean`).
-/
/-- The residual after peeling `k` *syntactic* ∀ binders, whatever
their domains (no substitution — the residual may mention the peeled
binders; the readers only look at its head shape). -/
def peelPis : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ b => peelPis k b
  | _ + 1, _ => none
end Expr
end ConLeche
end
-- frontx_ind Expr.peelPis on TExpr

-- ConLeche/Kernel/PropRead.lean:50
section
namespace ConLeche
namespace Expr
/-- The domain of the `k`-th syntactic ∀ binder (`0` = outermost) of a
telescope, unsubstituted. -/
def binderDom : Nat → Expr → Option Expr
  | 0, .forallE A _ => some A
  | k + 1, .forallE _ b => binderDom k b
  | _, _ => none
end Expr
end ConLeche
end
-- frontx_ind Expr.binderDom on TExpr

-- ConLeche/Kernel/PropRead.lean:56
section
namespace ConLeche
namespace Expr
/-- The number of arguments of an application spine. -/
def numArgs : Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0
end Expr
end ConLeche
end
-- frontx_ind Expr.numArgs on TExpr

-- ConLeche/Kernel/PropRead.lean:73
section
namespace ConLeche
/-- The body of a λ-telescope that is a single bound variable: `some
(k, j)` for `fun x₁ … x_k => x_{k-j}` (the shape of `outParam`,
`semiOutParam`, `optParam`, `autoParam`). -/
def lamProj? : Nat → Expr → Option (Nat × Nat)
  | k, .lam _ b => lamProj? (k + 1) b
  | k, .bvar j => if j < k then some (k, j) else none
  | _, _ => none
end ConLeche
end
-- frontx_ind lamProj? on TExpr

-- ConLeche/Kernel/Basis/Names.lean:18
section
namespace ConLeche
open Name (anonymous)
/-!
# Basis names

The reserved names of the pinned basis blocks (see `ConLeche.Kernel.Basis`).
-/
/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"
end ConLeche
end
-- frontx_ind eqName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:21
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"
end ConLeche
end
-- frontx_ind eqReflName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:24
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"
end ConLeche
end
-- frontx_ind natName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:27
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"
end ConLeche
end
-- frontx_ind natZeroName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:30
section
namespace ConLeche
open Name (anonymous)
/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"
end ConLeche
end
-- frontx_ind natSuccName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:32
section
namespace ConLeche
open Name (anonymous)
def emptyName : Name := anonymous |>.str "Empty"
end ConLeche
end
-- frontx_ind emptyName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:38
section
namespace ConLeche
open Name (anonymous)
/-- The name of the pinned `False` basis type (task #181): the
zero-constructor `Prop`, pinned like `Empty` so that the consistency
corollary about `False` needs no hypothesis about how a stream declares
it. -/
def falseName : Name := anonymous |>.str "False"
end ConLeche
end
-- frontx_ind falseName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:41
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient type. -/
def quotName : Name := anonymous |>.str "Quot"
end ConLeche
end
-- frontx_ind quotName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:44
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient constructor. -/
def quotMkName : Name := quotName |>.str "mk"
end ConLeche
end
-- frontx_ind quotMkName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:47
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Name := quotName |>.str "lift"
end ConLeche
end
-- frontx_ind quotLiftName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:50
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Name := quotName |>.str "ind"
end ConLeche
end
-- frontx_ind quotIndName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:53
section
namespace ConLeche
open Name (anonymous)
/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Name := quotName |>.str "sound"
end ConLeche
end
-- frontx_ind quotSoundName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:63
section
namespace ConLeche
open Name (anonymous)
/-! The names of the string-literal support constants (see
`litShapeOk` in `ConLeche.Kernel.CoreDefs`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(inductive blocks and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/
/-- The name `String`. -/
def stringName : Name := anonymous |>.str "String"
end ConLeche
end
-- frontx_ind stringName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:66
section
namespace ConLeche
open Name (anonymous)
/-- The name `String.ofList`. -/
def stringOfListName : Name := stringName.str "ofList"
end ConLeche
end
-- frontx_ind stringOfListName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:69
section
namespace ConLeche
open Name (anonymous)
/-- The name `List`. -/
def listName : Name := anonymous |>.str "List"
end ConLeche
end
-- frontx_ind listName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:72
section
namespace ConLeche
open Name (anonymous)
/-- The name `List.nil`. -/
def listNilName : Name := listName.str "nil"
end ConLeche
end
-- frontx_ind listNilName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:75
section
namespace ConLeche
open Name (anonymous)
/-- The name `List.cons`. -/
def listConsName : Name := listName.str "cons"
end ConLeche
end
-- frontx_ind listConsName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:78
section
namespace ConLeche
open Name (anonymous)
/-- The name `Char`. -/
def charName : Name := anonymous |>.str "Char"
end ConLeche
end
-- frontx_ind charName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:90
section
namespace ConLeche
open Name (anonymous)
/-- The name `And`: the one propositional structure whose recursor is
rescued on a stuck proof (`majorToCtor`'s `And` branch,
`ConLeche/Kernel/Core.lean`, gated by `andRescueSlots`).  `And` is
pinned (`andPin`, `ConLeche/Kernel/Basis/And.lean`): a record that
declares one of its names and is not the toolchain's block is rejected
(`andPinOk`), the matching block installs through the ordinary
installer, and the built-in prelude supplies it to a stream that does
not declare it — so the name always denotes the toolchain's `And` and
the rescue is always available.  (The rescue's soundness does not rest
on the pin: its certificate is proof irrelevance.) -/
def andName : Name := anonymous |>.str "And"
end ConLeche
end
-- frontx_ind andName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:93
section
namespace ConLeche
open Name (anonymous)
/-- The name `Char.ofNat`. -/
def charOfNatName : Name := charName.str "ofNat"
end ConLeche
end
-- frontx_ind charOfNatName on TExpr

-- ConLeche/Kernel/Basis/Names.lean:118
section
namespace ConLeche
open Name (anonymous)
/-! ## The tolerated axiom

`sorryAx` is the one axiom the checker tolerates as a *declaration*:
an export declares it whenever the module it came from mentions
`sorry`, whether or not anything uses it, so a stream that merely
DECLARES it must not be turned away.  Its record installs nothing —
there is no set model for `∀ (α : Sort u), Bool → α` and there cannot
be one — and therefore any USE of it is a positively detected
unsupported feature: a decline, at the record that uses it
(`unknownConstError`, `ConLeche/Kernel/Core.lean`).  The name lives
here, at the bottom of the kernel, because the decline is decided
where a constant fails to resolve — inside the inference body. -/
/-- The name `sorryAx`. -/
def sorryAxName : Name := anonymous |>.str "sorryAx"
end ConLeche
end
-- frontx_ind sorryAxName on TExpr

-- ConLeche/Kernel/Basis/Builder.lean:67
section
namespace ConLeche
namespace BasisDSL
/-- `Prop` = `Sort 0`. -/
def prop : Expr := .sort .zero
end BasisDSL
end ConLeche
end
-- frontx_ind BasisDSL.prop on TExpr

-- ConLeche/Kernel/Basis/Builder.lean:70
section
namespace ConLeche
namespace BasisDSL
/-- `Type` = `Sort 1`. -/
def type1 : Expr := .sort (.succ .zero)
end BasisDSL
end ConLeche
end
-- frontx_ind BasisDSL.type1 on TExpr

-- ConLeche/Kernel/Basis/Eq.lean:38
section
namespace ConLeche
open BasisDSL
/-- The motive of `Eq.rec`: `∀ (b : α) (t : Eq α a b), Sort u_1`, in
the `α`/`a` binder context (`α` is `#1`, `a` is `#0` at its head). -/
def eqRecMotive : Expr :=
  pi "b" (bv 1) <|
  pi "t" (ap3 (cnst eqName [u]) (bv 2) (bv 1) (bv 0)) (srt u1)
end ConLeche
end
-- frontx_ind eqRecMotive on TExpr

-- ConLeche/Kernel/Basis/Nat.lean:22
section
namespace ConLeche
open BasisDSL
/-!
# The pinned `Nat` basis block

The raw pin — the `Nat` block exactly as an export carries it: the
toolchain's `Init.Prelude` declaration as the parser reads it (the
recursor rules' install-computed fields at their parse placeholders).
A block's check compares its records with these pins (`natA`, …), up to the
records' level-parameter names (`ConLeche/Kernel/Basis.lean`).
-/
/-- The type `Nat`, as a closed constant. -/
def natT : Expr := cnst natName
end ConLeche
end
-- frontx_ind natT on TExpr

-- ConLeche/Kernel/Basis/Nat.lean:37
section
namespace ConLeche
open BasisDSL
/-- The motive of `Nat.rec`: `∀ (t : Nat), Sort u`. -/
def natRecMotive : Expr := pi "t" natT (srt u)
end ConLeche
end
-- frontx_ind natRecMotive on TExpr

-- ConLeche/Kernel/Basis/Nat.lean:41
section
namespace ConLeche
open BasisDSL
/-- The successor minor premise of `Nat.rec`, in the `motive`/`zero`
binder context: `∀ (n : Nat), motive n → motive (Nat.succ n)`. -/
def natRecSucc : Expr :=
  pi "n" natT <|
  pi "n_ih" (.app (bv 2) (bv 0)) <|
  .app (bv 3) (.app (cnst natSuccName) (bv 1))
end ConLeche
end
-- frontx_ind natRecSucc on TExpr

-- ConLeche/Kernel/Basis/Quot.lean:29
section
namespace ConLeche
open BasisDSL
/-!
# The pinned `Quot` basis block

Lean's kernel quotient bundle, pinned as an installed basis block:
`Quot` as a stored inductive with the single constructor `Quot.mk`,
the eliminators `Quot.lift`/`Quot.ind` as stored recursors with one
synthetic rule each (applying the lift/ind slot to the packed
element), and `Quot.sound` as a stored axiom (true in the set model).

The pins below (`quotA`, …) match the exporter's `quot` records (and
`Quot.sound`'s `axiom` record).  Each record stores its slot's pin at the
level-parameter names it declares (`ConLeche/Kernel/Basis.lean`): references
between the package's constants are positional, and the eliminators' rules
carry their comparand level (`.levels`), so no record reads another's names.
-/
/-- The relation argument's type in the `α` binder context:
`α → α → Prop`. -/
def quotRel : Expr := piA (bv 0) (piA (bv 1) prop)
end ConLeche
end
-- frontx_ind quotRel on TExpr

-- ConLeche/Kernel/Basis/Quot.lean:46
section
namespace ConLeche
open BasisDSL
/-- `Quot.lift`'s function slot, in the `α`/`r`/`β` context: `α → β`. -/
def quotLiftF : Expr := pi "a" (bv 2) (bv 1)
end ConLeche
end
-- frontx_ind quotLiftF on TExpr

-- ConLeche/Kernel/Basis/Quot.lean:50
section
namespace ConLeche
open BasisDSL
/-- `Quot.lift`'s coherence slot, in the `α`/`r`/`β`/`f` context:
`∀ a b, r a b → f a = f b`. -/
def quotLiftH : Expr :=
  pi "a" (bv 3) <|
  pi "b" (bv 4) <|
  pi "a" (ap2 (bv 4) (bv 1) (bv 0)) <|
  ap3 (cnst eqName [v]) (bv 4) (.app (bv 3) (bv 2)) (.app (bv 3) (bv 1))
end ConLeche
end
-- frontx_ind quotLiftH on TExpr

-- ConLeche/Kernel/Basis/Quot.lean:77
section
namespace ConLeche
open BasisDSL
/-- `Quot.ind`'s motive slot, in the `α`/`r` context:
`Quot α r → Prop`. -/
def quotIndMotive : Expr :=
  pi "a" (ap2 (cnst quotName [u]) (bv 1) (bv 0)) prop
end ConLeche
end
-- frontx_ind quotIndMotive on TExpr

-- ConLeche/Kernel/Basis/Quot.lean:82
section
namespace ConLeche
open BasisDSL
/-- `Quot.ind`'s minor premise, in the `α`/`r`/`β` context:
`∀ a, β (Quot.mk α r a)`. -/
def quotIndMk : Expr :=
  pi "a" (bv 2) <|
  .app (bv 1) (ap3 (cnst quotMkName [u]) (bv 3) (bv 2) (bv 0))
end ConLeche
end
-- frontx_ind quotIndMk on TExpr

-- ConLeche/Kernel/Basis/And.lean:40
section
namespace ConLeche
open BasisDSL
/-!
# The pinned `And` block

The raw pin — the `And` block exactly as an export carries it: the
toolchain's `Init.Prelude` structure

    structure And (a b : Prop) : Prop where
      intro :: (left : a) (right : b)

as the parser reads it (its projection functions
`And.left`/`And.right` are ordinary definition records of their own).

**Why `And` is pinned, and how that differs from the basis blocks.**
The checker has code for "the" `And`: the stuck-proof rescue
(`majorToCtor`'s `And` branch, `ConLeche/Kernel/Core.lean`) fabricates
`And.intro a b h.1 h.2` for an `And.rec` whose major is a proof that
does not reduce to a constructor.  That branch must be available in
every accepted run, so the name must denote the toolchain's `And`.
Unlike `Eq`, `Nat`, `Empty` and `False`, `And` has no hand-written set
model and is not installed from literals: the fold only RECOGNISES the
block (`andPinOk`, `ConLeche/Kernel/Basis.lean`) and rejects any other
record claiming one of its three names; the matching block then goes
through the ordinary inductive installer, which stores its projection
table like any structure's.  The rescue's soundness needs none of this
(its certificate is proof irrelevance, sound whatever `And` is); the
pin is what makes it *present*.
-/
/-- The name `And.intro`. -/
def andIntroName : Name := andName.str "intro"
end ConLeche
end
-- frontx_ind andIntroName on TExpr

-- ConLeche/Kernel/Basis/And.lean:43
section
namespace ConLeche
open BasisDSL
/-- The name `And.rec`. -/
def andRecName : Name := andName.str "rec"
end ConLeche
end
-- frontx_ind andRecName on TExpr

-- ConLeche/Kernel/Basis/And.lean:62
section
namespace ConLeche
open BasisDSL
/-- The motive of `And.rec`: `And a b → Sort u`, in the `a`/`b` binder
context (`a` is `#1`, `b` is `#0`). -/
def andRecMotive : Expr :=
  pi "t" (ap2 (cnst andName) (bv 1) (bv 0)) (srt u)
end ConLeche
end
-- frontx_ind andRecMotive on TExpr

-- ConLeche/Kernel/Basis/And.lean:68
section
namespace ConLeche
open BasisDSL
/-- The minor premise of `And.rec`:
`(left : a) → (right : b) → motive (And.intro left right)`, in the
`a`/`b`/`motive` binder context. -/
def andRecMinor : Expr :=
  pi "left" (bv 2) <|
  pi "right" (bv 2) <|
  .app (bv 2) (ap4 (cnst andIntroName) (bv 4) (bv 3) (bv 1) (bv 0))
end ConLeche
end
-- frontx_ind andRecMinor on TExpr

-- ConLeche/Kernel/Canon.lean:60
section
namespace ConLeche
/-- The level-parameter renaming a constant's own parameter list
induces: the `i`-th parameter becomes `⟨i⟩`, anything else is left
alone. -/
def canonNameMap (ps : List Name) : Name → Name := fun n =>
  match ps.findIdx? (fun p => p == n) with
  | some i => .num .anonymous i
  | none => n
end ConLeche
end
-- frontx_ind canonNameMap on TExpr

-- ConLeche/Kernel/Level.lean:33
section
namespace ConLeche.Level
/-!
# Level operations

Implementation of universe level comparison, following the official kernel /
nanoda (`level.rs` there): `simplify` normalizes, `leqCore` decides
`eval l ≤ eval r + diff` with the same case order as nanoda's `leq_core`
(so reduction happens the same way), and antisymmetry gives equivalence.

`leqCore`'s termination argument is nontrivial (the `imax` by-cases rule
substitutes into both sides), so it takes fuel.  Running out of fuel — or
hitting a case that is unreachable for simplified input — is reported as
`none`, which callers must never read as a verdict: a check that REQUIRES
a comparison lifts it with `liftFueled`, which DECLINES (our resource
limit).  A comparison against `zero` may read `none` as
"no": `simplify` sends every always-zero level to `zero`, where
`isEquiv` answers on its syntactic fast path.

Soundness of all of this (w.r.t. evaluation of levels into `Nat`) is proved
in `ConLeche.Verify.Level`.
-/
/-- Substitute level parameters: `subst ks vs l` replaces `param k` by the
corresponding `v`.  Unlisted parameters remain. -/
def subst (ks : List Name) (vs : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (subst ks vs l)
  | .max l r => .max (subst ks vs l) (subst ks vs r)
  | .imax l r => .imax (subst ks vs l) (subst ks vs r)
  | .param n => go ks vs n
where
  go : List Name → List Level → Name → Level
  | k :: ks, v :: vs, n => if k = n then v else go ks vs n
  | _, _, n => .param n
end ConLeche.Level
end

-- ConLeche/Kernel/Basis.lean:98
section
namespace ConLeche
/-- **What a recursor's rule reads off its constructor's parameters**, by
name (`recFireComparands`' `.plain` arm): the constructor's parameters
at the recursor's names.  The stream's names must link the two the way
the pin's do: this is the constant part of that comparison. -/
def pinLinkOk (R Rp : List Name) (C Cp : List Name) : Bool :=
  C.map Level.param == Cp.map fun p => Level.subst Rp (R.map Level.param) (.param p)
end ConLeche
end
-- frontx_ind pinLinkOk on TExpr

-- ConLeche/Kernel/ExprOps.lean:848
section
namespace ConLeche.Expr
/-- The head of an application spine. -/
def getAppFn : Expr → Expr
  | .app f _ => getAppFn f
  | e => e
end ConLeche.Expr
end

-- ConLeche/Kernel/CoreDefs.lean:42
section
namespace ConLeche
/-!
# The checker core's fuel-free helpers

The definitions of the core checker that mention no monad, no
`CoreFns` record and no fuel: the delta step and its readers
(`unfoldDefinition`, `unfoldableHead`, `headHint`, `sameConstHeads`),
the literal shapes and their guards (`natLitToConstructor`,
`natLitStored`, `strLitToConstructor`, `strLitStored`, `litShapeOk`,
`rawNatLit?`), the certified `Nat` operations' names, recurrences,
reducts and pins (`natOpNames`, `natDivModNames`, `natOpEquations`,
`natOpResult`, `natOpStoredOk`, …), the structure-η fabrications
(`etaProjs`, `etaFabArgsE`, `andRescueSlots`), the rule
data (`etaRescueTable?`, `recFireComparands`), the ι case split
(`iotaCtorNeverProp`, `iotaCase3`) and the tower entry's readers
(`projGuardRows`, `ProjEntry.typeAt`).

Split out of `ConLeche/Kernel/Core.lean` at task #305 (prep): a
relational description of the core's moves — a relation over `Expr`
and `Env` — must name these without importing the executable bodies,
and every one of them is exactly what such a relation needs.  The
bodies (`whnfCoreBody`, `whnfBody`, `inferBody`, `defeqBody`,
the knot and the fuel constants) stay in `Core.lean`,
which re-exports this module, so every importer of `Core` sees the
names unchanged.  Nothing here was rewritten: the definitions keep
their names, docstrings, attributes and relative order.
-/
/-- **Is the spine's head neither a λ nor a `let`** (nor a loose bound
variable)?  The io grade's claim of such a term, where the term is not
the point, is a membership of its io-inferred type (task #342 L18,
`IORel`): a hereditary claim arises only at an abstraction.  A term in
weak-head normal form that is not a λ has such a head. -/
def Expr.ioNeutral (e : Expr) : Bool :=
  match e.getAppFn with
  | .lam .. | .letE .. | .bvar _ => false
  | _ => true
end ConLeche
end
-- frontx_ind Expr.ioNeutral on TExpr

-- ConLeche/Kernel/CoreDefs.lean:147
section
namespace ConLeche
/-- Are `a` and `b` applications of the *same* constant (the lazy delta
same-head short-circuit: try level and spine congruence before
unfolding both sides)?  Mirrors the official kernel's
`try_eq_const_app`: both sides must actually be applications. -/
def sameConstHeads : Expr → Expr → Bool
  | .app f₁ _, .app f₂ _ =>
    match f₁.getAppFn, f₂.getAppFn with
    | .const n₁ _, .const n₂ _ => n₁ == n₂
    | _, _ => false
  | _, _ => false
end ConLeche
end
-- frontx_ind sameConstHeads on TExpr

-- ConLeche/Kernel/CoreDefs.lean:157
section
namespace ConLeche
/-- The constructor form of a `Nat` literal, one layer:
`n + 1` becomes `Nat.succ (lit n)`, `0` becomes `Nat.zero` (the
official kernel's `natLitToConstructor`, used on recursor majors). -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))
end ConLeche
end
-- frontx_ind natLitToConstructor on TExpr

-- ConLeche/Kernel/CoreDefs.lean:232
section
namespace ConLeche
/-- A `Nat` literal reading of a whnf'd expression: literals and the
`Nat.zero` constant (the official kernel's `rawNatLitExt?`). -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const c [] => if c = natZeroName then some 0 else none
  | _ => none
end ConLeche
end
-- frontx_ind rawNatLit? on TExpr

-- ConLeche/Kernel/CoreDefs.lean:415
section
namespace ConLeche
/-! ## Structural-Nat literal acceleration

The official kernel accelerates the structural `Nat` operations on
literals (GMP-backed there).  Here the fast path is *certified*: an
operation participates only when its defining recurrence equations
hold by definitional equality — checked once, at its check: `checkDecl`
positively rejects a nonstandard definition under one of these names,
so *presence in the store is the certificate* (no runtime flag, no
re-checking; a reduction-time re-check would in fact livelock — the
certification's own `pred zero` equation re-enters the fast path).

The certification runs in the environment *before* the operation is
stored, on the equations with the operation's self-references replaced
by its stored definition value (`Expr.substConst0`): running it
after insertion would let the operation's own just-enabled fast path
discharge its all-literal-argument equations (`pred zero ≡ zero`,
`beq zero zero ≡ true`) vacuously — accepting definitions that
disagree with the fast path on those points, which is unsound.  The
install also pins the operation's and its dependencies' types to the
expected `Nat → … → Nat`/`Bool` shapes (`natOpStoredOk`): the model
reads the operations' function-space memberships off these shapes.

The environment model carries the matching semantic clause: a stored
definition under one of these names satisfies its recurrences, from
which meta-level induction over the literal yields the computed
value.  WF-recursive operations (`div`, `mod`, `gcd`) and string
literals are deferred. -/
def natPredName : Name := natName.str "pred"
end ConLeche
end
-- frontx_ind natPredName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:416
section
namespace ConLeche
def natAddName : Name := natName.str "add"
end ConLeche
end
-- frontx_ind natAddName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:417
section
namespace ConLeche
def natSubName : Name := natName.str "sub"
end ConLeche
end
-- frontx_ind natSubName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:418
section
namespace ConLeche
def natMulName : Name := natName.str "mul"
end ConLeche
end
-- frontx_ind natMulName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:419
section
namespace ConLeche
def natPowName : Name := natName.str "pow"
end ConLeche
end
-- frontx_ind natPowName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:420
section
namespace ConLeche
def natBeqName : Name := natName.str "beq"
end ConLeche
end
-- frontx_ind natBeqName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:421
section
namespace ConLeche
def natBleName : Name := natName.str "ble"
end ConLeche
end
-- frontx_ind natBleName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:422
section
namespace ConLeche
def natDivName : Name := natName.str "div"
end ConLeche
end
-- frontx_ind natDivName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:423
section
namespace ConLeche
def natModName : Name := natName.str "mod"
end ConLeche
end
-- frontx_ind natModName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:424
section
namespace ConLeche
def natGcdName : Name := natName.str "gcd"
end ConLeche
end
-- frontx_ind natGcdName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:425
section
namespace ConLeche
def natLandName : Name := natName.str "land"
end ConLeche
end
-- frontx_ind natLandName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:426
section
namespace ConLeche
def natLorName : Name := natName.str "lor"
end ConLeche
end
-- frontx_ind natLorName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:427
section
namespace ConLeche
def natXorName : Name := natName.str "xor"
end ConLeche
end
-- frontx_ind natXorName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:428
section
namespace ConLeche
def natShiftLeftName : Name := natName.str "shiftLeft"
end ConLeche
end
-- frontx_ind natShiftLeftName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:429
section
namespace ConLeche
def natShiftRightName : Name := natName.str "shiftRight"
end ConLeche
end
-- frontx_ind natShiftRightName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:430
section
namespace ConLeche
def boolName : Name := .str .anonymous "Bool"
end ConLeche
end
-- frontx_ind boolName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:434
section
namespace ConLeche
/-- `eagerReduce` (`Init/Core.lean`: `def eagerReduce (a : α) : α := a`),
the gadget that sets the official kernel's eager flag (task #353). -/
def eagerReduceName : Name := .str .anonymous "eagerReduce"
end ConLeche
end
-- frontx_ind eagerReduceName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:439
section
namespace ConLeche
/-- Is `e` of the form `eagerReduce _ _` — official `is_eager_reduce`
(`type_checker.cpp`): the head constant `eagerReduce`, exactly two
arguments, any universe levels. -/
@[inline] def Expr.isEagerReduce : Expr → Bool
  | .app (.app (.const c _) _) _ => c == eagerReduceName
  | _ => false
end ConLeche
end
-- frontx_ind Expr.isEagerReduce on TExpr

-- ConLeche/Kernel/CoreDefs.lean:442
section
namespace ConLeche
def boolTrueName : Name := boolName.str "true"
end ConLeche
end
-- frontx_ind boolTrueName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:443
section
namespace ConLeche
def boolFalseName : Name := boolName.str "false"
end ConLeche
end
-- frontx_ind boolFalseName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:448
section
namespace ConLeche
/-- Is `e` the constant `Bool.true` — the official kernel's
`is_constant(e, Bool.true)` (`type_checker.cpp:1097`): the name, no
universe levels. -/
def Expr.isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false
end ConLeche
end
-- frontx_ind Expr.isBoolTrue on TExpr

-- ConLeche/Kernel/CoreDefs.lean:480
section
namespace ConLeche
/-- **The certified operations' names**: the fast path fires on them by name, so only a
definition may take one, and its job holds it to the pin; any other declaration at such a
name is refused (`checkConstantVal`, `reservedRecName`). -/
def natOpName (n : Name) : Bool :=
  natOpNames.contains n || natDivModNames.contains n
end ConLeche
end
-- frontx_ind natOpName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:517
section
namespace ConLeche
/-- **A name no block RECURSOR may take**: one a literal guard looks
up, one of the certified `Nat` operations (whose presence in the store IS their certificate, so a
recursor stored under such a name would claim a capability nothing
certified), or `Bool` and its two constructors, whose stored entries the
certified operations' guards read (`natOpTyPinned`, `natOpGuard`; task
#431: the stored recursors replace the generated ones' types, which
must not move a guard).  Type formers and constructors are NOT held to this — a
stream must be able to declare `List`, `List.cons` and `Nat.add` —
which is why the block install spends this predicate on the recursors
alone.  The basis names are `basisNamesOk`'s: a pinned block's own
recursor carries one, and no other declaration may. -/
def reservedRecName (n : Name) : Bool :=
  litGuardNames.contains n ||
    natOpNames.contains n || natDivModNames.contains n ||
    n == boolName || n == boolTrueName || n == boolFalseName
end ConLeche
end
-- frontx_ind reservedRecName on TExpr

-- ConLeche/Kernel/CoreDefs.lean:523
section
namespace ConLeche
/-- The operations (transitively) involved in `c`'s recurrences. -/
def natOpDeps (c : Name) : List Name :=
  if c = natPredName then [natPredName]
  else if c = natAddName then [natAddName]
  else if c = natSubName then [natPredName, natSubName]
  else if c = natMulName then [natAddName, natMulName]
  else if c = natPowName then [natAddName, natMulName, natPowName]
  else if c = natBeqName then [natBeqName]
  else if c = natBleName then [natBleName]
  else if c = natDivName then [natPredName, natSubName, natBleName, natDivName]
  else if c = natModName then [natPredName, natSubName, natBleName, natModName]
  else if c = natGcdName then [natBleName, natModName, natGcdName]
  else if c = natLandName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natLandName]
  else if c = natLorName then
    [natAddName, natSubName, natMulName, natBleName, natDivName, natModName,
     natLorName]
  else if c = natXorName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natXorName]
  else if c = natShiftLeftName then
    [natSubName, natMulName, natBleName, natShiftLeftName]
  else if c = natShiftRightName then
    [natSubName, natBleName, natDivName, natShiftRightName]
  else []
end ConLeche
end
-- frontx_ind natOpDeps on TExpr

-- ConLeche/Kernel/CoreDefs.lean:550
section
namespace ConLeche
/-- The defining recurrence equations of a structural-Nat operation,
over constructor forms with free variables `d`, `d + 1` (the equation
sides are binder-free). -/
def natOpEquations (d : Nat) (c : Name) : List (Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar d natTy
  let y : Expr := .fvar (d + 1) natTy
  let z : Expr := .const natZeroName []
  let s : Expr → Expr := (.app (.const natSuccName []) ·)
  let ap1 : Name → Expr → Expr := fun n a => .app (.const n []) a
  let ap2 : Name → Expr → Expr → Expr := fun n a b =>
    .app (.app (.const n []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  if c = natPredName then
    [(ap1 c z, z), (ap1 c (s x), x)]
  else if c = natAddName then
    [(ap2 c x z, x), (ap2 c x (s y), s (ap2 c x y))]
  else if c = natSubName then
    [(ap2 c x z, x), (ap2 c x (s y), ap1 natPredName (ap2 c x y))]
  else if c = natMulName then
    [(ap2 c x z, z), (ap2 c x (s y), ap2 natAddName (ap2 c x y) x)]
  else if c = natPowName then
    [(ap2 c x z, s z), (ap2 c x (s y), ap2 natMulName (ap2 c x y) x)]
  else if c = natBeqName then
    [(ap2 c z z, bT), (ap2 c z (s y), bF), (ap2 c (s x) z, bF),
     (ap2 c (s x) (s y), ap2 c x y)]
  else if c = natBleName then
    [(ap2 c z y, bT), (ap2 c (s x) z, bF), (ap2 c (s x) (s y), ap2 c x y)]
  else []
end ConLeche
end
-- frontx_ind natOpEquations on TExpr

-- ConLeche/Kernel/CoreDefs.lean:583
section
namespace ConLeche
/-- The reduct of op `c` on literal arguments (`pred` ignores the
second slot): the computation itself, at any size.  The official
kernel's maximum `Nat` size, which refuses a computation that would be too
large, is the cached core's (`natOpRefusal`,
`ConLeche/Cached/StateC.lean`). -/
def natOpResult (c : Name) (a b : Nat) : Option Expr :=
  if c = natPredName then some (.lit (.natVal (a - 1)))
  else if c = natAddName then some (.lit (.natVal (a + b)))
  else if c = natSubName then some (.lit (.natVal (a - b)))
  else if c = natMulName then some (.lit (.natVal (a * b)))
  else if c = natPowName then some (.lit (.natVal (a ^ b)))
  else if c = natDivName then some (.lit (.natVal (a / b)))
  else if c = natModName then some (.lit (.natVal (a % b)))
  else if c = natGcdName then some (.lit (.natVal (Nat.gcd a b)))
  else if c = natLandName then some (.lit (.natVal (Nat.land a b)))
  else if c = natLorName then some (.lit (.natVal (Nat.lor a b)))
  else if c = natXorName then some (.lit (.natVal (Nat.xor a b)))
  else if c = natShiftLeftName then
    some (.lit (.natVal (Nat.shiftLeft a b)))
  else if c = natShiftRightName then
    some (.lit (.natVal (Nat.shiftRight a b)))
  else if c = natBeqName then
    some (.const (if a = b then boolTrueName else boolFalseName) [])
  else if c = natBleName then
    some (.const (if a <= b then boolTrueName else boolFalseName) [])
  else none
end ConLeche
end
-- frontx_ind natOpResult on TExpr

-- ConLeche/Kernel/CoreDefs.lean:631
section
namespace ConLeche
/-- Substitute the level-monomorphic constant `n` by `r` through an
application spine (the certification equations' self-references; the
equation sides are binder-free, so only `app` recurses). -/
def Expr.substConst0 (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConst0 n r f) (Expr.substConst0 n r a)
  | e => e
end ConLeche
end
-- frontx_ind Expr.substConst0 on TExpr

-- ConLeche/Kernel/CoreDefs.lean:641
section
namespace ConLeche
/-- Substitute the level-monomorphic constant `n` by the *closed* term
`r` everywhere, including under binders (the div/mod certificate
statements' and proofs' references to the pinned operation; `r` being
closed, no lifting is needed).  `fvar` annotations are not entered:
the substitution runs on closed input terms only. -/
def Expr.substConstAll (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConstAll n r f) (Expr.substConstAll n r a)
  | .lam ty b =>
    .lam (Expr.substConstAll n r ty) (Expr.substConstAll n r b)
  | .forallE ty b =>
    .forallE (Expr.substConstAll n r ty) (Expr.substConstAll n r b)
  | .letE ty v b =>
    .letE (Expr.substConstAll n r ty) (Expr.substConstAll n r v)
      (Expr.substConstAll n r b)
  | .proj s i e => .proj s i (Expr.substConstAll n r e)
  | e => e
end ConLeche
end
-- frontx_ind Expr.substConstAll on TExpr

-- ConLeche/Kernel/ExprOps.lean:27
section
namespace ConLeche.Expr
/-!
# Expression operations

`instantiate1` opens a binder body: the bound variable `bvar 0` is replaced
by a given expression (in practice an `fvar`, which is closed, so no
de Bruijn shifting of the replacement is needed).

`sizeB` is the termination measure for functions that recurse into
instantiated binder bodies: it counts expression nodes but gives every
`fvar` size 1 regardless of its annotated type.  Instantiating a `bvar`
(size 1) with an `fvar` (size 1) preserves it (`sizeB_instantiate1`), so
`sizeB body < sizeB (forallE n ty body)` keeps holding after opening.
-/
/-- Replace `bvar d` by `v` in `e`, where `d` counts the binders passed on
the way (callers start at the default `d = 0`).  `v` must be closed with
respect to bound variables (an `fvar`, a constant, …); it is not shifted.
Loose `bvar`s above `d` are lowered by one. -/
def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiate1 f v d) (instantiate1 a v d)
  | .lam ty body => .lam (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .forallE ty body => .forallE (instantiate1 ty v d) (instantiate1 body v (d + 1))
  | .letE ty val body =>
    .letE (instantiate1 ty v d) (instantiate1 val v d) (instantiate1 body v (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiate1 e v d)
end ConLeche.Expr
end

-- ConLeche/Kernel/CoreDefs.lean:693
section
namespace ConLeche
/-- Peel a `∀`-telescope along an argument list (the residual type of
a fully applied telescope). -/
def piResidual : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ b, a :: as => piResidual (b.instantiate1 a) as
  | _, _ :: _ => none
end ConLeche
end
-- frontx_ind piResidual on TExpr

-- ConLeche/Kernel/CoreDefs.lean:701
section
namespace ConLeche
/-- The fabricated projections of a structure-eta spine: the
`.proj T j b` nodes, one per field of the family's projection table
(the node is what the table types and reduces). -/
def etaProjs (T : Name) (b : Expr) (nF : Nat) : List Expr :=
  (List.range nF).map fun j => Expr.proj T j b
end ConLeche
end
-- frontx_ind etaProjs on TExpr

-- ConLeche/Kernel/ExprOps.lean:551
section
namespace ConLeche.Expr
/-- Bulk instantiation (task #50): substitute the replacement list `vs`
for the bound variables `bvar d, bvar (d + 1), …` in one traversal —
`vs[0]` replaces `bvar d` (the *innermost* binder of a peeled
telescope), `vs[i]` replaces `bvar (d + i)`; loose `bvar`s above the
range are lowered by `vs.length`.

The semantics is by construction the *fold* of `instantiate1`:

  `instantiateList e (v :: vs) d
     = (instantiateList e vs (d + 1)).instantiate1 v d`

(`instantiateList_cons`, unconditional) — so a chain that consumes a
spine `a₁ … aₖ` outermost-first equals one call at the accumulator list
`[aₖ, …, a₁]`.  In the fold, a replacement inserted early is traversed
again by the later `instantiate1` passes; the `bvar` case reproduces
this by recursing into the replacement with the *earlier-listed*
entries (`vs.take i` — the substitutions the fold applies after
inserting `vs[i]`).  On `bvar`-closed replacements (every checker call
site) that recursion is the identity, and the cost is a single
traversal of `e` instead of `vs.length` traversals. -/
def instantiateList (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar j =>
    if j < d then .bvar j
    else if h : j - d < vs.length then
      instantiateList vs[j - d] (vs.take (j - d)) d
    else .bvar (j - vs.length)
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiateList f vs d) (instantiateList a vs d)
  | .lam ty body =>
    .lam (instantiateList ty vs d) (instantiateList body vs (d + 1))
  | .forallE ty body =>
    .forallE (instantiateList ty vs d) (instantiateList body vs (d + 1))
  | .letE ty val body =>
    .letE (instantiateList ty vs d) (instantiateList val vs d)
      (instantiateList body vs (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiateList e vs d)
termination_by (vs.length, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp [List.length_take]; omega)
    | (apply Prod.Lex.right; simp; omega)
end ConLeche.Expr
end

-- ConLeche/Kernel/CoreDefs.lean:747
section
namespace ConLeche
/-- **The field telescope of an η family's instance** (the opening of
official's `is_unit_like` field loop): the η constructor's type at the
levels `us`, its `nP` parameter binders dropped and instantiated with the
type's arguments `targs` in one pass (official's `binding_body` ×`nP`,
then `instantiate_rev`). -/
def unitFieldTele (cty : Expr) (nP : Nat) (targs : List Expr) : Option Expr :=
  (Expr.peelPis nP cty).map fun body => body.instantiateList targs.reverse
end ConLeche
end
-- frontx_ind unitFieldTele on TExpr

-- ConLeche/Kernel/CoreDefs.lean:781
section
namespace ConLeche
/-- The eta-rescue fabrication's argument spine: the major's type's
arguments, then the major's projections (`etaProjs`). -/
def etaFabArgsE (T : Name) (targs : List Expr) (major : Expr) (nF : Nat) :
    List Expr :=
  targs ++ etaProjs T major nF
end ConLeche
end
-- frontx_ind etaFabArgsE on TExpr

-- ConLeche/Kernel/CoreDefs.lean:792
section
namespace ConLeche
/-- **The telescope check of a spine** (task #342 L18): the
telescope's syntactic arity, nothing else.  It is applied to spines of
the subject (the projection fire, `projCert`; the recursor's own
telescope in `iotaRec`): where the redex is not the point, its spine
fits its head's telescope by the application slots of its own
invariant, and a reduction claims nothing of a redex that is the
point. -/
def teleArityOk (ty : Expr) (args : List Expr) : Bool :=
  (Expr.peelPis args.length ty).isSome
end ConLeche
end
-- frontx_ind teleArityOk on TExpr

-- ConLeche/Kernel/CoreDefs.lean:798
section
namespace ConLeche
/-- Open the first `n` `∀`-binders at fresh free variables `0..n-1`
(each fvar's type is the binder domain, instantiated with the earlier
fvars).  Returns the fvars and the opened body. -/
def openPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e)
  | n + 1, .forallE dom body, i =>
    let fv : Expr := .fvar i dom
    match openPisAtFvars n (body.instantiate1 fv) (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none
end ConLeche
end
-- frontx_ind openPisAtFvars on TExpr

-- ConLeche/Kernel/Expr.lean:254
section
namespace ConLeche
/-- Loose-bvar-bound field of a packed word (bits 30…16). -/
@[inline] def bvarOfData (w : UInt64) : UInt64 := w / 65536 % 32768
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:485
section
namespace ConLeche
namespace Expr
/-- The stored loose-bvar bound, saturating at `satRange`. -/
@[inline] def bvarBRaw (e : Expr) : Nat := (bvarOfData e.data).toNat
end Expr
end ConLeche
end

-- ConLeche/Kernel/ExprOps.lean:153
section
namespace ConLeche.Expr
/-! ## The saturated branch of the packed range fields (task #167)

`Expr.bvarBRaw`/`Expr.fvarBRaw` (`Kernel/Expr.lean`) are the packed
word's 15-bit range fields; they *saturate* at `satRange`.  The
accessors the checker reads — `Expr.bvarB`, `Expr.fvarB` — stay
**exact**: below saturation they are the field, and at saturation they
fall back to a memoized recomputation of the very same recurrence.

Two consequences, and they are the point of the design:

* **no lemma weakens** — `bvarB_eq`/`fvarB_eq`
  (`Verify/Cached/Erase.lean`) are still plain equations with the spec
  functions, so no skip site grows a guard and no invariant is
  threaded anywhere;
* **what saturation costs is time, not truth** — the `O(1)` field read
  becomes an `O(DAG)` walk, and only on a term with `satRange` loose
  bvars (or fvar levels).  The measured maxima on the real streams are
  213 (`init-full`), 488 (`grind-ring-5`) and 4000 (`app-lam`, the
  deepest artificial workload) against `satRange = 32767`.

The walks are **memoized** (an `Std.HashMap` keyed by the node) so
that even the fallback stays linear in the DAG rather than the
unfolded tree — the standing "no unmemoized traversals in executable
paths" rule applies to the saturated branch too. -/
/-- Memoized `bvarBound` (the saturated branch's exact recomputation). -/
def bvarBoundGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .bvar i => (i + 1, memo)
      | .fvar _ _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := bvarBoundGo memo f
        let (ra, memo) := bvarBoundGo memo a
        (max rf ra, memo)
      | .lam ty body | .forallE ty body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rb, memo) := bvarBoundGo memo body
        (max rt (rb - 1), memo)
      | .letE ty val body =>
        let (rt, memo) := bvarBoundGo memo ty
        let (rv, memo) := bvarBoundGo memo val
        let (rb, memo) := bvarBoundGo memo body
        (max (max rt rv) (rb - 1), memo)
      | .proj _ _ sub => bvarBoundGo memo sub
    (r, memo.insert e r)
end ConLeche.Expr
end

-- ConLeche/Kernel/ExprOps.lean:179
section
namespace ConLeche.Expr
@[inherit_doc bvarBoundGo]
def bvarBoundMemo (e : Expr) : Nat := (bvarBoundGo {} e).1
end ConLeche.Expr
end

-- ConLeche/Kernel/ExprOps.lean:214
section
namespace ConLeche.Expr
/-- **The loose-bvar bound the checker reads**: the packed field, or —
on the saturated branch alone — the exact memoized recomputation.
Equal to `Expr.bvarBound` unconditionally (`bvarB_eq`). -/
@[inline] def bvarB (e : Expr) : Nat :=
  let r := e.bvarBRaw
  if r == satRange then bvarBoundMemo e else r
end ConLeche.Expr
end

-- ConLeche/Kernel/CoreDefs.lean:827
section
namespace ConLeche
/-- `hasLooseBVar` with the packed bound's cutoff (task #214, P4): a
node whose loose-bvar bound is at or below `i` has no `bvar i`, so the
walk stops there without descending, so `structUsedLater` calls touch
only the spine of a large telescope, never its shared instance towers.  Read as `hasLooseBVar`
by `Expr.hasLooseBVarB_eq` (`ConLeche/Verify/LooseBVar.lean`). -/
def Expr.hasLooseBVarB (i : Nat) (e : Expr) : Bool :=
  if e.bvarB ≤ i then false else
  match e with
  | .bvar j => i == j
  | .fvar .. => false
  | .sort _ => false
  | .const .. => false
  | .lit _ => false
  | .app f a => hasLooseBVarB i f || hasLooseBVarB i a
  | .lam ty b => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .forallE ty b => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .letE t v b =>
    hasLooseBVarB i t || hasLooseBVarB i v || hasLooseBVarB (i + 1) b
  | .proj _ _ e => hasLooseBVarB i e
end ConLeche
end
-- frontx_ind Expr.hasLooseBVarB on TExpr

-- ConLeche/Kernel/ExprOps.lean:872
section
namespace ConLeche.Expr
/-- Strip `k` leading `∀`s: the binder list (outermost first) and the
body. -/
def stripPis : Nat → Expr → Option (List Expr × Expr)
  | 0, e => some ([], e)
  | k + 1, .forallE ty b =>
    (stripPis k b).map fun (bs, e) => (ty :: bs, e)
  | _ + 1, _ => none
end ConLeche.Expr
end

-- ConLeche/Kernel/CoreDefs.lean:846
section
namespace ConLeche
/-- **Binder `nP + j` is used by the rest of the telescope**: its
variable occurs in the remainder of `cty` after it (a later field's
domain or the result).  The occurrence predicate the positivity check
and the model state their facts in. -/
def structUsedLater (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => rest.hasLooseBVarB 0
  | none => false
end ConLeche
end
-- frontx_ind structUsedLater on TExpr

-- ConLeche/Kernel/CoreDefs.lean:861
section
namespace ConLeche
/-- **The rows of a projection's guard: the field loop of the official
`infer_proj`.**  `r` is the constructor telescope with its parameters and
every field before the current one opened, the current field's variable
at depth `d`; `k` fields remain before the projected one.  A field the
rest of the telescope uses is a row, its domain at depth `d`, and is
opened at its variable; one it does not use is stepped over, as official
does.  The rest's only loose variable is the current field's, so
`hasLooseBVarB 0` is answered by the packed bound at the binder.  The
projected field's domain is the last row.  `none` where the telescope
binds too few fields. -/
def projGuardRowsGo : Nat → Nat → Expr → Option (List (Nat × Expr))
  | 0, d, .forallE dom _ => some [(d, dom)]
  | k + 1, d, .forallE dom body =>
    if body.hasLooseBVarB 0 then
      match projGuardRowsGo k (d + 1) (body.instantiate1 (.fvar d dom)) with
      | some rows => some ((d, dom) :: rows)
      | none => none
    else projGuardRowsGo k (d + 1) body
  | _, _, _ => none
end ConLeche
end
-- frontx_ind projGuardRowsGo on TExpr

-- ConLeche/Kernel/Core.lean:791
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- Is `e` a `String` literal?  (The structure rescue leaves one to the
literal conversion, as lean4#15351's `to_cnstr_when_structure` does.) -/
def Expr.isStrLit : Expr → Bool
  | .lit (.strVal _) => true
  | _ => false
end ConLeche
end
-- frontx_ind Expr.isStrLit on TExpr

-- ConLeche/Kernel/Core.lean:1119
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- Is `e` a literal? -/
def Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false
end ConLeche
end
-- frontx_ind Expr.isLit on TExpr

-- ConLeche/Kernel/Core.lean:1527
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- `Nat.zero` or the literal `0` (official `is_nat_zero`). -/
def Expr.isNatZero : Expr → Bool
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false
end ConLeche
end
-- frontx_ind Expr.isNatZero on TExpr

-- ConLeche/Kernel/Core.lean:1534
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The predecessor of a successor form (official `is_nat_succ`): a
nonzero literal, or `Nat.succ x`. -/
def Expr.natPred? : Expr → Option Expr
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app (.const c []) x => if c = natSuccName then some x else none
  | _ => none
end ConLeche
end
-- frontx_ind Expr.natPred? on TExpr

-- ConLeche/Kernel/Core.lean:1554
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- Is the head of the application spine a projection? -/
def Expr.headIsProj (e : Expr) : Bool :=
  match e.getAppFn with
  | .proj _ _ _ => true
  | _ => false
end ConLeche
end
-- frontx_ind Expr.headIsProj on TExpr

-- ConLeche/Kernel/StdAxioms.lean:34
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-!
# Recognized standard axioms and their prerequisite shapes

A stream may use the standard axioms `propext` and `Classical.choice`.
Both are true in the set-theoretic model — `propext` by extensionality
of propositions (derived through the stored `Iff` recursor),
`Classical.choice` by global choice (through the stored `Nonempty`
recursor) — so the checker accepts exactly these two axioms, after
pinning their types and the *shapes of the inductives they quantify
over* to the toolchain's.  The pins below are hand-written through the
builder in `ConLeche/Kernel/Basis/Builder.lean`.

**Binder annotations (tasks #142, #203, #205).**  A pin carries no
binder name and no binder info — `Expr` has neither field (task #205),
so `propext`'s `{a b : Prop}` and `Classical.choice`'s `{α}` are
`pi`/`piI` for the reader only.  Binders carry no datum either (task
#342), so the comparison `ConstantVal.matchesPin` is plain equality;
`Expr.ErasedEq` — the model's "same denotation" relation, up to `fvar`
type annotations — bridges a hit.
-/
/-- The name `propext`. -/
def propextName : Name := anonymous |>.str "propext"
end ConLeche
end
-- frontx_ind propextName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:37
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Classical.choice`. -/
def choiceName : Name := (anonymous |>.str "Classical") |>.str "choice"
end ConLeche
end
-- frontx_ind choiceName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:40
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff`. -/
def iffName : Name := anonymous |>.str "Iff"
end ConLeche
end
-- frontx_ind iffName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:43
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff.intro`. -/
def iffIntroName : Name := iffName |>.str "intro"
end ConLeche
end
-- frontx_ind iffIntroName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:46
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Iff.rec`. -/
def iffRecName : Name := iffName |>.str "rec"
end ConLeche
end
-- frontx_ind iffRecName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:49
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty`. -/
def nonemptyName : Name := anonymous |>.str "Nonempty"
end ConLeche
end
-- frontx_ind nonemptyName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:52
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty.intro`. -/
def nonemptyIntroName : Name := nonemptyName |>.str "intro"
end ConLeche
end
-- frontx_ind nonemptyIntroName on TExpr

-- ConLeche/Kernel/StdAxioms.lean:55
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Nonempty.rec`. -/
def nonemptyRecName : Name := nonemptyName |>.str "rec"
end ConLeche
end
-- frontx_ind nonemptyRecName on TExpr

-- ConLeche/Kernel/Inductives/StructParts.lean:40
section
namespace ConLeche
/-!
# Shared syntactic generators of the inductive install

The syntactic pieces the block install reads and compares against the
stream: the family and constructor spines and the Π-rewrites of the
generated recursor shape (read by the recursor stage,
`ConLeche/Kernel/Inductives/GenRec.lean`), the projection table's
bodies (`structProjBodies`, stored by `checkStructProjTable` at a
structure-like member), and the occurrence test
(`mentionsAnyConst`).

Line numbers cite lean4lean `Lean4Lean/Inductive/Add.lean`, a
line-by-line port of the official `src/kernel/inductive/inductive.cpp`.
-/
/-! ## The generated recursor's pieces

The reference kernels *generate* the recursor from the block
(lean4lean `Inductive/Add.lean:326-483`, official
`inductive.cpp`'s `mk_rec_infos`); the pieces below spell that shape
syntactically, over the stored type former and constructor types, one
minor premise and one rule per constructor.

**Binders** carry no name, info or other datum (`Expr` has no slot for
them), so the generated telescope is compared against an exported
shape (the standard-axiom pins, `stdAxiomOk`, against the stored
`Iff.rec`/`Nonempty.rec`) by plain equality.  The domains are
re-emitted verbatim. -/
/-- The parameter variables as seen from under `o` extra binders:
`p_k = bvar (o + nP - 1 - k)` — `structFamI`'s argument spine. -/
def structPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (o + nP - 1 - k)
end ConLeche
end
-- frontx_ind structPsAt on TExpr

-- ConLeche/Kernel/Inductives/StructParts.lean:70
section
namespace ConLeche
/-! ## The generated recursor at an indexed family (task #175 indexed)

A non-recursive family `T : ∀ p⃗ ı⃗, Sort w` with constructors
`C_k : ∀ p⃗ f⃗, T p⃗ e⃗_k` (the index expressions `e⃗_k` arbitrary terms
over the parameters and the fields) has the recursor

    ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
      (minor_k : ∀ f⃗, motive e⃗_k (C_k p⃗ f⃗))…
      ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t

(lean4lean `Inductive/Add.lean:326-483`, official `mk_rec_infos`):
the index binders are the type former's own telescope past the
parameters, re-emitted twice — at the motive (over the parameters
alone) and after the minors (lifted under the motive and the `n`
minors); the minor's conclusion applies the motive to the
constructor's residual index expressions (lifted under the extras)
before the constructor spine.  A rule binds no index
(`rulePrefix = nP + 1 + n`). -/
/-- A constructor residual's shape at an indexed family: the family
at exactly the parameter variables (`o` binders below the parameter
frame) followed by `nIdx` index expressions. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppArgs.length == nP + nIdx &&
  cbody.getAppArgs.take nP == structPsAt o nP
end ConLeche
end
-- frontx_ind structCtorResidOk on TExpr

-- ConLeche/Kernel/Inductives/StructParts.lean:78
section
namespace ConLeche
/-- The parameter spine of the generated projection bodies, spelled at
the frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar
(nP - k)`, below the subject `bvar 0`. -/
def structProjPs (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.bvar (nP - k)
end ConLeche
end
-- frontx_ind structProjPs on TExpr

-- ConLeche/Kernel/Inductives/StructParts.lean:86
section
namespace ConLeche
/-- The `j`-th earlier-field substitute in a **tower entry's**
generated type (task #175 wiring): the first-class node `t.j`
(`.proj T j` of the subject), at the frame of the subject
`t = bvar 0`.  Each field's entry stands alone, which is what makes
O4's per-field entry branch real. -/
def structProjArgP (T : Name) (j : Nat) : Expr :=
  Expr.proj T j (Expr.bvar 0)
end ConLeche
end
-- frontx_ind structProjArgP on TExpr

-- ConLeche/Kernel/ExprOps.lean:677
section
namespace ConLeche.Expr
/-- Bump every loose bound variable `≥ cutoff` by `amount`.  Used to
transport a constructor-telescope field domain (parameters, then prior
fields) into a recursor-rule telescope (parameters, motive, minors,
then prior fields): parameter references must skip the extra motive
and minor binders, and by the zeta expansion's substitution to carry
open let-values under binders. -/
def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
  | c, .bvar i => if i ≥ c then .bvar (i + amount) else .bvar i
  | _, .fvar i ty => .fvar i ty
  | _, .sort u => .sort u
  | _, .const n us => .const n us
  | c, .app a b => .app (liftLooseBVars amount c a) (liftLooseBVars amount c b)
  | c, .lam ty body =>
    .lam (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .forallE ty body =>
    .forallE (liftLooseBVars amount c ty) (liftLooseBVars amount (c + 1) body)
  | c, .letE ty v body =>
    .letE (liftLooseBVars amount c ty) (liftLooseBVars amount c v)
      (liftLooseBVars amount (c + 1) body)
  | _, .lit l => .lit l
  | c, .proj s i e => .proj s i (liftLooseBVars amount c e)
end ConLeche.Expr
end

-- ConLeche/Kernel/ExprOps.lean:934
section
namespace ConLeche.Expr
/-! ### `instantiateLift`: the capture-avoiding substitution of several variables at once

`bvar (d + j)` (`j` below the values' count) becomes value `j` lifted
past the `d` binders crossed, and the variables above the values are
lowered by their count: what peeling a telescope at **open** values
does to a binder domain, in one walk (the official kernel's
`instantiate` at open values; `Verify/Subst.lean`'s
`instSeqLift_eq_instantiateLift` reads it as the binder-by-binder
`instantiate1Lift` fold).  `structProjBodies` builds each projection
body with one call.  The specification: the cached driver executes
`instantiateLiftC` (`ConLeche/Cached/ExprOpsC.lean`, the cutoff and
the pointer-keyed walk, `instantiateLiftC_spec`). -/
/-- Instantiate `bvar d, bvar (d + 1), …` at the values `vs` (innermost
first), lifting each value past the `d` binders crossed. -/
def instantiateLift (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match e with
  | .bvar j =>
    if j < d then .bvar j
    else if h : j - d < vs.length then Expr.liftLooseBVars d 0 vs[j - d]
    else .bvar (j - vs.length)
  | .fvar idx ty => .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (instantiateLift f vs d) (instantiateLift a vs d)
  | .lam ty body =>
    .lam (instantiateLift ty vs d) (instantiateLift body vs (d + 1))
  | .forallE ty body =>
    .forallE (instantiateLift ty vs d) (instantiateLift body vs (d + 1))
  | .letE ty val body =>
    .letE (instantiateLift ty vs d) (instantiateLift val vs d)
      (instantiateLift body vs (d + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (instantiateLift e vs d)
end ConLeche.Expr
end

-- ConLeche/Kernel/Inductives/StructParts.lean:105
section
namespace ConLeche
/-- **The projection bodies of a recognised block** (task #175 S1),
one walk of the constructor telescope: the parameter binders are
skipped, and field `i`'s raw domain is instantiated once
(`Expr.instantiateLift`) at the values of the binders before it,
innermost first — the subject's earlier projections `.proj T j (bvar
0)` (`structProjArgP`), then the parameters as the loose variables
`structProjPs nP` (parameter `k` at `bvar (nP - k)`, the subject
reserved at `bvar 0`).  So `bodies[i] = F_i[p⃗ ↦ bvars, f_j ↦ .proj T
j (bvar 0)]`, scoped at `nP + 1`: what a `.proj T i e` use
instantiates in one `instantiateList` along the subject type's
arguments and the subject (`ProjEntry.typeAt`).  The values are
threaded down the telescope (`vs`, one cons per field), the rest of
the telescope is never rewritten.  The table holds every field (the
official `infer_proj` restriction at a `Prop`-declared structure is
checked at the use, `projGuardRows`); no entry is inferred or
pinned. -/
def structProjBodiesGo (T : Name) (vs : List Expr) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body =>
    (structProjBodiesGo T (structProjArgP T i :: vs) k (i + 1) body).map
      (fdom.instantiateLift vs :: ·)
  | _ + 1, _, _ => none
end ConLeche
end
-- frontx_ind structProjBodiesGo on TExpr

-- ConLeche/Kernel/Inductives/StructParts.lean:125
section
namespace ConLeche
/-! ## `mentionsAnyConst`: the positivity walk's question at k names -/
/-- Does any of the constants `names` occur in `e`?  A syntactic walk
(`fvar` annotations included; a `.proj` node names its structure), at a
list of names, so that the k-ary positivity walk does ONE traversal per
field domain and not one per member; the fold's `sorryAx` test
(`unresolvedConstsError`, `ConLeche/Kernel/CheckerBase.lean`) asks it
at one name. -/
def Expr.mentionsAnyConst (names : List Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => false
  | .const n _ => names.contains n
  | .fvar _ ty => ty.mentionsAnyConst names
  | .app f a => f.mentionsAnyConst names || a.mentionsAnyConst names
  | .lam ty b | .forallE ty b => ty.mentionsAnyConst names || b.mentionsAnyConst names
  | .letE ty v b =>
    ty.mentionsAnyConst names || v.mentionsAnyConst names || b.mentionsAnyConst names
  | .proj s _ e => names.contains s || e.mentionsAnyConst names
end ConLeche
end
-- frontx_ind Expr.mentionsAnyConst on TExpr

-- ConLeche/Kernel/Inductives/FieldTele.lean:47
section
namespace ConLeche
/-- All leading `∀` binders of an expression (outermost first) and
the body — a recursive field's own telescope (`[]` at a finitary
field, the `a⃗ : A⃗` of a reflexive one, task #202). -/
def Expr.piBinders : Expr → List Expr × Expr
  | .forallE ty b =>
    let (bs, e) := piBinders b
    (ty :: bs, e)
  | e => ([], e)
end ConLeche
end
-- frontx_ind Expr.piBinders on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:56
section
set_option linter.unusedSimpArgs false
namespace ConLeche
/-! ## Closing a telescope -/
/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List Expr → Nat → Expr → Expr
  | [], _, body => body
  | dom :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0)
end ConLeche
end
-- frontx_ind closeTelescope on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:245
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-! ## Positivity through containers — ONE function, GATED

The charter (DESIGN.md, "THE CHARTER", items 3–4): there is ONE
positivity function in the kernel; it reduces with the kernel's own
verified whnf (`ops.whnf`, β, δ, ι, …); the theorem to come is
"returns ⇒ the operator is monotone", by inversion of its run.  It
looks through a container at the CONCRETE instantiation `C (t[X])`:
the arguments `t[X]` — λ or not — are substituted into `C`'s
constructors and positivity is checked there, jointly in the member
holes `X` and in the instantiation's own recursive occurrences `Y`.
Nothing is stated or cached about a container in the abstract: the
only cache is keyed by the instantiation.  Official's nested→mutual
encoding is never mirrored: no auxiliary type, constructor or name.

**The holes are variables** (charter item 2: "the holes
are ordinary open terms (members abstracted to fvars)").  Every WHOLE
application of a member to the parameters is abstracted to a free
variable BEFORE the walk (`nestCrest`: `T_m.{lps} p⃗ ↦ X_m`, at `nP + m`,
typed by the former's type at the parameters — a family over the
member's indices), and a container's own applications `C_j q⃗` are
abstracted to its FRAME's holes before its constructors are instantiated
(charter item 4's `Y` holes, keyed by the instantiation, typed by the
container's formers at the key: families over their indices).  So every hole the monotonicity
theorem varies is a variable of the term `ops.whnf` reduces: `whnf`'s
denotation lemma is stated at one environment model, where a constant
reads one fixed leaf, and says nothing about a constant's reading at
other values.  Verdict-neutral: a member is an inductive former with
no δ and, at positivity time, no ι, so a typed variable in its place
changes no reduction; an installed container's own occurrences are at
its canonical parameters, so its frame's hole is met at the frame's
own `Ds` (anything else declines).  A frame abstracts the container's
WHOLE recorded block (`IndCaps.all`) at the instantiation and walks all
their constructors in one pass (N2-eager), as official copies the whole
group; so an
accepted frame reads the joint operator of the container's block at the
instantiation, and an instantiation in progress is only ever met as its
hole — met as a constant (reduction only) it is official's "non valid
occurrence".

**`nestPos`, the function**, by structural recursion on its fuel; its
cases are the monotonicity induction's:

* the whnf of the domain mentions no member — hole-free (`const`);
* a `Π` whose domain mentions no member — recurse on the body (`pi`);
* a hole at its frame's own parameters with hole-free indices, at its
  full arity (`holeApp`, official's `is_valid_ind_app` :338): a member
  hole — the ROOT frame's, at the block's parameters — or a container
  frame's (its instantiation in progress);
* a stored inductive `C` (not a member) applied to parameters `Ds`
  (some mentioning a member, none a field or binder variable — official
  :962) and member-free indices (`contApp`): an instantiation IN
  PROGRESS is a `Y` hole; one already accepted is a cache hit; else its
  checks — (N2) the instantiated index telescope names no member
  (official checks the auxiliary type former before the block exists,
  :219), (N3) its sort `Level.isEquiv` the block's (:250) — and then
  `nestPos` on every field of every constructor of `C` AT the
  instantiation, the instantiation pushed onto the in-progress list,
  and the constructor's result indices member-free;
* anything else — official's "non valid occurrence".

**No basis special-casing** but one: `Quot`, stored as an `.indInfo`
yet no inductive for official, is a "non valid occurrence" as a
container head.  The pinned `Eq`/`Nat`/`Empty`/`False` (and the
stream's `And`) are read from the environment like any stored inductive
— their constructors are `.ctorInfo` records with parameter counts.
The parameter-free ones never reach the container case; `Eq` (two
parameters, `α` and `a`, as official) always ends in official's
verdicts: a field in `a` is a local variable, `@Eq Prop (T p) True`
fails the instantiated `refl`'s result index ("invalid return type"),
`@Eq Prop T T` has a member in an index.

**Fuel** (derived from the input, no fixed limit):
`nestPos` recurses on an explicit fuel, one unit per `Π` body and per
container field descent — per root constructor `whnfWalkFuel` of its
instantiated type (its depth plus a slack, see "The input-derived fuel"
below), so a
telescope or a nesting written out in the input never exhausts it.
Running out THROWS
`.notImplemented` — a decline (exit 2), never an accept.  The cache of
instantiations is unbounded: every entry is a frame the walk completed.

**The seeds**: the stream's recursor family names official's
auxiliary types as its outside majors (the recursor check's classes);
the recursor check walks every class it resolved at the root like a
container instance met there (`nestSeeds`, "The seeds" below), so every
class is a node BY CONSTRUCTION — an occurrence whnf erases among
them.

**Accepted superset of official** (the charter's item 8; with an e2e
fixture; a reject-only check would go into a separate unverified
stage, never into this function): official locates
nested instances SYNTACTICALLY, before any whnf (`replace_all_nested`
:1043), so a container reached only by reduction (`F T`,
`F α := List α`) is a "non valid occurrence" there; here the container
case reads the whnf, so it accepts (`corner_nestpos_redex_bad`, D1).
A container with NO constructor is read at its RECORDED parameter
count (`IndCaps.nparams`); its frame walks nothing.

**Who calls it.**  The check's positivity stage runs the walk
(`checkBlockPositivity`, `nestRoot`); `nestedBlockPositivity` is
the unit tests' entry, on a hand-built context.
-/
/-- Does a MEMBER or a HOLE occur in `e`?  Official's `has_ind_occ`:
member constants, and here also the hole variables `lo ..< hi` — a free
variable's annotation is NOT looked into (a local's type lives in the
local context, not in the term) and a `.proj` node's structure name is
no occurrence.  The specification; the cached tier runs `nestOccC`. -/
def Expr.nestOcc (names : List Name) (lo hi : Nat) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .lit _ => false
  | .fvar i _ => decide (lo ≤ i ∧ i < hi)
  | .const n _ => names.contains n
  | .app f a => nestOcc names lo hi f || nestOcc names lo hi a
  | .lam ty body => nestOcc names lo hi ty || nestOcc names lo hi body
  | .forallE ty body => nestOcc names lo hi ty || nestOcc names lo hi body
  | .letE ty val body =>
    nestOcc names lo hi ty || nestOcc names lo hi val || nestOcc names lo hi body
  | .proj _ _ sub => nestOcc names lo hi sub
end ConLeche
end
-- frontx_ind Expr.nestOcc on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:260
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- Instantiate the leading `Π` binders of `e` at `args`, in order
(the parameters of a constructor or a type former). -/
def instPisWith : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body => instPisWith as (body.instantiate1 a)
  | _ :: _, _ => none
end ConLeche
end
-- frontx_ind instPisWith on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:305
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- A term's depth: the longest root-to-leaf path (`fvar` annotations
not descended).  The executed form is the cached tier's memoised
`Expr.depthC` (`depthC_spec`). -/
def Expr.depth : Expr → Nat
  | .app f a => max f.depth a.depth + 1
  | .lam ty body => max ty.depth body.depth + 1
  | .forallE ty body => max ty.depth body.depth + 1
  | .letE ty v body => max (max ty.depth v.depth) body.depth + 1
  | .proj _ _ x => x.depth + 1
  | _ => 1
end ConLeche
end
-- frontx_ind Expr.depth on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:300
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-! ### The input-derived fuel

The walks that read a telescope THROUGH whnf (`nestPos`, and the
recursor stage's `targetWhnfPis`) recurse on an explicit fuel, one unit
per `Π` body and per container descent.  The fuel is derived from the
term the walk starts on: its DEPTH (the longest root-to-leaf path,
`fvar` annotations not descended) bounds every `Π` and every container
argument the term carries syntactically, so a telescope or a nesting
written out in the input never exhausts it; `fuelSlack` on top covers
what the syntax does not show — a container constructor's own fields
walked in a frame, a redex that reduces to a `Π` — and keeps the fuel
at or above 1024.  Running out DECLINES (it takes a
telescope that reduction manufactures beyond both).  No proof reads
the value: the functions' theorems hold at every fuel. -/
/-- The fuel's slack above the term's depth (see the section header). -/
def fuelSlack : Nat := 1024
end ConLeche
end

-- ConLeche/Kernel/Inductives/Positivity.lean:315
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- **The fuel of a walk through whnf** starting at `e`: its depth plus
the slack (see the section header). -/
def whnfWalkFuel (e : Expr) : Nat := e.depth + fuelSlack
end ConLeche
end
-- frontx_ind whnfWalkFuel on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:546
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- The canonical parameter variables `fvar 0, …, fvar (n - 1)`. -/
def nestPhs (n : Nat) : List Expr := (List.range n).map fun i => .fvar i (.sort .zero)
end ConLeche
end
-- frontx_ind nestPhs on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:566
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- The variable replacement of a key: the canonical parameter variable
`i` to the key's parameter `ds[i]`, the canonical hole `|ds| + m` to the
frame's hole `holes[m]`. -/
def nestKeyMap (ds holes : List Expr) : Nat → Option Expr :=
  fun i => if i < ds.length then ds[i]? else holes[i - ds.length]?
end ConLeche
end
-- frontx_ind nestKeyMap on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:625
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- A constructor's result is headed by a variable (its member's hole,
once the members are abstracted) — `checkSumCtor` already checked the
result is the member applied, so this never fires on a checked block;
the monotonicity proof reads the result's spine off it. -/
def nestResHead (e : Expr) : Bool :=
  match e.getAppFn with
  | .fvar .. => true
  | _ => false
end ConLeche
end
-- frontx_ind nestResHead on TExpr

-- ConLeche/Kernel/Inductives/Positivity.lean:985
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-! ### Uniform occurrences: official's `check_uniform_ind_occs`

Official v4.33.1+ (`inductive.cpp` v4.34.1 `check_uniform_ind_occs`,
called first thing by `add_inductive`) walks every constructor type
SYNTACTICALLY — every subterm, `let`s, projections and the parameters'
own domains included — and rejects every occurrence of a member that is
not literally `T.{lps} p⃗`: the declaration's level parameters, applied
to exactly the parameter variables (over-applied, the extra arguments
are walked too; in a parameter's domain every occurrence is rejected).
Reduction never creates such an occurrence (the members are not yet in
the environment), so the syntactic check covers every occurrence a
later reduct could expose or erase.

Here it reads the root frame's canonical crest (`nestRootCanon`): every WHOLE
application `T_m.{lps} p⃗` replaced by the member's hole before the
parameters are instantiated (`nestCanonCrest`) — an over-applied one has its
extra arguments walked — so an occurrence at other levels, or applied to
anything but exactly the parameters, is a member constant left over.
The parameters' domains must be free of members altogether.

The check reads the STORED constructor, which is the declared one,
`let`s included, so an occurrence only in a `let`'s type, or in the
value of a `let` its body never uses, is seen and rejected, as
official does (`uh_let_erase_type`, `uh_let_erase_value`). -/
/-- Does a member or a hole occur in one of the first `n` binder domains
of `e`?  (The parameters' domains, at `n = nP`.) -/
def Expr.piDomsOcc (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE d b => d.nestOcc names lo hi || piDomsOcc names lo hi n b
  | _ + 1, _ => false
end ConLeche
end
-- frontx_ind Expr.piDomsOcc on TExpr

-- ConLeche/Kernel/Inductives/BlockShape.lean:260
section
set_option linter.unusedSimpArgs false
namespace ConLeche
/-- **The member a recursor's MAJOR names** (recursor NAMES are the
stream's business, and what makes a recursor this member's is its major
premise).

Strip the `mI` binders the record claims off the stored type; the next
binder is the MAJOR, and its domain's head constant is read against
the block's member names.  `names.length` — no member — when the type
does not have those binders, when the major's domain heads something
else, or when it heads a constant outside the block: a NESTED block's
auxiliary recursors are exactly that (their majors are the containers
official's auxiliary block carries, not the block's own members). -/
def recTargetOf (names : List Name) (mI : Nat) (ty : Expr) : Nat :=
  match ty.stripPis mI with
  | some (_, .forallE dom _) =>
    (match dom.getAppFn with
     | .const n _ => names.findIdx? (· == n)
     | _ => none).getD names.length
  | _ => names.length
end ConLeche
end
-- frontx_ind recTargetOf on TExpr

-- ConLeche/Kernel/TrustPins.lean:43
section
namespace ConLeche
open BasisDSL
/-!
# Pinned compiler-trust opaque values (task #95; hand-written since task #273)

The pinned defining expressions of the toolchain's `Lean.reduceNat` /
`Lean.reduceBool` opaques: the plain identity functions, written with
the same builder (`ConLeche/Kernel/Basis/Builder.lean`) that
`ConLeche/Kernel/TrustAxioms.lean` writes the family's axiom shapes,
`Lean.trustCompiler` and the types with.  At install (`checkReducePin`
in `ConLeche/Kernel/Checker.lean`) the stream's stored opaque value is
compared against the pin by definitional equality — drift declines,
never silently — and the identity certificate `value x ≡ x` is what
the model consumes (`EnvModel.reduce_ops`).

**Nothing here reads the compiling environment.**  Until task #273
these two pins were GENERATED at elaboration time (`#gen_trust_pins`,
reading `Lean.reduceBool`/`reduceNat` out of the COMPILING toolchain's
`Init`), which made the binary's behaviour depend on the toolchain
that compiled it — the one such dependency left once the Nat-op pins
became committed files — and lean4 master has removed the two opaques
(with `Lean.trustCompiler` and the `ofReduce*` axioms) from `Init`
altogether, so there was nothing to read there.  The user's ruling:
*"the host toolchain of the binary is irrelevant for our purposes; if
not, there is a design flaw."*  The pin has been the same on every
toolchain that had the opaques —
`opaque reduceBool (b : Bool) : Bool := have := trustCompiler; b`,
whose `have` the conversion zeta-expanded away, leaving `fun b => b` —
so it is written down here once.  Should a toolchain ever respell the
opaques, the block comparison declines its streams and the
toolchain matrix (`scripts/natop-matrix.sh`) shows it; no
generator-side assertion is kept.
-/
/-- `Lean.reduceBool`'s pinned value: `fun (b : Bool) => b`. -/
def reduceBoolDeclPin : Expr := lm "b" (cnst (bn "Bool")) (bv 0)
end ConLeche
end
-- frontx_ind reduceBoolDeclPin on TExpr

-- ConLeche/Kernel/TrustPins.lean:46
section
namespace ConLeche
open BasisDSL
/-- `Lean.reduceNat`'s pinned value: `fun (n : Nat) => n`. -/
def reduceNatDeclPin : Expr := lm "n" (cnst (bn "Nat")) (bv 0)
end ConLeche
end
-- frontx_ind reduceNatDeclPin on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:50
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-!
# The compiler-trust axiom family (task #95)

`Init`'s compiler-trust scaffolding is installed rather than
declined:

* `Lean.trustCompiler : True` is trivially realizable — it is
  installed as an *opaque* (stored `axiomInfo`, exactly like a checked
  `opaque` declaration) with value `True.intro`, over a pinned `True`
  family.  No new meta-axiom: the model is `True.intro`'s own
  interpretation.
* `Lean.reduceNat` / `Lean.reduceBool` then check as ordinary
  `opaque`s (their exported values are identity functions modulo the
  `have := trustCompiler` wrapper); at its check their stored values are
  pinned against the identity function
  (`ConLeche/Kernel/TrustPins.lean`, hand-pinned since task #273 —
  every toolchain's definition after zeta) by definitional equality —
  the task-#47 pattern: drift declines, never silently.
* `Lean.ofReduceNat` / `Lean.ofReduceBool` are pinned axioms over
  those stored opaques (the task-#34 standard-axioms machinery).  With
  the stored reduce operation certified to be the identity (a
  definitional-equality certificate at the operation's own install,
  `checkReducePin`; the axiom's install checks `ofReduceAxOk`),
  `∀ a b, reduceNat a = b → a = b` interprets to
  an inhabited proposition (the hypothesis *is* the conclusion), so
  both axioms are true in the set model with the proof point as value.

`sorryAx` remains the only axiom tolerated as a *declaration*: its
record installs nothing and any use of it declines
(`sorryAxName`, `ConLeche/Kernel/Basis/Names.lean`).

The pins below are hand-written through the builder in
`ConLeche/Kernel/Basis/Builder.lean`.
-/
/-- The name `True`. -/
def trueName : Name := anonymous |>.str "True"
end ConLeche
end
-- frontx_ind trueName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:53
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `True.intro`. -/
def trueIntroName : Name := trueName |>.str "intro"
end ConLeche
end
-- frontx_ind trueIntroName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:56
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.trustCompiler`. -/
def trustCompilerName : Name := (anonymous |>.str "Lean") |>.str "trustCompiler"
end ConLeche
end
-- frontx_ind trustCompilerName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:59
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.reduceNat`. -/
def reduceNatName : Name := (anonymous |>.str "Lean") |>.str "reduceNat"
end ConLeche
end
-- frontx_ind reduceNatName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:62
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.reduceBool`. -/
def reduceBoolName : Name := (anonymous |>.str "Lean") |>.str "reduceBool"
end ConLeche
end
-- frontx_ind reduceBoolName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:65
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.ofReduceNat`. -/
def ofReduceNatName : Name := (anonymous |>.str "Lean") |>.str "ofReduceNat"
end ConLeche
end
-- frontx_ind ofReduceNatName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:68
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The name `Lean.ofReduceBool`. -/
def ofReduceBoolName : Name := (anonymous |>.str "Lean") |>.str "ofReduceBool"
end ConLeche
end
-- frontx_ind ofReduceBoolName on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:74
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The reduce operation an `ofReduce*` axiom speaks about. -/
def ofReduceOp (n : Name) : Name :=
  if n = ofReduceNatName then reduceNatName else reduceBoolName
end ConLeche
end
-- frontx_ind ofReduceOp on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:100
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The element type of a reduce operation, as the pinned constant. -/
def reduceElemTy (c : Name) : Expr :=
  if c = reduceNatName then .const natName [] else .const boolName []
end ConLeche
end
-- frontx_ind reduceElemTy on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:192
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-! ## The reduce-operation install pin -/
/-- The pinned defining expression of a reduce operation
(`ConLeche/Kernel/TrustPins.lean`: the plain identity, hand-written
with the basis builder — every toolchain's `have := trustCompiler; b`
after zeta). -/
def reduceDeclPin (c : Name) : Expr :=
  if c = reduceNatName then reduceNatDeclPin else reduceBoolDeclPin
end ConLeche
end
-- frontx_ind reduceDeclPin on TExpr

-- ConLeche/Kernel/TrustAxioms.lean:203
section
namespace ConLeche
open Name (anonymous)
open BasisDSL
/-- The identity certificate's variable: `fvar 0` at the element
type. -/
def reduceCertVar (c : Name) : Expr :=
  .fvar 0 (reduceElemTy c)
end ConLeche
end
-- frontx_ind reduceCertVar on TExpr

-- ConLeche/Kernel/Inductives/RecCheck.lean:90
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- The holes of a rule frame of width `base`: member `t` is
`.fvar (base + t)` at its former's type. -/
def targetHoles (formerTys : List Expr) (base : Nat) : List Expr :=
  (List.range formerTys.length).map fun t => .fvar (base + t) (formerTys.getD t default)
end ConLeche
end
-- frontx_ind targetHoles on TExpr

-- ConLeche/Kernel/Inductives/RecCheck.lean:134
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- A term with every free variable's ANNOTATION erased (the variable
kept): the comparison K.53′ runs up to, which is exactly what the model's
interpretation never reads (`Expr.ErasedEq`). -/
def Expr.eraseFVarTys (e : Expr) : Expr :=
  e.replaceFVars fun i => some (.fvar i (.sort .zero))
end ConLeche
end
-- frontx_ind Expr.eraseFVarTys on TExpr

-- ConLeche/Kernel/Inductives/RecCheck.lean:161
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-! ### Matching a class against a node, per component

A recursor class `I.{us} D⃗` and an instantiation the positivity check
recorded (a node's key, or a constructor entry's `(lvls, ds)`, read back:
holes as their constants, the parameters at the walk's canonical
variables) MATCH when they agree PER COMPONENT (ruling 2026-09-27): the
levels by `Level.isEquivList`, every parameter by the kernel's defeq —
the block's members abstracted to their holes on both sides
(`targetAbs`, the holes after the class's recursor prefix), every
parameter variable moved to the class's own opener of that index
(`targetCanonParams`, so both sides live over one context whatever
annotations their variables carry), both sides inferred first.  The head is
compared by the caller.  Whole-application defeq would not do: at `Prop`
two instances read alike (`P Nat`, `P Bool`: both `{pt}`) without
sharing a frame; per component, the frames agree at every value of the
holes.  The two comparisons of the recursor check against the
positivity check — the class's recorded normal forms, a call's callee
against its field (K.53′) — both run this one function, so a match
found at one is a match at the other.  (A class is a node of the walk by
construction — its seed, `classSeeds` (`GenRec.lean`) — and matches that node's key
syntactically, up to the free variables' annotations.) -/
/-- A term over the walk's canonical parameter variables, moved to the
class's openers `pfvs` (variables `0 … |pfvs|-1`, the rest kept). -/
def targetCanonParams (pfvs : List Expr) (e : Expr) : Expr :=
  e.replaceFVars fun i => pfvs[i]?
end ConLeche
end
-- frontx_ind targetCanonParams on TExpr

-- ConLeche/Kernel/Inductives/RecCheck.lean:412
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- The domains of the first `|xs|` `∀` binders, each instantiated at the
earlier `xs` (a telescope's field types at given field variables). -/
def targetPiDomsWith : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE d b => (d :: ·) <$> targetPiDomsWith xs (b.instantiate1 x)
  | _ :: _, _ => none
end ConLeche
end
-- frontx_ind targetPiDomsWith on TExpr

-- ConLeche/Kernel/ExprOps.lean:739
section
namespace ConLeche.Expr
/-- Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping
`k` under binders — the inverse of `instantiate1` with a fresh variable
(`fvar` type annotations are not descended into; a well-scoped term has no
`fvar d` inside another variable's annotation). -/
def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  match e with
  | .bvar i => .bvar i
  | .fvar idx ty => if idx = d then .bvar k else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (abstract1 f d k) (abstract1 a d k)
  | .lam ty body => .lam (abstract1 ty d k) (abstract1 body d (k + 1))
  | .forallE ty body => .forallE (abstract1 ty d k) (abstract1 body d (k + 1))
  | .letE ty val body =>
    .letE (abstract1 ty d k) (abstract1 val d k) (abstract1 body d (k + 1))
  | .lit l => .lit l
  | .proj s i e => .proj s i (abstract1 e d k)
end ConLeche.Expr
end

-- ConLeche/Kernel/Inductives/RecCheck.lean:431
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- **The free variables `0 … k-1` closed at cursor `c`**: `fvar i`
becomes `bvar (c + k - 1 - i)`, as `e.abstractRange 0 k c` does
(`abstractPrefix_eq`), stated as the fold of `abstract1` passes,
innermost first (the cached twin `abstractPrefixC` is one
`abstractRangeC` pass). -/
def Expr.abstractPrefix : Nat → Nat → Expr → Expr
  | 0, _, e => e
  | k + 1, c, e => abstractPrefix k (c + 1) (e.abstract1 k c)
end ConLeche
end
-- frontx_ind Expr.abstractPrefix on TExpr

-- ConLeche/Kernel/Inductives/BlockInstall.lean:87
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- Does some binder domain of the SYNTACTIC `∀`-telescope of `e`
mention one of `names`?  No reduction: the walk stops at the first
non-`∀`, as official's `while (is_pi(t))` loop does. -/
def Expr.piDomsMentionAny (names : List Name) : Expr → Bool
  | .forallE ty b => ty.mentionsAnyConst names || b.piDomsMentionAny names
  | _ => false
end ConLeche
end
-- frontx_ind Expr.piDomsMentionAny on TExpr

-- ConLeche/Kernel/Inductives/BlockInstall.lean:274
section
set_option linter.unusedSimpArgs false
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
/-- The field kinds of the root frame's outputs. -/
def nestOutKinds (outs : List (List (List NestFieldKind × Expr))) : List (List (List NestFieldKind)) :=
  outs.map (·.map (·.1))
end ConLeche
end
-- frontx_ind nestOutKinds on TExpr

-- ConLeche/Kernel/Checker.lean:117
section
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The pinned defining expression of a pin-certified WF-recursive op
in one **pin variant** (`ConLeche/Kernel/NatOpPinSet.lean`: one
toolchain's generated pins, `ConLeche/Kernel/NatOpPins.lean` splices one
per committed dump). -/
def divModDeclPin (ps : NatOpPinSet) (c : Name) : Expr :=
  if c = natDivName then ps.divPin
  else if c = natGcdName then ps.gcdPin
  else if c = natLandName then ps.landPin
  else if c = natLorName then ps.lorPin
  else if c = natXorName then ps.xorPin
  else if c = natShiftLeftName then ps.shiftLeftPin
  else if c = natShiftRightName then ps.shiftRightPin
  else ps.modPin
end ConLeche
end
-- frontx_ind divModDeclPin on TExpr

-- ConLeche/Kernel/Checker.lean:129
section
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The certificate proof terms of a pin-certified WF-recursive op in
one pin variant, one per statement of `divModCertStmts`. -/
def divModCertProofs (ps : NatOpPinSet) (c : Name) : List Expr :=
  if c = natDivName then ps.divProofs
  else if c = natGcdName then ps.gcdProofs
  else if c = natLandName then ps.landProofs
  else if c = natLorName then ps.lorProofs
  else if c = natXorName then ps.xorProofs
  else if c = natShiftLeftName then ps.shiftLeftProofs
  else if c = natShiftRightName then ps.shiftRightProofs
  else ps.modProofs
end ConLeche
end
-- frontx_ind divModCertProofs on TExpr

-- ConLeche/Kernel/Checker.lean:143
section
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The type pins of a pin-certified WF-recursive op in one pin variant
(task #364): the constants its certificates use whose types differ
between supported toolchains, each with its type in this variant's
toolchain. -/
def divModTypePins (ps : NatOpPinSet) (c : Name) : List (Name × Expr) :=
  if c = natDivName then ps.divTypePins
  else if c = natGcdName then ps.gcdTypePins
  else if c = natLandName then ps.landTypePins
  else if c = natLorName then ps.lorTypePins
  else if c = natXorName then ps.xorTypePins
  else if c = natShiftLeftName then ps.shiftLeftTypePins
  else if c = natShiftRightName then ps.shiftRightTypePins
  else ps.modTypePins
end ConLeche
end
-- frontx_ind divModTypePins on TExpr

-- ConLeche/Kernel/Checker.lean:173
section
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The pinned characterization statements of a pin-certified
WF-recursive op, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOps` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored
value before checking (all statement components are application
spines, so `Expr.substConst0` applies). -/
def divModCertStmts (c : Name) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar 0 natTy
  let y : Expr := .fvar 1 natTy
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natMulName []) a) b
  if c = natGcdName then
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natShiftLeftName then
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natShiftRightName then
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natLandName then
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
    -- `x = 0 → x &&& y = 0`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c = natLorName then
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
    -- `x = 0 → x ||| y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natXorName then
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
    -- `x = 0 → x ^^^ y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]
end ConLeche
end
-- frontx_ind divModCertStmts on TExpr

-- ConLeche/Kernel/Checker.lean:246
section
namespace ConLeche
variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)
/-- The vendored proof applied to the statement's free variables
(`x`, `y`, then one `fvar` per hypothesis, carrying the hypothesis
*type* as its `fvar` annotation — the checker's implicit local
context). -/
def divModCertApplied (proofS : Expr) (hyps : List Expr) : Expr :=
  let base : Expr :=
    .app (.app proofS (.fvar 0 (.const natName [])))
      (.fvar 1 (.const natName []))
  match hyps with
  | [h1] => .app base (.fvar 2 h1)
  | [h1, h2] =>
    .app (.app base (.fvar 2 h1))
      (.fvar 3 h2)
  | _ => base
end ConLeche
end
-- frontx_ind divModCertApplied on TExpr

-- ConLeche/Kernel/Inductives/ClassRead.lean:79
section
namespace ConLeche
/-- The motive ordinal of the prefix variable `fvar p` (`nP ≤ p`), when
that binder is a motive. -/
def classOfMotiveVar (nP : Nat) (motPos : List Nat) (p : Nat) : Option Nat :=
  if nP ≤ p then motPos.findIdx? (· == p - nP) else none
end ConLeche
end

-- ConLeche/Kernel/Inductives/ClassRead.lean:83
section
namespace ConLeche
/-- Read one minor premise's type `dom`, opened at depth `d`. -/
def classReadMinor (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    Option ClassSlot := do
  let n := dom.piBinders.1.length
  let (fvs, concl) ← openPisAtFvars n dom d
  let .fvar p _ := concl.getAppFn | none
  let c ← classOfMotiveVar nP motPos p
  let .const C _ := (← concl.getAppArgs.getLast?).getAppFn | none
  -- every binder whose own conclusion is a motive is an ih; the others
  -- are the fields, before them
  let ihs := (List.range fvs.length).filterMap fun q =>
    match (fvs.getD q default).fvarTypeD.piResult.getAppFn with
    | .fvar p' _ =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match (fvs.getD q default).fvarTypeD.piResult.getAppArgs.getLast? with
        | some a =>
          match a.getAppFn with
          | .fvar f _ => if d ≤ f then some (f - d, t) else none
          | _ => none
        | none => none
      | none => none
    | _ => none
  pure (.minor c C ihs)
end ConLeche
end
-- frontx_ind classReadMinor on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:87
section
namespace ConLeche
/-- Close a telescope of `λ`s (`closeTelescope`'s twin). -/
def closeLams : List Expr → Nat → Expr → Expr
  | [], _, body => body
  | dom :: bs, i, body => .lam dom ((closeLams bs (i + 1) body).abstract1 i 0)
end ConLeche
end
-- frontx_ind closeLams on TExpr

-- ConLeche/Kernel/ExprOps.lean:905
section
namespace ConLeche.Expr
/-- The type annotation of a free-variable leaf (the expression itself
otherwise; used to read the domains off an opened telescope's
variables). -/
def fvarTypeD : Expr → Expr
  | .fvar _ ty => ty
  | e => e
end ConLeche.Expr
end

-- ConLeche/Kernel/Inductives/GenRec.lean:107
section
namespace ConLeche
/-- The binder of an opened variable (the motive types' binders: their
codomains are sorts, never zero). -/
def classBinder (x : Expr) : Expr := x.fvarTypeD
end ConLeche
end
-- frontx_ind classBinder on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:110
section
namespace ConLeche
/-- A generated binder of an opened variable. -/
def ClassGen.binder (_g : ClassGen) (x : Expr) : Expr := x.fvarTypeD
end ConLeche
end
-- frontx_ind ClassGen.binder on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:113
section
namespace ConLeche
/-- The prefix variable of slot `s`. -/
def ClassGen.slotVar (g : ClassGen) (s : Nat) : Expr := .fvar (g.nP + s) (.sort .zero)
end ConLeche
end
-- frontx_ind ClassGen.slotVar on TExpr

-- ConLeche/Kernel/Inductives/ClassRead.lean:70
section
namespace ConLeche
namespace ClassRead
/-- The prefix position (after the parameters) of class `c`'s motive. -/
def motiveSlot (r : ClassRead) (c : Nat) : Option Nat :=
  let ms := (List.range r.slots.length).filter fun s =>
    match r.slots[s]? with | some (.motive _) => true | _ => false
  ms[c]?
end ClassRead
end ConLeche
end

-- ConLeche/Kernel/Inductives/GenRec.lean:116
section
namespace ConLeche
/-- Class `c`'s motive variable. -/
def ClassGen.motVar (g : ClassGen) (c : Nat) : Expr :=
  g.slotVar ((ClassRead.motiveSlot ⟨g.slots, []⟩ c).getD 0)
end ConLeche
end
-- frontx_ind ClassGen.motVar on TExpr

-- ConLeche/Kernel/ExprOps.lean:858
section
namespace ConLeche.Expr
/-- Apply to a list of arguments. -/
def mkAppN (f : Expr) : List Expr → Expr
  | [] => f
  | a :: as => mkAppN (.app f a) as
end ConLeche.Expr
end

-- ConLeche/Kernel/Inductives/GenRec.lean:120
section
namespace ConLeche
/-- Class `c`'s index telescope opened at `d`, and its major domain. -/
def ClassGen.major (g : ClassGen) (c : Nat) (d : Nat) : Option (List Expr × Expr) := do
  let ci := g.cls.getD c default
  let ty ← instPisWith ci.ds (g.formerTys.getD c default)
  let (ifs, _) ← openPisAtFvars ci.nIdx ty d
  pure (ifs, Expr.mkAppN (.const ci.ind ci.lvls) (ci.ds ++ ifs))
end ConLeche
end
-- frontx_ind ClassGen.major on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:127
section
namespace ConLeche
/-- Class `c`'s motive type at depth `d`: `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ`. -/
def ClassGen.motiveTy (g : ClassGen) (c d : Nat) : Option Expr := do
  let (ifs, maj) ← g.major c d
  pure (closeTelescope (ifs.map classBinder) d (.forallE maj (.sort g.elim)))
end ConLeche
end
-- frontx_ind ClassGen.motiveTy on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:134
section
namespace ConLeche
/-- The inductive hypothesis of a recursive field whose WALKED type is `w`
(`∀ a⃗, J E⃗ e⃗`, landing at class `t`), opened at `d`: its telescope and its
index arguments. -/
def ClassGen.ihParts (g : ClassGen) (t : Nat) (tele : Nat) (w : Expr) (d : Nat) :
    Option (List Expr × List Expr) := do
  let (xs, leaf) ← openPisAtFvars tele w d
  pure (xs, leaf.getAppArgs.drop (g.cls.getD t default).nPc)
end ConLeche
end
-- frontx_ind ClassGen.ihParts on TExpr

-- ConLeche/Kernel/Env.lean:431
section
namespace ConLeche
namespace ConstantInfo
def name (c : ConstantInfo) : Name := c.toConstantVal.name
end ConstantInfo
end ConLeche
end

-- ConLeche/Kernel/Inductives/GenRec.lean:143
section
namespace ConLeche
/-- Constructor `x`'s minor premise type at depth `d`, of class `c`: its
declared fields, then per recursive field `f` (walked type `w`) the
inductive hypothesis `∀ a⃗, motive_t e⃗ (f a⃗)`, over the motive at the
declared result indices and the constructor applied. -/
def ClassGen.minorTy (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) : Option Expr := do
  let ci := g.cls.getD c default
  let (fvs, res) ← openPisAtFvars x.nF x.tyD d
  let ws ← targetPiDomsWith fvs x.tyN
  let recs := (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none
  let ihs ← (List.range recs.length).mapM fun l => do
    let (i, t, tele) := recs.getD l default
    let e := d + x.nF + l
    let (xs, idx) ← g.ihParts t tele (ws.getD i default) e
    pure (closeTelescope (xs.map g.binder) e
      (Expr.mkAppN (g.motVar t) (idx ++ [Expr.mkAppN (fvs.getD i default) xs])))
  let concl := Expr.mkAppN (g.motVar c)
    (res.getAppArgs.drop ci.nPc ++ [Expr.mkAppN (.const x.cv.name ci.lvls) (ci.ds ++ fvs)])
  pure (closeTelescope (fvs.map g.binder ++ ihs) d concl)
end ConLeche
end
-- frontx_ind ClassGen.minorTy on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:163
section
namespace ConLeche
/-- The prefix binders (parameters, then every slot in the stream's
order). -/
def ClassGen.prefixBinders (g : ClassGen) : Option (List Expr) := do
  let slotBs ← (List.range g.slots.length).mapM fun s => do
    let d := g.nP + s
    match g.slots.getD s default with
    | .motive _ =>
      let c := ((List.range s).filter fun s' =>
        match g.slots.getD s' default with | .motive _ => true | _ => false).length
      g.motiveTy c d
    | .minor c C _ =>
      let x ← (g.ctors.getD c []).find? (·.cv.name == C)
      g.minorTy c x d
  pure (g.params.map g.binder ++ slotBs)
end ConLeche
end
-- frontx_ind ClassGen.prefixBinders on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:177
section
namespace ConLeche
/-- **The generated recursor type** at class `c`. -/
def classGenRecTy (g : ClassGen) (c : Nat) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.major c rP
  let t : Expr := .fvar (rP + ifs.length) maj
  pure (closeTelescope (pre ++ ifs.map g.binder ++ [maj]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [t])))
end ConLeche
end
-- frontx_ind classGenRecTy on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:270
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- A walked field's leaf is headed by class `M`'s inductive. -/
def classLeafAt (M : TargetMajor) (leaf : Expr) : Bool :=
  match leaf.getAppFn with
  | .const I _ => I == M.ind
  | _ => false
end ConLeche
end
-- frontx_ind classLeafAt on TExpr

-- ConLeche/Kernel/Inductives/GenRec.lean:485
section
namespace ConLeche
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
/-- A class key moved to the block's canonical parameter variables
`params` (the pre-pass reads it over the stream recursor's own openers). -/
def classKeyCanon (params : List Expr) (k : ClassKey) : ClassKey :=
  { k with ds := k.ds.map (targetCanonParams params) }
end ConLeche
end
-- frontx_ind classKeyCanon on TExpr

-- ConLeche/Kernel/Install.lean:36
section
namespace ConLeche
/-- `n` variables below a term's own, which do not occur in it, dropped. -/
def Expr.dropVars : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.dropVars n (e.instantiate1 (.sort .zero))
end ConLeche
end
-- frontx_ind Expr.dropVars on TExpr

-- ConLeche/Cached/ExprOpsC.lean:30
section
namespace ConLeche.Expr
/-!
# The cached syntactic operations on `Expr`

The **executed**, memoized syntactic operations; the derived data they
cut off on is a field of the node.  Two structural facts, both
load-bearing for performance:

* the scope and definedness walks' memos are keyed on `Expr` itself
  (`O(1)` hashing off the cached field, pointer-first equality), so
  shared sub-DAGs are still visited once (`Std.HashMap Expr α`).  The
  SUBSTITUTION walks key theirs by address instead; see "The
  substitution walks" below;
* a cutoff (`bvarB ≤ d`, `fvarB ≤ d`, `!hasLP`) returns the node
  **itself**, so the result shares memory with the input and later
  pointer comparisons on it are `O(1)`.
-/
/-! ## Spines -/
/-- Prepend the spine arguments of `e` to `acc` (outermost last). -/
def getAppArgsAccC : Expr → List Expr → List Expr
  | .app f a .., acc => getAppArgsAccC f (a :: acc)
  | _, acc => acc
end ConLeche.Expr
end
-- frontx_ind Expr.getAppArgsAccC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:35
section
namespace ConLeche.Expr
/-- The arguments of an application spine, outermost last. -/
@[inline] def getAppArgsC (e : Expr) : List Expr := getAppArgsAccC e []
end ConLeche.Expr
end
-- frontx_ind Expr.getAppArgsC on TExpr

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
-- frontx_ind Expr.isCompound on TExpr

-- ConLeche/Kernel/Expr.lean:1339
section
namespace ConLeche
namespace Expr
/-! ## The shared `bvar` pool (task #177)

A `bvar` node is the smallest thing this checker builds and the one it
builds most: every substitution shifts loose indices, every abstraction
introduces one, the parser reads one per occurrence.  Each of those was
a fresh allocation — and, since the substitution walks stopped
recording their atoms in the per-walk memo, a fresh allocation that
nothing shared afterwards.

`bvarPool` is one **static** table of the first `bvarPoolSize` of them.
It is a closed top-level `def`, so the runtime builds it once at module
initialization and marks it persistent (`lean_mark_persistent` in the
generated C): handing out `bvarPool[i]` costs a bounds check and a
borrowed read, and its reference counting is free.  `mkBvar` is
representation-transparent (`mkBvar_eq`, `@[simp]`), so pattern
matching stays on `.bvar` and no statement anywhere changes.

**Where it is used.**  Every *runtime* `bvar` construction goes through
it, and the routing is one line: `ConLeche.Expr.mkBVar` is the
cached tier's only `bvar` builder, so the substitution and abstraction
walks and the frontend's parser are all covered at once.  The
remaining `.bvar` literals in the tree are either the pure *spec*
functions of `ConLeche/Kernel/ExprOps.lean` (which must keep the bare
constructor — they are what the pool is proved transparent against) or
closed constants such as the cores' `.bvar 0`, which the compiler
already lifts to a per-module `_init_…_closed__n` and marks persistent
itself.

The bound covers the corpus with room to spare: the deepest de Bruijn
index the battery produces is the 4 000-binder λ tower of
`good/perf/app-lam`. -/
/-- Size of the static `bvar` pool. -/
def bvarPoolSize : Nat := 4096
end Expr
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:1342
section
namespace ConLeche
namespace Expr
@[inherit_doc bvarPoolSize]
def bvarPool : Array Expr := (Array.range bvarPoolSize).map Expr.bvar
end Expr
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:1346
section
namespace ConLeche
namespace Expr
/-- The `bvar` smart constructor: the pooled node below `bvarPoolSize`,
a fresh one above it.  Same value either way (`mkBvar_eq`). -/
@[inline] def mkBvar (i : Nat) : Expr :=
  if h : i < bvarPool.size then bvarPool[i] else .bvar i
end Expr
end ConLeche
end

-- ConLeche/Cached/ExprNodes.lean:96
section
namespace ConLeche.Expr
@[inline] def mkApp (f a : Expr) : Expr := .app f a
end ConLeche.Expr
end

-- ConLeche/Cached/ExprNodes.lean:98
section
namespace ConLeche.Expr
@[inline] def mkLam (ty body : Expr) : Expr :=
  .lam ty body
end ConLeche.Expr
end

-- ConLeche/Cached/ExprNodes.lean:101
section
namespace ConLeche.Expr
@[inline] def mkForallE (ty body : Expr) :
    Expr := .forallE ty body
end ConLeche.Expr
end

-- ConLeche/Cached/ExprNodes.lean:104
section
namespace ConLeche.Expr
@[inline] def mkLetE (ty val body : Expr) : Expr :=
  .letE ty val body
end ConLeche.Expr
end

-- ConLeche/Cached/ExprNodes.lean:109
section
namespace ConLeche.Expr
@[inline] def mkProj (s : Name) (i : Nat) (e : Expr) : Expr := .proj s i e
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:263
section
namespace ConLeche.Expr
/-! ### `liftLooseBVarsC` (task #498)

`Expr.liftLooseBVars`: every loose bound variable at or above the
cursor bumped by a fixed amount.  The section's walk, with the `bvarB`
cutoff (a node bounded at or below the cursor has nothing to lift and
is returned unchanged); `liftLooseBVarsP_spec`
(`ConLeche/Verify/Cached/OpsC.lean`) reads the descent as
`Expr.liftLooseBVars`.  `instantiateLiftXP` lifts its values with it. -/
/-- The plain descent of `liftLooseBVarsC`: the reference
`liftLooseBVarsXP` carries its own proof against. -/
def liftLooseBVarsP (amount : Nat) (e : Expr) (c : Nat) : Expr :=
  if e.bvarB ≤ c then e else
  match e with
  | .bvar i .. => if i ≥ c then Expr.mkBvar (i + amount) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (liftLooseBVarsP amount f c) (liftLooseBVarsP amount a c)
  | .lam ty body .. =>
    mkLam (liftLooseBVarsP amount ty c) (liftLooseBVarsP amount body (c + 1))
  | .forallE ty body .. =>
    mkForallE (liftLooseBVarsP amount ty c) (liftLooseBVarsP amount body (c + 1))
  | .letE ty val body .. =>
    mkLetE (liftLooseBVarsP amount ty c) (liftLooseBVarsP amount val c)
      (liftLooseBVarsP amount body (c + 1))
  | .proj sn i sub .. => mkProj sn i (liftLooseBVarsP amount sub c)
end ConLeche.Expr
end
-- frontx_ind Expr.liftLooseBVarsP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:122
section
namespace ConLeche.Expr
/-- The term of a walk's result (the quotient lifts: the term is fixed
by its subtype). -/
@[inline] def resTerm {c : Expr} {M : Type} (s : Squash ({ r : Expr // r = c } × M)) : Expr :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:204
section
namespace ConLeche.Expr
/-- The hash-map table: the incumbent's `Std.HashMap`, keyed by the
packed address instead of the structural pair. -/
abbrev HTab (s : Expr → Nat → Expr) := Std.HashMap PKey (PEnt s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:208
section
namespace ConLeche.Expr
/-- The pointer-keyed memo: absent until the first shared compound
node. -/
abbrev MemoXP (s : Expr → Nat → Expr) := Option (HTab s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:212
section
namespace ConLeche.Expr
/-- A pointer-keyed walk's result: the term, fixed by its proof,
beside the memo. -/
abbrev ResXP (s : Expr → Nat → Expr) (e : Expr) (c : Nat) :=
  { r : Expr // r = s e c } × MemoXP s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:284
section
namespace ConLeche.Expr
/-- The child step of `liftLooseBVarsXP`: the cutoff, the compound
test, the exclusivity read. -/
@[inline] def enterLLP (amount : Nat) (e : @& Expr) (c : Nat)
    (memo : MemoXP (liftLooseBVarsP amount))
    (rec : (hcut : ¬ e.bvarB ≤ c) → Squash (ResXP (liftLooseBVarsP amount) e c)) :
    Squash (ResXP (liftLooseBVarsP amount) e c) :=
  if hcut : e.bvarB ≤ c then Squash.mk (⟨e, (liftLooseBVarsP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e c fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:294
section
namespace ConLeche.Expr
/-- The walk of `liftLooseBVarsC` (the node is past the cutoff). -/
def liftLooseBVarsXP (amount : Nat) (memo : MemoXP (liftLooseBVarsP amount)) (e : @& Expr)
    (c : Nat) (hcut : ¬ e.bvarB ≤ c) : Squash (ResXP (liftLooseBVarsP amount) e c) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i ≥ c then Expr.mkBvar (i + amount) else .bvar i,
      by rw [liftLooseBVarsP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [liftLooseBVarsP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [liftLooseBVarsP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [liftLooseBVarsP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [liftLooseBVarsP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLLP amount f c memo (fun h => liftLooseBVarsXP amount memo f c h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLLP amount a c memo (fun h => liftLooseBVarsXP amount memo a c h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [liftLooseBVarsP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterLLP amount ty c memo (fun h => liftLooseBVarsXP amount memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLLP amount body (c + 1) memo (fun h => liftLooseBVarsXP amount memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [liftLooseBVarsP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterLLP amount ty c memo (fun h => liftLooseBVarsXP amount memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLLP amount body (c + 1) memo (fun h => liftLooseBVarsXP amount memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [liftLooseBVarsP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLLP amount ty c memo (fun h => liftLooseBVarsXP amount memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLLP amount val c memo (fun h => liftLooseBVarsXP amount memo val c h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLLP amount body (c + 1) memo (fun h => liftLooseBVarsXP amount memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [liftLooseBVarsP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLLP amount sub c memo (fun h => liftLooseBVarsXP amount memo sub c h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [liftLooseBVarsP]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:327
section
namespace ConLeche.Expr
/-- The cached `Expr.liftLooseBVars amount c`: the cutoff, then the
walk. -/
def liftLooseBVarsC (amount : Nat) (e : @& Expr) (c : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ c then e else
  resTerm (liftLooseBVarsXP amount none e c hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.liftLooseBVarsC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:350
section
namespace ConLeche.Expr
/-! ### `instantiateLiftC`

The capture-avoiding substitution of several variables at once,
`Expr.instantiateLift`: what `structProjBodiesC` runs once per field
over that field's raw domain (task #495's algorithm).  The twin is the
section's walk, with the `bvarB` cutoff (a node bounded at or below the
cursor is returned unchanged).  `instantiateLiftC_spec`
(`ConLeche/Verify/Cached/OpsC.lean`) reads it as `Expr.instantiateLift`. -/
/-- The plain descent of `instantiateLiftC`: the reference
`instantiateLiftXP` carries its own proof against. -/
def instantiateLiftP (vs : Array Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. =>
    if i < d then e
    else if h : i - d < vs.size then liftLooseBVarsP d vs[i - d] 0
    else Expr.mkBvar (i - vs.size)
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiateLiftP vs f d) (instantiateLiftP vs a d)
  | .lam ty body .. =>
    mkLam (instantiateLiftP vs ty d) (instantiateLiftP vs body (d + 1))
  | .forallE ty body .. =>
    mkForallE (instantiateLiftP vs ty d) (instantiateLiftP vs body (d + 1))
  | .letE ty val body .. =>
    mkLetE (instantiateLiftP vs ty d) (instantiateLiftP vs val d)
      (instantiateLiftP vs body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiateLiftP vs sub d)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:374
section
namespace ConLeche.Expr
/-- The child step of `instantiateLiftXP`: the cutoff, the compound
test, the exclusivity read. -/
@[inline] def enterLiftP (vs : @& Array Expr) (e : @& Expr) (d : Nat)
    (memo : MemoXP (instantiateLiftP vs))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiateLiftP vs) e d)) :
    Squash (ResXP (instantiateLiftP vs) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateLiftP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:384
section
namespace ConLeche.Expr
/-- The walk of `instantiateLiftC`. -/
def instantiateLiftXP (vs : @& Array Expr) (memo : MemoXP (instantiateLiftP vs)) (e : @& Expr)
    (d : Nat) (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiateLiftP vs) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i < d then .bvar i
        else if h : i - d < vs.size then liftLooseBVarsC d vs[i - d] 0
        else Expr.mkBvar (i - vs.size),
      by rw [instantiateLiftP]; simp [hcut, liftLooseBVarsC_eqP]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiateLiftP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiateLiftP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiateLiftP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiateLiftP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLiftP vs f d memo (fun h => instantiateLiftXP vs memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterLiftP vs a d memo (fun h => instantiateLiftXP vs memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiateLiftP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterLiftP vs ty d memo (fun h => instantiateLiftXP vs memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP vs body (d + 1) memo (fun h => instantiateLiftXP vs memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [instantiateLiftP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterLiftP vs ty d memo (fun h => instantiateLiftXP vs memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP vs body (d + 1) memo (fun h => instantiateLiftXP vs memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [instantiateLiftP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterLiftP vs ty d memo (fun h => instantiateLiftXP vs memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterLiftP vs val d memo (fun h => instantiateLiftXP vs memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterLiftP vs body (d + 1) memo (fun h => instantiateLiftXP vs memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiateLiftP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterLiftP vs sub d memo (fun h => instantiateLiftXP vs memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiateLiftP]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:419
section
namespace ConLeche.Expr
/-- The cached `Expr.instantiateLift`: the cutoff (a closed binder
domain costs neither the values' `Array` nor a memo), then the walk. -/
def instantiateLiftC (e : @& Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiateLiftXP vs.toArray none e d hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.instantiateLiftC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:426
section
namespace ConLeche.Expr
/-- The plain descent of `instantiate1C`: the reference the walk is
verified against (`instantiate1P_spec`, `Verify/Cached/OpsC.lean`, is
the equation to `Expr.instantiate1`). -/
def instantiate1P (v : Expr) (e : Expr) (d : Nat) : Expr :=
  if e.bvarB ≤ d then e else
  match e with
  | .bvar i .. => if i = d then v else if i > d then Expr.mkBvar (i - 1) else e
  | .fvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (instantiate1P v f d) (instantiate1P v a d)
  | .lam ty body .. => mkLam (instantiate1P v ty d) (instantiate1P v body (d + 1))
  | .forallE ty body .. =>
    mkForallE (instantiate1P v ty d) (instantiate1P v body (d + 1))
  | .letE ty val body .. =>
    mkLetE (instantiate1P v ty d) (instantiate1P v val d) (instantiate1P v body (d + 1))
  | .proj sn i sub .. => mkProj sn i (instantiate1P v sub d)
end ConLeche.Expr
end
-- frontx_ind Expr.instantiate1P on TExpr

-- ConLeche/Cached/ExprOpsC.lean:445
section
namespace ConLeche.Expr
/-- The child step of `instantiate1XP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enter1P (v : @& Expr) (e : @& Expr) (d : Nat) (memo : MemoXP (instantiate1P v))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (instantiate1P v) e d)) :
    Squash (ResXP (instantiate1P v) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiate1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:455
section
namespace ConLeche.Expr
/-- The walk of `instantiate1C` (the node is past the cutoff: the
wrapper and `enter1P` test it). -/
def instantiate1XP (v : @& Expr) (memo : MemoXP (instantiate1P v)) (e : @& Expr) (d : Nat)
    (hcut : ¬ e.bvarB ≤ d) : Squash (ResXP (instantiate1P v) e d) :=
  match e with
  | .bvar i .. =>
    Squash.mk (⟨if i = d then v else if i > d then Expr.mkBvar (i - 1) else .bvar i,
      by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [instantiate1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enter1P v f d memo (fun h => instantiate1XP v memo f d h) |>.lift fun (⟨f', hf⟩, memo) =>
    enter1P v a d memo (fun h => instantiate1XP v memo a d h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [instantiate1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [instantiate1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [instantiate1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enter1P v ty d memo (fun h => instantiate1XP v memo ty d h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enter1P v val d memo (fun h => instantiate1XP v memo val d h) |>.lift fun (⟨v', hv⟩, memo) =>
    enter1P v body (d + 1) memo (fun h => instantiate1XP v memo body (d + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [instantiate1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enter1P v sub d memo (fun h => instantiate1XP v memo sub d h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [instantiate1P]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:487
section
namespace ConLeche.Expr
/-- The cached `Expr.instantiate1`: the cutoff, then the walk. -/
def instantiate1C (e : @& Expr) (v : Expr) (d : Nat := 0) : Expr :=
  if hcut : e.bvarB ≤ d then e else
  resTerm (instantiate1XP v none e d hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.instantiate1C on TExpr

-- ConLeche/Cached/ExprOpsC.lean:493
section
namespace ConLeche.Expr
/-- The plain descent of `instantiateListC`: the reference
`instantiateListXP` carries its own proof against. -/
def instantiateListP (vs : Array Expr) (e : Expr) (k : Nat) (d : Nat) : Expr :=
  if k = 0 then e
  else if e.bvarB ≤ d then e
  else
    match e with
    | .bvar i .. =>
      if i < d then e
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then w
          else instantiateListP vs w (i - d) d
        else e
      else Expr.mkBvar (i - k)
    | .fvar .. | .sort .. | .const .. | .lit .. => e
    | .app f a .. => mkApp (instantiateListP vs f k d) (instantiateListP vs a k d)
    | .lam ty body .. => mkLam (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1))
    | .forallE ty body .. =>
      mkForallE (instantiateListP vs ty k d) (instantiateListP vs body k (d + 1))
    | .letE ty val body .. =>
      mkLetE (instantiateListP vs ty k d) (instantiateListP vs val k d) (instantiateListP vs body k (d + 1))
    | .proj sn i sub .. => mkProj sn i (instantiateListP vs sub k d)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:527
section
namespace ConLeche.Expr
/-- The type of the re-entry of `leafListP` (see `reentListP`): the walk at a
shorter live prefix `j` under a fresh memo, as a bare term. -/
abbrev ReentListP (vs : Array Expr) (k d : Nat) : Type :=
  (j : Nat) → j < k → (w : Expr) → ¬ j = 0 → ¬ w.bvarB ≤ d →
    { r : Expr // r = instantiateListP vs w j d }
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:538
section
namespace ConLeche.Expr
/-- The non-compound node of the bulk instantiation, past the
cutoff: a bare term, the memo is not involved.  Everything but the
re-entry is a few comparisons and an array read, inlined into the
walk.  The re-entry — a replacement whose value has loose bound
variables below the lift — is `reent`: the walk under a FRESH memo (the
one place the live prefix `k` shrinks, and `k` is not part of the key),
whose memo is dropped (`reentListP`). -/
@[inline] def leafListP (vs : @& Array Expr) (k : Nat) (e : @& Expr) (d : Nat) (hk : ¬ k = 0)
    (reent : ReentListP vs k d)
    (hcut : ¬ e.bvarB ≤ d) (hc : (!isCompound e) = true) :
    { r : Expr // r = instantiateListP vs e k d } :=
  match e with
  | .bvar i .. =>
    if hi : i < d then ⟨.bvar i, by rw [instantiateListP.eq_def]; simp [hk, hcut, hi]⟩
    else if _h : i - d < k then
      if h : i - d < vs.size then
        let w := vs[i - d]
        if h0 : i - d = 0 || w.bvarB ≤ d then
          ⟨w, by rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0]⟩
        else
          have h0' : ¬ i - d = 0 ∧ ¬ w.bvarB ≤ d := by
            simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or] using h0
          match reent (i - d) _h w h0'.1 h0'.2 with
          | ⟨r, hr⟩ => ⟨r, by rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h, w, h0, hr]⟩
      else ⟨.bvar i, by rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h, h]⟩
    else ⟨Expr.mkBvar (i - k), by rw [instantiateListP.eq_def]; simp [hk, hcut, hi, _h]⟩
  | .fvar idx ty .. => ⟨.fvar idx ty, by rw [instantiateListP.eq_def]; simp [hk, hcut]⟩
  | .sort u .. => ⟨.sort u, by rw [instantiateListP.eq_def]; simp [hk, hcut]⟩
  | .const n us .. => ⟨.const n us, by rw [instantiateListP.eq_def]; simp [hk, hcut]⟩
  | .lit l .. => ⟨.lit l, by rw [instantiateListP.eq_def]; simp [hk, hcut]⟩
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => absurd hc (by simp [isCompound])
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:569
section
namespace ConLeche.Expr
/-- The child step of `instantiateListXP` (`k` is the parent's live
prefix): the cutoff; a non-compound child is `leafListP`, a bare term —
no `(term, memo)` pair is built for it, and the memo passes on
untouched; a compound child gets the exclusivity read.  `reent` and
`rec` are passed as partial applications of the walk's two functions,
so no closure is built: once this is inlined, each is a direct call. -/
@[inline] def enterListP (vs : @& Array Expr) (e : @& Expr) (k d : Nat) (hk : ¬ k = 0)
    (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (reent : ReentListP vs k d)
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResXP (fun e d => instantiateListP vs e k d) e d)) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨e, (instantiateListP_cut hcut).symm⟩, memo)
  else if hc : !isCompound e then Squash.mk (leafListP vs k e d hk reent hcut hc, memo)
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut
end ConLeche.Expr
end

-- mutual group (emitted together; members are mutually recursive)
-- ConLeche/Cached/ExprOpsC.lean:583
section
namespace ConLeche.Expr
mutual
-- ConLeche/Cached/ExprOpsC.lean:583
/-- The re-entry of `leafListP`: the walk at the shorter live prefix `j`
under a fresh memo, which is dropped. -/
def reentListP (vs : @& Array Expr) (k d : Nat) (j : Nat) (_hj : j < k) (w : @& Expr)
    (h0 : ¬ j = 0) (hw : ¬ w.bvarB ≤ d) : { r : Expr // r = instantiateListP vs w j d } :=
  ⟨resTerm (instantiateListXP vs j none w d h0 hw), resTerm_eq _⟩
termination_by (j, sizeOf w + 1)
decreasing_by
  all_goals (apply Prod.Lex.right; omega)

-- ConLeche/Cached/ExprOpsC.lean:593
/-- The walk of the bulk instantiation (the node is past the
cutoff: the wrapper and `enterListP` test it).  A non-compound node is
`leafListP`'s. -/
def instantiateListXP (vs : @& Array Expr) (k : Nat) (memo : MemoXP (fun e d => instantiateListP vs e k d))
    (e : @& Expr) (d : Nat) (hk : ¬ k = 0) (hcut : ¬ e.bvarB ≤ d) :
    Squash (ResXP (fun e d => instantiateListP vs e k d) e d) :=
  match e with
  | .app f a .. =>
    enterListP vs f k d hk memo (reentListP vs k d) (instantiateListXP vs k memo f d hk) |>.lift fun (⟨f', hf⟩, memo) =>
    enterListP vs a k d hk memo (reentListP vs k d) (instantiateListXP vs k memo a d hk) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterListP vs ty k d hk memo (reentListP vs k d) (instantiateListXP vs k memo ty d hk) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) hk memo (reentListP vs k (d + 1)) (instantiateListXP vs k memo body (d + 1) hk) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterListP vs ty k d hk memo (reentListP vs k d) (instantiateListXP vs k memo ty d hk) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs body k (d + 1) hk memo (reentListP vs k (d + 1)) (instantiateListXP vs k memo body (d + 1) hk) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterListP vs ty k d hk memo (reentListP vs k d) (instantiateListXP vs k memo ty d hk) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterListP vs val k d hk memo (reentListP vs k d) (instantiateListXP vs k memo val d hk) |>.lift fun (⟨v', hv⟩, memo) =>
    enterListP vs body k (d + 1) hk memo (reentListP vs k (d + 1)) (instantiateListXP vs k memo body (d + 1) hk) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterListP vs sub k d hk memo (reentListP vs k d) (instantiateListXP vs k memo sub d hk) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by dsimp only; rw [instantiateListP.eq_def]; simp [hk, hcut, hs, mkProj]⟩, memo)
  | .bvar i => Squash.mk (leafListP vs k (.bvar i) d hk (reentListP vs k d) hcut rfl, memo)
  | .fvar idx ty => Squash.mk (leafListP vs k (.fvar idx ty) d hk (reentListP vs k d) hcut rfl, memo)
  | .sort u => Squash.mk (leafListP vs k (.sort u) d hk (reentListP vs k d) hcut rfl, memo)
  | .const n us => Squash.mk (leafListP vs k (.const n us) d hk (reentListP vs k d) hcut rfl, memo)
  | .lit l => Squash.mk (leafListP vs k (.lit l) d hk (reentListP vs k d) hcut rfl, memo)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

end
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:631
section
namespace ConLeche.Expr
/-- The cached `Expr.instantiateList` (bulk): the cutoff, then the walk. -/
def instantiateListC (e : @& Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match vs with
  | [] => e
  | v :: vs' =>
    let a := (v :: vs').toArray
    if hcut : e.bvarB ≤ d then e
    else resTerm (instantiateListXP a a.size none e d (by simp [a]) hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.instantiateListC on TExpr

-- ConLeche/Kernel/Expr.lean:257
section
namespace ConLeche
/-- Fvar-range field of a packed word (bits 15…1). -/
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:488
section
namespace ConLeche
namespace Expr
/-- The stored fvar range, saturating at `satRange`. -/
@[inline] def fvarBRaw (e : Expr) : Nat := (fvarOfData e.data).toNat
end Expr
end ConLeche
end

-- ConLeche/Kernel/ExprOps.lean:183
section
namespace ConLeche.Expr
/-- Memoized `fvarRange` (the saturated branch's exact
recomputation). -/
def fvarRangeGo (memo : Std.HashMap Expr Nat) (e : Expr) :
    Nat × Std.HashMap Expr Nat :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Nat × Std.HashMap Expr Nat :=
      match e with
      | .fvar idx _ => (idx + 1, memo)
      | .bvar _ | .sort _ | .const _ _ | .lit _ => (0, memo)
      | .app f a =>
        let (rf, memo) := fvarRangeGo memo f
        let (ra, memo) := fvarRangeGo memo a
        (max rf ra, memo)
      | .lam ty body | .forallE ty body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rb, memo) := fvarRangeGo memo body
        (max rt rb, memo)
      | .letE ty val body =>
        let (rt, memo) := fvarRangeGo memo ty
        let (rv, memo) := fvarRangeGo memo val
        let (rb, memo) := fvarRangeGo memo body
        (max (max rt rv) rb, memo)
      | .proj _ _ sub => fvarRangeGo memo sub
    (r, memo.insert e r)
end ConLeche.Expr
end

-- ConLeche/Kernel/ExprOps.lean:209
section
namespace ConLeche.Expr
@[inherit_doc fvarRangeGo]
def fvarRangeMemo (e : Expr) : Nat := (fvarRangeGo {} e).1
end ConLeche.Expr
end

-- ConLeche/Kernel/ExprOps.lean:221
section
namespace ConLeche.Expr
/-- **The fvar range the checker reads**: the packed field, or — on the
saturated branch alone — the exact memoized recomputation.  Equal to
`Expr.fvarRange` unconditionally (`fvarB_eq`). -/
@[inline] def fvarB (e : Expr) : Nat :=
  let r := e.fvarBRaw
  if r == satRange then fvarRangeMemo e else r
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:789
section
namespace ConLeche.Expr
/-! ## Abstraction -/
/-- The plain descent of `abstract1C`: the reference of
`abstract1XP`. -/
def abstract1P (d : Nat) (e : Expr) (k : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. => if idx = d then Expr.mkBvar k else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstract1P d f k) (abstract1P d a k)
  | .lam ty body .. => mkLam (abstract1P d ty k) (abstract1P d body (k + 1))
  | .forallE ty body .. => mkForallE (abstract1P d ty k) (abstract1P d body (k + 1))
  | .letE ty val body .. =>
    mkLetE (abstract1P d ty k) (abstract1P d val k) (abstract1P d body (k + 1))
  | .proj sn i sub .. => mkProj sn i (abstract1P d sub k)
end ConLeche.Expr
end
-- frontx_ind Expr.abstract1P on TExpr

-- ConLeche/Cached/ExprOpsC.lean:806
section
namespace ConLeche.Expr
/-- (Task #316.) The child step of `abstract1XP`, pointer-keyed. -/
@[inline] def enterAbs1P (d : Nat) (e : @& Expr) (k : Nat) (memo : MemoXP (abstract1P d))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstract1P d) e k)) :
    Squash (ResXP (abstract1P d) e k) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstract1P_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e k fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:815
section
namespace ConLeche.Expr
/-- The walk of `abstract1C`. -/
def abstract1XP (d : Nat) (memo : MemoXP (abstract1P d)) (e : @& Expr) (k : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstract1P d) e k) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if idx = d then Expr.mkBvar k else .fvar idx ty,
      by rw [abstract1P]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstract1P]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbs1P d f k memo (fun h => abstract1XP d memo f k h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbs1P d a k memo (fun h => abstract1XP d memo a k h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstract1P]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [abstract1P]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [abstract1P]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbs1P d ty k memo (fun h => abstract1XP d memo ty k h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbs1P d val k memo (fun h => abstract1XP d memo val k h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbs1P d body (k + 1) memo (fun h => abstract1XP d memo body (k + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstract1P]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbs1P d sub k memo (fun h => abstract1XP d memo sub k h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstract1P]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:847
section
namespace ConLeche.Expr
/-- The cached `Expr.abstract1`: the cutoff, then the walk. -/
def abstract1C (e : @& Expr) (d : Nat) (k : Nat := 0) : Expr :=
  if hcut : e.fvarB ≤ d then e else
  resTerm (abstract1XP d none e k hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.abstract1C on TExpr

-- ConLeche/Cached/ExprOpsC.lean:853
section
namespace ConLeche.Expr
/-- The plain descent of `abstractRangeC`: the reference of
`abstractRangeXP`. -/
def abstractRangeP (d k : Nat) (e : Expr) (c : Nat) : Expr :=
  if e.fvarB ≤ d then e else
  match e with
  | .fvar idx .. =>
    if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app f a .. => mkApp (abstractRangeP d k f c) (abstractRangeP d k a c)
  | .lam ty body .. =>
    mkLam (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1))
  | .forallE ty body .. =>
    mkForallE (abstractRangeP d k ty c) (abstractRangeP d k body (c + 1))
  | .letE ty val body .. =>
    mkLetE (abstractRangeP d k ty c) (abstractRangeP d k val c)
      (abstractRangeP d k body (c + 1))
  | .proj sn i sub .. => mkProj sn i (abstractRangeP d k sub c)
end ConLeche.Expr
end
-- frontx_ind Expr.abstractRangeP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:874
section
namespace ConLeche.Expr
/-- (Task #316.) The child step of `abstractRangeXP`, pointer-keyed. -/
@[inline] def enterAbsRP (d k : Nat) (e : @& Expr) (c : Nat) (memo : MemoXP (abstractRangeP d k))
    (rec : (hcut : ¬ e.fvarB ≤ d) → Squash (ResXP (abstractRangeP d k) e c)) :
    Squash (ResXP (abstractRangeP d k) e c) :=
  if hcut : e.fvarB ≤ d then Squash.mk (⟨e, (abstractRangeP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e c fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:883
section
namespace ConLeche.Expr
/-- The walk of `abstractRangeC`. -/
def abstractRangeXP (d k : Nat) (memo : MemoXP (abstractRangeP d k)) (e : @& Expr) (c : Nat)
    (hcut : ¬ e.fvarB ≤ d) : Squash (ResXP (abstractRangeP d k) e c) :=
  match e with
  | .fvar idx ty .. =>
    Squash.mk (⟨if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx))
        else .fvar idx ty,
      by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [abstractRangeP]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterAbsRP d k f c memo (fun h => abstractRangeXP d k memo f c h) |>.lift fun (⟨f', hf⟩, memo) =>
    enterAbsRP d k a c memo (fun h => abstractRangeXP d k memo a c h) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨mkApp f' a', by rw [abstractRangeP]; simp [hcut, hf, ha, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [abstractRangeP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [abstractRangeP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterAbsRP d k ty c memo (fun h => abstractRangeXP d k memo ty c h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterAbsRP d k val c memo (fun h => abstractRangeXP d k memo val c h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterAbsRP d k body (c + 1) memo (fun h => abstractRangeXP d k memo body (c + 1) h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [abstractRangeP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterAbsRP d k sub c memo (fun h => abstractRangeXP d k memo sub c h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [abstractRangeP]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:917
section
namespace ConLeche.Expr
/-- The cached `Expr.abstractRange` (`k = 0` is the identity and skips
the traversal, as in the arena): the cutoff, then the walk. -/
def abstractRangeC (e : @& Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match k with
  | 0 => e
  | _ + 1 =>
    if hcut : e.fvarB ≤ d then e else
    resTerm (abstractRangeXP d k none e c hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.abstractRangeC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:244
section
namespace ConLeche.Expr
/-- The cursor-free instance (`instLevelParams`): the cursored memo at
cursor `0`. -/
abbrev MemoXP0 (s : Expr → Expr) := MemoXP (fun e _ => s e)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:246
section
namespace ConLeche.Expr
abbrev ResXP0 (s : Expr → Expr) (e : Expr) := { r : Expr // r = s e } × MemoXP0 s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1184
section
namespace ConLeche.Expr
/-! ## Constant substitution (task #497)

`Expr.substConstAll n r` replaces the level-monomorphic constant `n` by
the closed term `r` everywhere — the `Nat.div`/`Nat.mod` certificates'
references to the pinned operation (`checkDivModPinC`,
`ConLeche/Cached/ParsedC.lean`).  The specification is a tree walk:
on a certificate proof (a DAG of a few thousand nodes) it rebuilt every
occurrence of a shared subterm separately, and every guard and the
inference after it then walked the unshared copy.  The twin is the
section's walk without a cutoff (no flag says whether `n` occurs): the
compound children through the exclusivity read, the shared ones memoised
by address, so the result keeps the input's sharing.  It is its own
reference: an entry proves its node's image under `Expr.substConstAll`
itself (`substConstAllC_spec`, `ConLeche/Verify/Cached/OpsC.lean`). -/
/-- The child step of `substConstAllXP`: the compound test, the
exclusivity read. -/
@[inline] def enterSCA (n : @& Name) (r : @& Expr) (e : @& Expr)
    (memo : MemoXP0 (Expr.substConstAll n r))
    (rec : Unit → Squash (ResXP0 (Expr.substConstAll n r) e)) :
    Squash (ResXP0 (Expr.substConstAll n r) e) :=
  if !isCompound e then rec ()
  else withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1193
section
namespace ConLeche.Expr
/-- The walk of `substConstAllC`. -/
def substConstAllXP (n : @& Name) (r : @& Expr) (memo : MemoXP0 (Expr.substConstAll n r))
    (e : @& Expr) : Squash (ResXP0 (Expr.substConstAll n r) e) :=
  match e with
  | .const c us .. =>
    Squash.mk (⟨if c == n && us.isEmpty then r else .const c us, by
      simp only [Expr.substConstAll, beq_iff_eq, List.isEmpty_iff, Bool.and_eq_true]⟩, memo)
  | .app f a .. =>
    enterSCA n r f memo (fun _ => substConstAllXP n r memo f) |>.lift fun (⟨f', hf⟩, memo) =>
    enterSCA n r a memo (fun _ => substConstAllXP n r memo a) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨.app f' a', by rw [hf, ha]; rfl⟩, memo)
  | .lam ty body .. =>
    enterSCA n r ty memo (fun _ => substConstAllXP n r memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterSCA n r body memo (fun _ => substConstAllXP n r memo body) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨.lam ty' b', by rw [ht, hb]; rfl⟩, memo)
  | .forallE ty body .. =>
    enterSCA n r ty memo (fun _ => substConstAllXP n r memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterSCA n r body memo (fun _ => substConstAllXP n r memo body) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨.forallE ty' b', by rw [ht, hb]; rfl⟩, memo)
  | .letE ty val body .. =>
    enterSCA n r ty memo (fun _ => substConstAllXP n r memo ty) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterSCA n r val memo (fun _ => substConstAllXP n r memo val) |>.lift fun (⟨v', hv⟩, memo) =>
    enterSCA n r body memo (fun _ => substConstAllXP n r memo body) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨.letE ty' v' b', by rw [ht, hv, hb]; rfl⟩, memo)
  | .proj sn i sub .. =>
    enterSCA n r sub memo (fun _ => substConstAllXP n r memo sub) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨.proj sn i s', by rw [hs]; rfl⟩, memo)
  | .bvar i .. => Squash.mk (⟨.bvar i, rfl⟩, memo)
  | .fvar idx ty .. => Squash.mk (⟨.fvar idx ty, rfl⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, rfl⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, rfl⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1226
section
namespace ConLeche.Expr
/-- The cached `Expr.substConstAll`: sharing-preserving, the shared
nodes memoised by address. -/
def substConstAllC (n : Name) (r : Expr) (e : @& Expr) : Expr :=
  resTerm (substConstAllXP n r none e)
end ConLeche.Expr
end
-- frontx_ind Expr.substConstAllC on TExpr

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
-- frontx_ind Expr.isCompoundF on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1393
section
namespace ConLeche.Expr
/-! ## Scope queries -/
/-- The plain descent of `wscopedBC`: the reference the walk is
verified against (`wscopedBP_spec`, `ConLeche/Verify/Cached/OpsC.lean`,
is the equation to `Expr.wscopedB`).  The cursor is the node's second
argument, as it is for the substitution walks — it CHANGES at `fvar`,
where the annotation is entered at the variable's own index, so the
memo key must carry it. -/
def wscopedBP (e : Expr) (d : Nat) : Bool :=
  if e.fvarB == 0 then true else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => true
  | .fvar idx ty .. => idx < d && wscopedBP ty idx
  | .app f a .. => wscopedBP f d && wscopedBP a d
  | .lam ty body .. | .forallE ty body .. => wscopedBP ty d && wscopedBP body d
  | .letE ty val body .. => wscopedBP ty d && wscopedBP val d && wscopedBP body d
  | .proj _ _ sub .. => wscopedBP sub d
end ConLeche.Expr
end
-- frontx_ind Expr.wscopedBP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1374
section
namespace ConLeche.Expr
/-- The decision of a `Bool` walk's result (the quotient lifts: the
decision is fixed by its subtype). -/
@[inline] def resBool {c : Bool} {M : Type} (s : Squash ({ r : Bool // r = c } × M)) : Bool :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1324
section
namespace ConLeche.Expr
/-- The `Bool` table: the packed address-and-cursor key under the
mixing hash of `PKey`. -/
abbrev BTab (s : Expr → Nat → Bool) := Std.HashMap PKey (BEnt s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1328
section
namespace ConLeche.Expr
/-- The pointer-keyed `Bool` memo: absent until the first shared
compound node. -/
abbrev MemoB (s : Expr → Nat → Bool) := Option (BTab s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1332
section
namespace ConLeche.Expr
/-- A `Bool` walk's result: the decision, fixed by its proof, beside
the memo. -/
abbrev ResB (s : Expr → Nat → Bool) (e : Expr) (c : Nat) :=
  { r : Bool // r = s e c } × MemoB s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1409
section
namespace ConLeche.Expr
/-- The child step of `wscopedBXP`: the cutoff, the compound test, the
exclusivity read. -/
@[inline] def enterWSP (e : @& Expr) (d : Nat) (memo : MemoB wscopedBP)
    (rec : (hcut : (e.fvarB == 0) = false) → Squash (ResB wscopedBP e d)) :
    Squash (ResB wscopedBP e d) :=
  match hcut : e.fvarB == 0 with
  | true => Squash.mk (⟨true, (wscopedBP_cut hcut).symm⟩, memo)
  | false =>
    if !isCompoundF e then rec hcut
    else withExcl e fun excl =>
      if excl then rec hcut else memo.shared e d fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1421
section
namespace ConLeche.Expr
/-- The walk of `wscopedBC` (the node is past the cutoff: the wrapper
and `enterWSP` test it). -/
def wscopedBXP (memo : MemoB wscopedBP) (e : @& Expr) (d : Nat)
    (hcut : (e.fvarB == 0) = false) : Squash (ResB wscopedBP e d) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [wscopedBP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. =>
    if hidx : idx < d then
      enterWSP ty idx memo (fun h => wscopedBXP memo ty idx h)
        |>.lift fun (⟨rt, ht⟩, memo) =>
      Squash.mk (⟨rt, by rw [wscopedBP]; simp [hcut, hidx, ← ht]⟩, memo)
    else
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, hidx]⟩, memo)
  | .app f a .. =>
    enterWSP f d memo (fun h => wscopedBXP memo f d h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterWSP a d memo (fun h => wscopedBXP memo a d h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [wscopedBP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP body d memo (fun h => wscopedBXP memo body d h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP body d memo (fun h => wscopedBXP memo body d h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterWSP ty d memo (fun h => wscopedBXP memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterWSP val d memo (fun h => wscopedBXP memo val d h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterWSP body d memo (fun h => wscopedBXP memo body d h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [wscopedBP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [wscopedBP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterWSP sub d memo (fun h => wscopedBXP memo sub d h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [wscopedBP]; simp [hcut, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1482
section
namespace ConLeche.Expr
/-- The cached `Expr.wscopedB d` (one memoized DAG walk): the cutoff,
then the walk. -/
def wscopedBC (d : Nat) (e : Expr) : Bool :=
  match hcut : e.fvarB == 0 with
  | true => true
  | false => resBool (wscopedBXP none e d hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.wscopedBC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1490
section
namespace ConLeche.Expr
/-- `Expr.hasLooseBVarB` with the node first: the reference of
`hasLooseBVarBXP` (task #497).  The specification carries the cutoff
itself (`bvarB ≤ i`). -/
def hasLooseBVarBP (e : Expr) (i : Nat) : Bool := Expr.hasLooseBVarB i e
end ConLeche.Expr
end
-- frontx_ind Expr.hasLooseBVarBP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1498
section
namespace ConLeche.Expr
/-- The child step of `hasLooseBVarBXP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enterLBP (e : @& Expr) (i : Nat) (memo : MemoB hasLooseBVarBP)
    (rec : (hcut : ¬ e.bvarB ≤ i) → Squash (ResB hasLooseBVarBP e i)) :
    Squash (ResB hasLooseBVarBP e i) :=
  if hcut : e.bvarB ≤ i then Squash.mk (⟨false, (hasLooseBVarBP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e i fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1507
section
namespace ConLeche.Expr
/-- The walk of `hasLooseBVarBC` (the node is past the cutoff). -/
def hasLooseBVarBXP (memo : MemoB hasLooseBVarBP) (e : @& Expr) (i : Nat)
    (hcut : ¬ e.bvarB ≤ i) : Squash (ResB hasLooseBVarBP e i) :=
  match e with
  | .bvar j .. =>
    Squash.mk (⟨i == j, by rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut]⟩, memo)
  | .fvar .. => Squash.mk (⟨false, by rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨false, by rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨false, by rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨false, by rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLBP f i memo (fun h => hasLooseBVarBXP memo f i h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      Squash.mk (⟨true, by
        rw [hasLooseBVarBP] at hf; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut, ← hf]⟩, memo)
    | false, hf =>
      enterLBP a i memo (fun h => hasLooseBVarBXP memo a i h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by
        rw [hasLooseBVarBP] at hf ha; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]
        simp [hcut, ← hf, ← ha]⟩, memo)
  | .lam ty body .. =>
    enterLBP ty i memo (fun h => hasLooseBVarBXP memo ty i h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by
        rw [hasLooseBVarBP] at ht; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLBP body (i + 1) memo (fun h => hasLooseBVarBXP memo body (i + 1) h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by
        rw [hasLooseBVarBP] at ht hb; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]
        simp [hcut, ← ht, ← hb]⟩, memo)
  | .forallE ty body .. =>
    enterLBP ty i memo (fun h => hasLooseBVarBXP memo ty i h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by
        rw [hasLooseBVarBP] at ht; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLBP body (i + 1) memo (fun h => hasLooseBVarBXP memo body (i + 1) h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by
        rw [hasLooseBVarBP] at ht hb; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]
        simp [hcut, ← ht, ← hb]⟩, memo)
  | .letE ty val body .. =>
    enterLBP ty i memo (fun h => hasLooseBVarBXP memo ty i h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by
        rw [hasLooseBVarBP] at ht; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLBP val i memo (fun h => hasLooseBVarBXP memo val i h) |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        Squash.mk (⟨true, by
          rw [hasLooseBVarBP] at ht hv; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]
          simp [hcut, ← ht, ← hv]⟩, memo)
      | false, hv =>
        enterLBP body (i + 1) memo (fun h => hasLooseBVarBXP memo body (i + 1) h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by
          rw [hasLooseBVarBP] at ht hv hb; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]
          simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
  | .proj _ _ sub .. =>
    enterLBP sub i memo (fun h => hasLooseBVarBXP memo sub i h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by
      rw [hasLooseBVarBP] at hs; rw [hasLooseBVarBP, Expr.hasLooseBVarB.eq_def]; simp [hcut, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1578
section
namespace ConLeche.Expr
/-- The cached `Expr.hasLooseBVarB i` (one memoized DAG walk): the
cutoff, then the walk (`hasLooseBVarBC_spec`,
`ConLeche/Verify/Cached/OpsC.lean`). -/
def hasLooseBVarBC (i : Nat) (e : Expr) : Bool :=
  if hcut : e.bvarB ≤ i then false else resBool (hasLooseBVarBXP none e i hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.hasLooseBVarBC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1593
section
namespace ConLeche.Expr
/-! ### `hasLooseBVarInC` (task #498, L7)

Does a loose bound variable of index `d ..< d + w` occur?  The
projection guard's question of a raw constructor telescope: does a
field's type, or the rest of the telescope, mention a field before it
(`projGuardFastC`).  Read only, no node is built.  The cutoff is the
packed bound (`bvarB ≤ d`: no loose variable at or above `d`); under a
binder the window moves up by one. -/
/-- The plain descent of `hasLooseBVarInC`, the cutoff included: the
reference `hasLooseBVarInXP` carries its own proof against
(`hasLooseBVarInP_false`, `ConLeche/Verify/Cached/DiscC4.lean`). -/
def hasLooseBVarInP (w : Nat) (e : Expr) (d : Nat) : Bool :=
  if e.bvarB ≤ d then false else
  match e with
  | .bvar j => decide (d ≤ j) && decide (j < d + w)
  | .fvar .. | .sort _ | .const .. | .lit _ => false
  | .app f a => hasLooseBVarInP w f d || hasLooseBVarInP w a d
  | .lam ty b => hasLooseBVarInP w ty d || hasLooseBVarInP w b (d + 1)
  | .forallE ty b => hasLooseBVarInP w ty d || hasLooseBVarInP w b (d + 1)
  | .letE t v b =>
    hasLooseBVarInP w t d || hasLooseBVarInP w v d || hasLooseBVarInP w b (d + 1)
  | .proj _ _ s => hasLooseBVarInP w s d
end ConLeche.Expr
end
-- frontx_ind Expr.hasLooseBVarInP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1611
section
namespace ConLeche.Expr
/-- The child step of `hasLooseBVarInXP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enterLIP (w : Nat) (e : @& Expr) (d : Nat) (memo : MemoB (hasLooseBVarInP w))
    (rec : (hcut : ¬ e.bvarB ≤ d) → Squash (ResB (hasLooseBVarInP w) e d)) :
    Squash (ResB (hasLooseBVarInP w) e d) :=
  if hcut : e.bvarB ≤ d then Squash.mk (⟨false, (hasLooseBVarInP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e d fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1620
section
namespace ConLeche.Expr
/-- The walk of `hasLooseBVarInC` (the node is past the cutoff). -/
def hasLooseBVarInXP (w : Nat) (memo : MemoB (hasLooseBVarInP w)) (e : @& Expr) (d : Nat)
    (hcut : ¬ e.bvarB ≤ d) : Squash (ResB (hasLooseBVarInP w) e d) :=
  match e with
  | .bvar j .. =>
    Squash.mk (⟨decide (d ≤ j) && decide (j < d + w), by
      rw [hasLooseBVarInP.eq_def]; simp [hcut]⟩, memo)
  | .fvar .. => Squash.mk (⟨false, by rw [hasLooseBVarInP.eq_def]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨false, by rw [hasLooseBVarInP.eq_def]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨false, by rw [hasLooseBVarInP.eq_def]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨false, by rw [hasLooseBVarInP.eq_def]; simp [hcut]⟩, memo)
  | .app f a .. =>
    enterLIP w f d memo (fun h => hasLooseBVarInXP w memo f d h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      Squash.mk (⟨true, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← hf]⟩, memo)
    | false, hf =>
      enterLIP w a d memo (fun h => hasLooseBVarInXP w memo a d h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← hf, ← ha]⟩, memo)
  | .lam ty body .. =>
    enterLIP w ty d memo (fun h => hasLooseBVarInXP w memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLIP w body (d + 1) memo (fun h => hasLooseBVarInXP w memo body (d + 1) h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht, ← hb]⟩, memo)
  | .forallE ty body .. =>
    enterLIP w ty d memo (fun h => hasLooseBVarInXP w memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLIP w body (d + 1) memo (fun h => hasLooseBVarInXP w memo body (d + 1) h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht, ← hb]⟩, memo)
  | .letE ty val body .. =>
    enterLIP w ty d memo (fun h => hasLooseBVarInXP w memo ty d h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      Squash.mk (⟨true, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht]⟩, memo)
    | false, ht =>
      enterLIP w val d memo (fun h => hasLooseBVarInXP w memo val d h) |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        Squash.mk (⟨true, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht, ← hv]⟩, memo)
      | false, hv =>
        enterLIP w body (d + 1) memo (fun h => hasLooseBVarInXP w memo body (d + 1) h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
  | .proj _ _ sub .. =>
    enterLIP w sub d memo (fun h => hasLooseBVarInXP w memo sub d h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [hasLooseBVarInP.eq_def]; simp [hcut, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1676
section
namespace ConLeche.Expr
/-- The cached window query (one memoized DAG walk): the cutoff, then
the walk; an empty window asks nothing. -/
def hasLooseBVarInC (d w : Nat) (e : @& Expr) : Bool :=
  if w = 0 then false else
  if hcut : e.bvarB ≤ d then false else resBool (hasLooseBVarInXP w none e d hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.hasLooseBVarInC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1695
section
namespace ConLeche.Expr
/-! ## Occurrence queries of the inductive check (task #498)

`Expr.nestOcc` (a member constant or a hole variable `lo ..< hi`; a
free variable's annotation is not looked into, a `.proj` node's
structure is no occurrence) and `Expr.mentionsAnyConst` (one of the
constants `names`, annotations included, a `.proj` node naming its
structure).  Neither has a cached field to cut off on — no field
records which constants a node mentions — so, like `constsResolveFC`,
each walk decides its leaves directly and probes only a compound node
`withExclusive` reports shared.  Both stop at the first occurrence.
`nestOccP_spec` and `mentionsAnyConstP_spec`
(`ConLeche/Verify/Cached/IndWalksC.lean`) read the descents as the
specifications. -/
/-- The plain descent of `nestOccC`. -/
def nestOccP (names : List Name) (lo hi : Nat) (e : Expr) : Bool :=
  match e with
  | .bvar .. | .sort .. | .lit .. => false
  | .fvar i .. => decide (lo ≤ i ∧ i < hi)
  | .const n .. => names.contains n
  | .app f a .. => nestOccP names lo hi f || nestOccP names lo hi a
  | .lam ty body .. | .forallE ty body .. => nestOccP names lo hi ty || nestOccP names lo hi body
  | .letE ty val body .. =>
    nestOccP names lo hi ty || nestOccP names lo hi val || nestOccP names lo hi body
  | .proj _ _ sub .. => nestOccP names lo hi sub
end ConLeche.Expr
end
-- frontx_ind Expr.nestOccP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1364
section
namespace ConLeche.Expr
/-- The cursor-free instance: the cursored `Bool` memo at cursor
`0`. -/
abbrev MemoB0 (s : Expr → Bool) := MemoB (fun e _ => s e)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1366
section
namespace ConLeche.Expr
abbrev ResB0 (s : Expr → Bool) (e : Expr) := { r : Bool // r = s e } × MemoB0 s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1708
section
namespace ConLeche.Expr
/-- The child step of `nestOccXP`: the compound test, then the
exclusivity read (there is no cutoff; `fvar` is a leaf). -/
@[inline] def enterNO (names : @& List Name) (lo hi : Nat) (e : @& Expr)
    (memo : MemoB0 (nestOccP names lo hi))
    (rec : Unit → Squash (ResB0 (nestOccP names lo hi) e)) :
    Squash (ResB0 (nestOccP names lo hi) e) :=
  if !isCompound e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1717
section
namespace ConLeche.Expr
/-- The walk of `nestOccC`. -/
def nestOccXP (names : @& List Name) (lo hi : Nat) (memo : MemoB0 (nestOccP names lo hi))
    (e : @& Expr) : Squash (ResB0 (nestOccP names lo hi) e) :=
  match e with
  | .bvar .. | .sort .. | .lit .. => Squash.mk (⟨false, by rw [nestOccP]⟩, memo)
  | .fvar i .. => Squash.mk (⟨decide (lo ≤ i ∧ i < hi), by rw [nestOccP]⟩, memo)
  | .const n .. => Squash.mk (⟨names.contains n, by rw [nestOccP]⟩, memo)
  | .app f a .. =>
    enterNO names lo hi f memo (fun _ => nestOccXP names lo hi memo f) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf => Squash.mk (⟨true, by rw [nestOccP, ← hf, Bool.true_or]⟩, memo)
    | false, hf =>
      enterNO names lo hi a memo (fun _ => nestOccXP names lo hi memo a) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [nestOccP, ← hf, ← ha, Bool.false_or]⟩, memo)
  | .lam ty body .. | .forallE ty body .. =>
    enterNO names lo hi ty memo (fun _ => nestOccXP names lo hi memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht => Squash.mk (⟨true, by rw [nestOccP, ← ht, Bool.true_or]⟩, memo)
    | false, ht =>
      enterNO names lo hi body memo (fun _ => nestOccXP names lo hi memo body) |>.lift
        fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [nestOccP, ← ht, ← hb, Bool.false_or]⟩, memo)
  | .letE ty val body .. =>
    enterNO names lo hi ty memo (fun _ => nestOccXP names lo hi memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht => Squash.mk (⟨true, by rw [nestOccP, ← ht]; simp⟩, memo)
    | false, ht =>
      enterNO names lo hi val memo (fun _ => nestOccXP names lo hi memo val) |>.lift
        fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv => Squash.mk (⟨true, by rw [nestOccP, ← ht, ← hv]; simp⟩, memo)
      | false, hv =>
        enterNO names lo hi body memo (fun _ => nestOccXP names lo hi memo body) |>.lift
          fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [nestOccP, ← ht, ← hv, ← hb]; simp⟩, memo)
  | .proj _ _ sub .. =>
    enterNO names lo hi sub memo (fun _ => nestOccXP names lo hi memo sub) |>.lift
      fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [nestOccP, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1757
section
namespace ConLeche.Expr
/-- The cached `Expr.nestOcc names lo hi` (one memoized DAG walk). -/
def nestOccC (names : List Name) (lo hi : Nat) (e : @& Expr) : Bool :=
  resBool (nestOccXP names lo hi none e)
end ConLeche.Expr
end
-- frontx_ind Expr.nestOccC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1761
section
namespace ConLeche.Expr
/-- The plain descent of `mentionsAnyConstC`. -/
def mentionsAnyConstP (names : List Name) (e : Expr) : Bool :=
  match e with
  | .bvar .. | .sort .. | .lit .. => false
  | .const n .. => names.contains n
  | .fvar _ ty .. => mentionsAnyConstP names ty
  | .app f a .. => mentionsAnyConstP names f || mentionsAnyConstP names a
  | .lam ty body .. | .forallE ty body .. =>
    mentionsAnyConstP names ty || mentionsAnyConstP names body
  | .letE ty val body .. =>
    mentionsAnyConstP names ty || mentionsAnyConstP names val || mentionsAnyConstP names body
  | .proj s _ sub .. => names.contains s || mentionsAnyConstP names sub
end ConLeche.Expr
end
-- frontx_ind Expr.mentionsAnyConstP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1775
section
namespace ConLeche.Expr
/-- The child step of `mentionsAnyConstXP`: the compound test (`fvar`
included: its annotation is descended), then the exclusivity read. -/
@[inline] def enterMAC (names : @& List Name) (e : @& Expr)
    (memo : MemoB0 (mentionsAnyConstP names))
    (rec : Unit → Squash (ResB0 (mentionsAnyConstP names) e)) :
    Squash (ResB0 (mentionsAnyConstP names) e) :=
  if !isCompoundF e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1784
section
namespace ConLeche.Expr
/-- The walk of `mentionsAnyConstC`. -/
def mentionsAnyConstXP (names : @& List Name) (memo : MemoB0 (mentionsAnyConstP names))
    (e : @& Expr) : Squash (ResB0 (mentionsAnyConstP names) e) :=
  match e with
  | .bvar .. | .sort .. | .lit .. => Squash.mk (⟨false, by rw [mentionsAnyConstP]⟩, memo)
  | .const n .. => Squash.mk (⟨names.contains n, by rw [mentionsAnyConstP]⟩, memo)
  | .fvar _ ty .. =>
    enterMAC names ty memo (fun _ => mentionsAnyConstXP names memo ty) |>.lift
      fun (⟨rt, ht⟩, memo) =>
    Squash.mk (⟨rt, by rw [mentionsAnyConstP, ← ht]⟩, memo)
  | .app f a .. =>
    enterMAC names f memo (fun _ => mentionsAnyConstXP names memo f) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf => Squash.mk (⟨true, by rw [mentionsAnyConstP, ← hf, Bool.true_or]⟩, memo)
    | false, hf =>
      enterMAC names a memo (fun _ => mentionsAnyConstXP names memo a) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [mentionsAnyConstP, ← hf, ← ha, Bool.false_or]⟩, memo)
  | .lam ty body .. | .forallE ty body .. =>
    enterMAC names ty memo (fun _ => mentionsAnyConstXP names memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht => Squash.mk (⟨true, by rw [mentionsAnyConstP, ← ht, Bool.true_or]⟩, memo)
    | false, ht =>
      enterMAC names body memo (fun _ => mentionsAnyConstXP names memo body) |>.lift
        fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [mentionsAnyConstP, ← ht, ← hb, Bool.false_or]⟩, memo)
  | .letE ty val body .. =>
    enterMAC names ty memo (fun _ => mentionsAnyConstXP names memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht => Squash.mk (⟨true, by rw [mentionsAnyConstP, ← ht]; simp⟩, memo)
    | false, ht =>
      enterMAC names val memo (fun _ => mentionsAnyConstXP names memo val) |>.lift
        fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv => Squash.mk (⟨true, by rw [mentionsAnyConstP, ← ht, ← hv]; simp⟩, memo)
      | false, hv =>
        enterMAC names body memo (fun _ => mentionsAnyConstXP names memo body) |>.lift
          fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [mentionsAnyConstP, ← ht, ← hv, ← hb]; simp⟩, memo)
  | .proj s _ sub .. =>
    if hs : names.contains s = true then
      Squash.mk (⟨true, by rw [mentionsAnyConstP, hs, Bool.true_or]⟩, memo)
    else
      enterMAC names sub memo (fun _ => mentionsAnyConstXP names memo sub) |>.lift
        fun (⟨rs, hsub⟩, memo) =>
      Squash.mk (⟨rs, by rw [mentionsAnyConstP, ← hsub, Bool.eq_false_iff.mpr hs, Bool.false_or]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1830
section
namespace ConLeche.Expr
/-- The cached `Expr.mentionsAnyConst names` (one memoized DAG walk). -/
def mentionsAnyConstC (names : List Name) (e : @& Expr) : Bool :=
  resBool (mentionsAnyConstXP names none e)
end ConLeche.Expr
end
-- frontx_ind Expr.mentionsAnyConstC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1901
section
namespace ConLeche.Expr
/-- The plain descent of `depthC`. -/
def depthP (e : Expr) : Nat :=
  match e with
  | .app f a .. => max (depthP f) (depthP a) + 1
  | .lam ty body .. | .forallE ty body .. => max (depthP ty) (depthP body) + 1
  | .letE ty val body .. => max (max (depthP ty) (depthP val)) (depthP body) + 1
  | .proj _ _ sub .. => depthP sub + 1
  | .bvar .. | .fvar .. | .sort .. | .const .. | .lit .. => 1
end ConLeche.Expr
end
-- frontx_ind Expr.depthP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1892
section
namespace ConLeche.Expr
/-- The value of a `Nat` walk's result. -/
@[inline] def resNat {c : Nat} {M : Type} (s : Squash ({ r : Nat // r = c } × M)) : Nat :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1857
section
namespace ConLeche.Expr
/-- The `Nat` table under the packed address key. -/
abbrev NTab (s : Expr → Nat) := Std.HashMap PKey (NEnt s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1861
section
namespace ConLeche.Expr
/-- The pointer-keyed `Nat` memo: absent until the first shared
compound node. -/
abbrev MemoN (s : Expr → Nat) := Option (NTab s)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1865
section
namespace ConLeche.Expr
/-- A `Nat` walk's result: the value, fixed by its proof, beside the
memo. -/
abbrev ResN (s : Expr → Nat) (e : Expr) := { r : Nat // r = s e } × MemoN s
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1911
section
namespace ConLeche.Expr
/-- The child step of `depthXP`: the compound test, then the
exclusivity read. -/
@[inline] def enterDepth (e : @& Expr) (memo : MemoN depthP)
    (rec : Unit → Squash (ResN depthP e)) : Squash (ResN depthP e) :=
  if !isCompound e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1918
section
namespace ConLeche.Expr
/-- The walk of `depthC`. -/
def depthXP (memo : MemoN depthP) (e : @& Expr) : Squash (ResN depthP e) :=
  match e with
  | .bvar .. | .fvar .. | .sort .. | .const .. | .lit .. =>
    Squash.mk (⟨1, by rw [depthP]⟩, memo)
  | .app f a .. =>
    enterDepth f memo (fun _ => depthXP memo f) |>.lift fun (⟨df, hf⟩, memo) =>
    enterDepth a memo (fun _ => depthXP memo a) |>.lift fun (⟨da, ha⟩, memo) =>
    Squash.mk (⟨max df da + 1, by rw [depthP, hf, ha]⟩, memo)
  | .lam ty body .. | .forallE ty body .. =>
    enterDepth ty memo (fun _ => depthXP memo ty) |>.lift fun (⟨dt, ht⟩, memo) =>
    enterDepth body memo (fun _ => depthXP memo body) |>.lift fun (⟨db, hb⟩, memo) =>
    Squash.mk (⟨max dt db + 1, by rw [depthP, ht, hb]⟩, memo)
  | .letE ty val body .. =>
    enterDepth ty memo (fun _ => depthXP memo ty) |>.lift fun (⟨dt, ht⟩, memo) =>
    enterDepth val memo (fun _ => depthXP memo val) |>.lift fun (⟨dv, hv⟩, memo) =>
    enterDepth body memo (fun _ => depthXP memo body) |>.lift fun (⟨db, hb⟩, memo) =>
    Squash.mk (⟨max (max dt dv) db + 1, by rw [depthP, ht, hv, hb]⟩, memo)
  | .proj _ _ sub .. =>
    enterDepth sub memo (fun _ => depthXP memo sub) |>.lift fun (⟨ds, hs⟩, memo) =>
    Squash.mk (⟨ds + 1, by rw [depthP, hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:1940
section
namespace ConLeche.Expr
/-- The cached `Expr.depth` (one memoized DAG walk). -/
def depthC (e : @& Expr) : Nat :=
  resNat (depthXP none e)
end ConLeche.Expr
end
-- frontx_ind Expr.depthC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:1976
section
namespace ConLeche.Expr
/-- Core of `fvarLeavesC` (memoized set accumulation).

**The one walk of the tree whose memo is not the `withExclusive`
idiom, and why** (task #319, which put that idiom in front of every
other traversal memo — the substitution walks, `Expr.beqGoX`, and the
`Bool`-valued walks above).  This memo is a visited SET, and its
entries are `Unit`: what an entry means is *"this node's leaves are
already in `acc`"* — a statement about the ACCUMULATOR, which changes
at every step, and about the walk's own descent path, not about the
node.  It is the verification's `SeenInv`
(`ConLeche/Verify/Cached/GuardsC.lean`): every key of `seen` either
has all its leaves in `acc` already or is *gray* (being processed).
An entry carrying no value cannot prove itself, so this memo needs a
table invariant — which is exactly what the idiom removes.

The self-proving alternative is an entry carrying the node's own leaf
list, `{ r : List (Nat × Expr) // r = Expr.fvarLeaves e }`, appended
at the parent.  That closes as a proof — it is the `Bool` walks'
shape with a list in place of the decision — but it is the wrong
ALGORITHM: `Expr.fvarLeaves` concatenates at every compound node
(`ConLeche/Kernel/ExprOps.lean`), so a node's own list is the leaf
list of its TREE unfolding, and materialising one per entry is
precisely the blow-up the `seen` set exists to avoid (an `app e e`
ladder gives the root a list of `2^k` elements on `k` nodes; the
affine frontier's 3.9 · 10⁸-node unfolding of a 3 106-node DAG is the
real instance).  Weakening the subtype to a membership
characterization — all the one consumer, `leafMem`, needs — closes
just as easily and does not shrink the lists: siblings still
concatenate, and deduplicating at each node reintroduces a per-node
set, i.e. the table the entry was meant to replace.  So the
accumulator is the algorithm here, and the accumulator is what cannot
be carried in a type.  DESIGN.md, task #319, records this as the one
permitted exception and the open question behind it. -/
def fvarLeavesGoC (acc : List (Nat × Expr))
    (seen : Std.HashMap Expr Unit) (e : Expr) :
    List (Nat × Expr) × Std.HashMap Expr Unit :=
  if e.fvarB == 0 then (acc, seen) else
  match seen[e]? with
  | some _ => (acc, seen)
  | none =>
    let seen := seen.insert e ()
    match e with
    | .bvar .. | .sort .. | .const .. | .lit .. => (acc, seen)
    | .fvar idx ty .. => fvarLeavesGoC ((idx, ty) :: acc) seen ty
    | .app f a .. =>
      let (acc, seen) := fvarLeavesGoC acc seen f
      fvarLeavesGoC acc seen a
    | .lam ty body .. | .forallE ty body .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      fvarLeavesGoC acc seen body
    | .letE ty val body .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      let (acc, seen) := fvarLeavesGoC acc seen val
      fvarLeavesGoC acc seen body
    | .proj _ _ sub .. => fvarLeavesGoC acc seen sub
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2000
section
namespace ConLeche.Expr
/-- The reachable `fvar` leaves (hereditarily through annotations). -/
def fvarLeavesC (e : Expr) : List (Nat × Expr) :=
  (fvarLeavesGoC [] {} e).1
end ConLeche.Expr
end
-- frontx_ind Expr.fvarLeavesC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2005
section
namespace ConLeche.Expr
/-- Is `(idx, ty)` in the base leaf list?  Compares the annotation
with `Expr.beq` (pointer-first). -/
def leafMem : List (Nat × Expr) → Nat → Expr → Bool
  | [], _, _ => false
  | (i, t) :: rest, idx, ty =>
    (i == idx && t == ty) || leafMem rest idx ty
end ConLeche.Expr
end
-- frontx_ind Expr.leafMem on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2015
section
namespace ConLeche.Expr
/-- The plain descent of the leaf-subset walk: the reference the walk
is verified against (`leavesSubP_spec`,
`ConLeche/Verify/Cached/GuardsC.lean`, is the equation to the
`Expr`-level leaf-subset boolean).  `leafMem` is the membership
test (task #86). -/
def leavesSubP (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  if e.fvarB == 0 then true else
  match e with
  | .bvar .. | .sort .. | .const .. | .lit .. => true
  | .fvar idx ty .. => leafMem bl idx ty && leavesSubP bl ty
  | .app f a .. => leavesSubP bl f && leavesSubP bl a
  | .lam ty body .. | .forallE ty body .. => leavesSubP bl ty && leavesSubP bl body
  | .letE ty val body .. =>
    leavesSubP bl ty && leavesSubP bl val && leavesSubP bl body
  | .proj _ _ sub .. => leavesSubP bl sub
end ConLeche.Expr
end
-- frontx_ind Expr.leavesSubP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2032
section
namespace ConLeche.Expr
/-- The child step of `leavesSubXP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enterLSub (bl : @& List (Nat × Expr)) (e : @& Expr)
    (memo : MemoB0 (leavesSubP bl))
    (rec : (hcut : (e.fvarB == 0) = false) → Squash (ResB0 (leavesSubP bl) e)) :
    Squash (ResB0 (leavesSubP bl) e) :=
  match hcut : e.fvarB == 0 with
  | true => Squash.mk (⟨true, (leavesSubP_cut hcut).symm⟩, memo)
  | false =>
    if !isCompoundF e then rec hcut
    else withExcl e fun excl =>
      if excl then rec hcut else memo.shared e fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2045
section
namespace ConLeche.Expr
/-- The leaf-subset walk (the node is past the cutoff: `leavesSubC`
and `enterLSub` test it). -/
def leavesSubXP (bl : @& List (Nat × Expr)) (memo : MemoB0 (leavesSubP bl))
    (e : @& Expr) (hcut : (e.fvarB == 0) = false) : Squash (ResB0 (leavesSubP bl) e) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .sort .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .const .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [leavesSubP]; simp [hcut]⟩, memo)
  | .fvar idx ty .. =>
    if hlm : leafMem bl idx ty = true then
      enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h)
        |>.lift fun (⟨rt, ht⟩, memo) =>
      Squash.mk (⟨rt, by rw [leavesSubP]; simp [hcut, hlm, ← ht]⟩, memo)
    else
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, hlm]⟩, memo)
  | .app f a .. =>
    enterLSub bl f memo (fun h => leavesSubXP bl memo f h) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterLSub bl a memo (fun h => leavesSubXP bl memo a h) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [leavesSubP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterLSub bl ty memo (fun h => leavesSubXP bl memo ty h) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLSub bl val memo (fun h => leavesSubXP bl memo val h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterLSub bl body memo (fun h => leavesSubXP bl memo body h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [leavesSubP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [leavesSubP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterLSub bl sub memo (fun h => leavesSubXP bl memo sub h) |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [leavesSubP]; simp [hcut, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2105
section
namespace ConLeche.Expr
/-- The cached leaf-subset test: the cutoff, then the walk. -/
def leavesSubC (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  match hcut : e.fvarB == 0 with
  | true => true
  | false => resBool (leavesSubXP bl none e hcut)
end ConLeche.Expr
end
-- frontx_ind Expr.leavesSubC on TExpr

-- ConLeche/Kernel/ExprOps.lean:60
section
namespace ConLeche.Expr
/-- Does the expression contain any free variable (`fvar`)?  Input
declarations must be `fvar`-free; the checker introduces `fvar`s only
internally when opening binders. -/
def hasFvar : Expr → Bool
  | .bvar _ | .sort _ | .const .. | .lit _ => false
  | .fvar .. => true
  | .app f a => hasFvar f || hasFvar a
  | .lam ty body | .forallE ty body => hasFvar ty || hasFvar body
  | .letE ty val body => hasFvar ty || hasFvar val || hasFvar body
  | .proj _ _ e => hasFvar e
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2113
section
namespace ConLeche.Expr
/-- The fabrication leaf guard: every `fvar` leaf of `fab` is one of
`base` (short-circuits on `fvar`-free fabrications, `O(1)` off the
cached range). -/
def leafGuard (fab base : Expr) : Bool :=
  !fab.hasFvar || leavesSubC (fvarLeavesC base) fab
end ConLeche.Expr
end
-- frontx_ind Expr.leafGuard on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2119
section
namespace ConLeche.Expr
/-! ## Telescope operations -/
/-- The `instantiate1C` chain of `Expr.instSpine`. -/
def instSpineChainC : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpineChainC as (t - 1) (instantiate1C e a t)
end ConLeche.Expr
end
-- frontx_ind Expr.instSpineChainC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2125
section
namespace ConLeche.Expr
/-- The cached `Expr.instSpine` (bulk when the spine spans the
telescope context, the chain otherwise). -/
def instSpineC (args : List Expr) (t : Nat) (e : Expr) : Expr :=
  if args.length = t + 1 then instantiateListC e args.reverse 0
  else instSpineChainC args t e
end ConLeche.Expr
end
-- frontx_ind Expr.instSpineC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2135
section
namespace ConLeche.Expr
/-- Core of `piResidual` (bulk form, task #50).

Not structural: the `bvar` arm re-enters on the same argument list with
the accumulator flushed.  Measure `(as.length, acc.length)` — the
`forallE` arm consumes an argument, the `bvar` arm keeps the arguments
and empties a nonempty accumulator. -/
def piResidualAcc : List Expr → Expr → List Expr → Option Expr
  | acc, e, [] => some (instantiateListC e acc 0)
  | acc, e, a :: as =>
    match e with
    | .forallE _ b .. => piResidualAcc (a :: acc) b as
    | .bvar .. =>
      match acc with
      | [] => none
      | _ :: _ => piResidualAcc [] (instantiateListC e acc 0) (a :: as)
    | _ => none
termination_by acc _ as => (as.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)
end ConLeche.Expr
end
-- frontx_ind Expr.piResidualAcc on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2152
section
namespace ConLeche.Expr
@[inherit_doc piResidualAcc]
def piResidual (e : Expr) (args : List Expr) : Option Expr :=
  piResidualAcc [] e args
end ConLeche.Expr
end
-- frontx_ind Expr.piResidual on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2198
section
namespace ConLeche.Expr
/-- The cached `closeTelescope` (task #498): the telescope opened at
the free variables `i ..< i + bs.length` closed back into a
`∀`-telescope over `body`, each domain and the body abstracted ONCE,
over the free variables of the binders outside it (`abstractRangeC`),
instead of re-abstracting the whole remaining telescope at every binder
(`closeTelescopeC_eq`, `ConLeche/Verify/Cached/IndWalksC.lean`).  `k`
counts the binders already passed. -/
def closeTelescopeGoC (i : Nat) : Nat → List Expr → Expr → Expr
  | k, [], body => abstractRangeC body i k
  | k, dom :: bs, body => mkForallE (abstractRangeC dom i k) (closeTelescopeGoC i (k + 1) bs body)
end ConLeche.Expr
end
-- frontx_ind Expr.closeTelescopeGoC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2203
section
namespace ConLeche.Expr
@[inherit_doc closeTelescopeGoC]
def closeTelescopeC (bs : List Expr) (i : Nat) (body : Expr) : Expr :=
  closeTelescopeGoC i 0 bs body
end ConLeche.Expr
end
-- frontx_ind Expr.closeTelescopeC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2207
section
namespace ConLeche.Expr
/-- The cached `closeLams`: `closeTelescopeC` with `λ` binders. -/
def closeLamsGoC (i : Nat) : Nat → List Expr → Expr → Expr
  | k, [], body => abstractRangeC body i k
  | k, dom :: bs, body => mkLam (abstractRangeC dom i k) (closeLamsGoC i (k + 1) bs body)
end ConLeche.Expr
end
-- frontx_ind Expr.closeLamsGoC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2212
section
namespace ConLeche.Expr
@[inherit_doc closeLamsGoC]
def closeLamsC (bs : List Expr) (i : Nat) (body : Expr) : Expr :=
  closeLamsGoC i 0 bs body
end ConLeche.Expr
end
-- frontx_ind Expr.closeLamsC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2217
section
namespace ConLeche.Expr
/-- The cached `Expr.abstractPrefix k c`: the free variables `0 … k-1`
closed at cursor `c` in one `abstractRangeC` pass. -/
def abstractPrefixC (k c : Nat) (e : Expr) : Expr :=
  abstractRangeC e 0 k c
end ConLeche.Expr
end
-- frontx_ind Expr.abstractPrefixC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2222
section
namespace ConLeche.Expr
/-- The cached `instPisWith`: the leading binders instantiated one by
one by `instantiate1C` (`instPisWithC_eq`). -/
def instPisWithC : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body => instPisWithC as (instantiate1C body a)
  | _ :: _, _ => none
end ConLeche.Expr
end
-- frontx_ind Expr.instPisWithC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2229
section
namespace ConLeche.Expr
/-- The cached `targetPiDomsWith`: each binder opened by `instantiate1C`
(`targetPiDomsWithC_eq`). -/
def targetPiDomsWithC : List Expr → Expr → Option (List Expr)
  | [], _ => some []
  | x :: xs, .forallE d b => (d :: ·) <$> targetPiDomsWithC xs (instantiate1C b x)
  | _ :: _, _ => none
end ConLeche.Expr
end
-- frontx_ind Expr.targetPiDomsWithC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2236
section
namespace ConLeche.Expr
/-- The cached `Expr.piDomsMentionAny`: some binder domain of the
syntactic `∀`-telescope mentions one of `names`. -/
def piDomsMentionAnyC (names : List Name) : Expr → Bool
  | .forallE ty b .. => mentionsAnyConstC names ty || piDomsMentionAnyC names b
  | _ => false
end ConLeche.Expr
end
-- frontx_ind Expr.piDomsMentionAnyC on TExpr

-- ConLeche/Kernel/Expr.lean:260
section
namespace ConLeche
/-- Has-level-param field of a packed word (bit 0). -/
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1
end ConLeche
end

-- ConLeche/Kernel/Expr.lean:482
section
namespace ConLeche
namespace Expr
/-- Has-level-param: is level instantiation ever non-trivial here?
One bit, so this read is *exact*. -/
@[inline] def hasLP (e : Expr) : Bool := lpOfData e.data
end Expr
end ConLeche
end

-- ConLeche/Cached/ExprOpsC.lean:2291
section
namespace ConLeche.Expr
/-! ## Level-parameter definedness (the parsed-index driver's guard) -/
/-- The plain descent of `allLevelParamsDefinedC`: the reference the
walk is verified against (`allLevelParamsDefinedP_spec`,
`ConLeche/Verify/Cached/GuardsC.lean`, is the equation to
`Expr.allLevelParamsDefined`).  The cutoff: a node without a level
parameter is `true` without traversal. -/
def allLevelParamsDefinedP (params : List Name) (e : Expr) : Bool :=
  if e.hasLP then
    match e with
    | .bvar .. | .lit .. => true
    | .sort u .. => Level.allParamsDefined params u
    | .const _ us .. => us.all (Level.allParamsDefined params)
    | .fvar _ ty .. => allLevelParamsDefinedP params ty
    | .app f a .. =>
      allLevelParamsDefinedP params f && allLevelParamsDefinedP params a
    | .lam ty body .. | .forallE ty body .. =>
      allLevelParamsDefinedP params ty && allLevelParamsDefinedP params body
    | .letE ty val body .. =>
      allLevelParamsDefinedP params ty && allLevelParamsDefinedP params val
        && allLevelParamsDefinedP params body
    | .proj _ _ sub .. => allLevelParamsDefinedP params sub
  else true
end ConLeche.Expr
end
-- frontx_ind Expr.allLevelParamsDefinedP on TExpr

-- ConLeche/Cached/ExprOpsC.lean:2314
section
namespace ConLeche.Expr
/-- The child step of `allLevelParamsDefinedXP`: the cutoff, the
compound test, the exclusivity read. -/
@[inline] def enterLPD (params : @& List Name) (e : @& Expr)
    (memo : MemoB0 (allLevelParamsDefinedP params))
    (rec : (hcut : e.hasLP = true) →
      Squash (ResB0 (allLevelParamsDefinedP params) e)) :
    Squash (ResB0 (allLevelParamsDefinedP params) e) :=
  if hcut : e.hasLP = true then
    (if !isCompoundF e then rec hcut
     else withExcl e fun excl =>
       if excl then rec hcut else memo.shared e fun _ => rec hcut)
  else Squash.mk (⟨true, (allLevelParamsDefinedP_cut hcut).symm⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2327
section
namespace ConLeche.Expr
/-- The walk of `allLevelParamsDefinedC` (the node is past the
cutoff: the wrapper and `enterLPD` test it). -/
def allLevelParamsDefinedXP (params : @& List Name)
    (memo : MemoB0 (allLevelParamsDefinedP params)) (e : @& Expr)
    (hcut : e.hasLP = true) :
    Squash (ResB0 (allLevelParamsDefinedP params) e) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .sort u .. =>
    Squash.mk (⟨Level.allParamsDefined params u,
      by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .const _ us .. =>
    Squash.mk (⟨us.all (Level.allParamsDefined params),
      by rw [allLevelParamsDefinedP]; simp [hcut]⟩, memo)
  | .fvar _ ty .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    Squash.mk (⟨rt, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .app f a .. =>
    enterLPD params f memo (fun h => allLevelParamsDefinedXP params memo f h)
      |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterLPD params a memo (fun h => allLevelParamsDefinedXP params memo a h)
        |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [allLevelParamsDefinedP]; simp [hcut, ← hf, ← ha]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← hf]⟩, memo)
  | .lam ty body .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb,
        by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .forallE ty body .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
        |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb,
        by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hb]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .letE ty val body .. =>
    enterLPD params ty memo (fun h => allLevelParamsDefinedXP params memo ty h)
      |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterLPD params val memo (fun h => allLevelParamsDefinedXP params memo val h)
        |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterLPD params body memo (fun h => allLevelParamsDefinedXP params memo body h)
          |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hv, ← hb]⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht, ← hv]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [allLevelParamsDefinedP]; simp [hcut, ← ht]⟩, memo)
  | .proj _ _ sub .. =>
    enterLPD params sub memo (fun h => allLevelParamsDefinedXP params memo sub h)
      |>.lift fun (⟨rs, hs⟩, memo) =>
    Squash.mk (⟨rs, by rw [allLevelParamsDefinedP]; simp [hcut, ← hs]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:2399
section
namespace ConLeche.Expr
/-- The cached `Expr.allLevelParamsDefined params` (one memoized DAG
walk): the cutoff, then the walk. -/
def allLevelParamsDefinedC (params : List Name) (e : Expr) : Bool :=
  if hcut : e.hasLP = true then resBool (allLevelParamsDefinedXP params none e hcut)
  else true
end ConLeche.Expr
end
-- frontx_ind Expr.allLevelParamsDefinedC on TExpr

-- ConLeche/Cached/StateC.lean:73
section
namespace ConLeche.Cached
open ConLeche
/-- The cached `sameConstHeads`. -/
def sameConstHeadsC (a b : Expr) : Bool :=
  match a, b with
  | .app f₁ _ .., .app f₂ _ .. =>
    match Expr.getAppFn f₁, Expr.getAppFn f₂ with
    | .const n₁ _ .., .const n₂ _ .. => n₁ == n₂
    | _, _ => false
  | _, _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.sameConstHeadsC on TExpr

-- ConLeche/Cached/StateC.lean:82
section
namespace ConLeche.Cached
open ConLeche
/-- `rawNatLit?` on an `Expr`. -/
def rawNatLitC? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) .. => some n
  | .const c [] .. => if c == natZeroName then some 0 else none
  | _ => none
end ConLeche.Cached
end
-- frontx_ind Cached.rawNatLitC? on TExpr

-- ConLeche/Cached/StateC.lean:190
section
namespace ConLeche.Cached
open ConLeche
/-- The operation's constant. -/
def NatBinOp.name : NatBinOp → Name
  | .add => natAddName | .sub => natSubName | .mul => natMulName | .pow => natPowName
  | .beq => natBeqName | .ble => natBleName | .div => natDivName | .mod => natModName
  | .gcd => natGcdName | .land => natLandName | .lor => natLorName | .xor => natXorName
  | .shiftLeft => natShiftLeftName | .shiftRight => natShiftRightName
end ConLeche.Cached
end
-- frontx_ind Cached.NatBinOp.name on TExpr

-- ConLeche/Cached/StateC.lean:197
section
namespace ConLeche.Cached
open ConLeche
/-- `c = n`, the cached hashes first: a different hash decides at once, without a call. -/
@[inline] def nameIsC (c n : Name) : Bool := c.hashData == n.hashData && decide (c = n)
end ConLeche.Cached
end
-- frontx_ind Cached.nameIsC on TExpr

-- ConLeche/Cached/StateC.lean:200
section
namespace ConLeche.Cached
open ConLeche
/-- The operation named `c`, if any. -/
def NatBinOp.ofName? (c : Name) : Option NatBinOp :=
  if nameIsC c natAddName then some .add
  else if nameIsC c natSubName then some .sub
  else if nameIsC c natMulName then some .mul
  else if nameIsC c natPowName then some .pow
  else if nameIsC c natBeqName then some .beq
  else if nameIsC c natBleName then some .ble
  else if nameIsC c natDivName then some .div
  else if nameIsC c natModName then some .mod
  else if nameIsC c natGcdName then some .gcd
  else if nameIsC c natLandName then some .land
  else if nameIsC c natLorName then some .lor
  else if nameIsC c natXorName then some .xor
  else if nameIsC c natShiftLeftName then some .shiftLeft
  else if nameIsC c natShiftRightName then some .shiftRight
  else none
end ConLeche.Cached
end
-- frontx_ind Cached.NatBinOp.ofName? on TExpr

-- ConLeche/Cached/StateC.lean:218
section
namespace ConLeche.Cached
open ConLeche
/-- The operation's result on literals, at any size (`natOpResult` of its name). -/
def NatBinOp.result : NatBinOp → Nat → Nat → Expr
  | .add, a, b => .lit (.natVal (a + b))
  | .sub, a, b => .lit (.natVal (a - b))
  | .mul, a, b => .lit (.natVal (a * b))
  | .pow, a, b => .lit (.natVal (a ^ b))
  | .beq, a, b => .const (if a = b then boolTrueName else boolFalseName) []
  | .ble, a, b => .const (if a <= b then boolTrueName else boolFalseName) []
  | .div, a, b => .lit (.natVal (a / b))
  | .mod, a, b => .lit (.natVal (a % b))
  | .gcd, a, b => .lit (.natVal (Nat.gcd a b))
  | .land, a, b => .lit (.natVal (Nat.land a b))
  | .lor, a, b => .lit (.natVal (Nat.lor a b))
  | .xor, a, b => .lit (.natVal (Nat.xor a b))
  | .shiftLeft, a, b => .lit (.natVal (Nat.shiftLeft a b))
  | .shiftRight, a, b => .lit (.natVal (Nat.shiftRight a b))
end ConLeche.Cached
end
-- frontx_ind Cached.NatBinOp.result on TExpr

-- ConLeche/Cached/StateC.lean:159
section
namespace ConLeche.Cached
open ConLeche
/-- The official kernel's size of a numeral in bytes
(`lean_nat_size_in_bytes`): one machine word for a scalar, the limbs
for a GMP number — 8 bytes per started 64 bits, and at least 8. -/
def natSizeBytes (n : Nat) : Nat := 8 * (n.log2 / 64 + 1)
end ConLeche.Cached
end

-- ConLeche/Cached/StateC.lean:257
section
namespace ConLeche.Cached
open ConLeche
/-- **The refusal after computing** (official `reduce_bin_nat_op`'s
`check_size`): the result `x` of `op`, a `Nat.add`, `Nat.sub` or
`Nat.mul`, is a numeral above the maximum size. -/
def natResultRefused (maxNatSize : Nat) (op : NatBinOp) (x : Expr) : Bool :=
  match op with
  | .add | .sub | .mul =>
    match x with
    | .lit (.natVal n) => natSizeBytes n > maxNatSize
    | _ => false
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.natResultRefused on TExpr

-- ConLeche/Kernel/Error.lean:42
section
namespace ConLeche
abbrev CheckM := Except CheckError
end ConLeche
end

-- ConLeche/Cached/StateC.lean:316
section
namespace ConLeche.Cached
open ConLeche
/-- The cached checker's monad: the per-declaration memo state over
`CheckM`. -/
abbrev CheckCM := StateT CState CheckM
end ConLeche.Cached
end

-- ConLeche/Cached/StateC.lean:336
section
namespace ConLeche.Cached
open ConLeche
/-! ## Syntactic operations (the `*M` wrappers) -/
/-- `Expr.instantiate1`; the identity — the same node, by reference —
when the target has no loose bvar at or above the cursor. -/
@[inline] def inst1M (e v : Expr) (d : Nat := 0) : CheckCM Expr :=
  pure (Expr.instantiate1C e v d)
end ConLeche.Cached
end
-- frontx_ind Cached.inst1M on TExpr

-- ConLeche/Cached/StateC.lean:312
section
namespace ConLeche.Cached
open ConLeche
/-- Entry bound for the persistent bulk-instantiation memo. -/
def instCCapC : Nat := 32000000
end ConLeche.Cached
end

-- ConLeche/Cached/StateC.lean:341
section
namespace ConLeche.Cached
open ConLeche
/-- Bulk instantiation with the persistent result memo (task #145),
keyed by the whole argument tuple. -/
def instListM (e : Expr) (vs : List Expr) (d : Nat := 0) : CheckCM Expr :=
  modifyGet fun s =>
    if e.bvarB ≤ d then (e, s)
    else
      match s.instC[(e, vs, d)]? with
      | some r => (r, s)
      | none =>
        let mp := s.instC
        let s := { s with instC := {} }
        let mp := if mp.size < instCCapC then mp else {}
        let r := Expr.instantiateListC e vs d
        (r, { s with instC := mp.insert (e, vs, d) r })
end ConLeche.Cached
end
-- frontx_ind Cached.instListM on TExpr

-- ConLeche/Cached/CoreC.lean:140
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- The length of an application spine, without building its argument
list. -/
def iotaNumArgs : Expr → Nat → Nat
  | .app f _, n => iotaNumArgs f (n + 1)
  | _, n => n
end ConLeche.Cached
end
-- frontx_ind Cached.iotaNumArgs on TExpr

-- ConLeche/Cached/CoreC.lean:182
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- A spine head that is its own head normal form and not a lambda: the
heads `whnfCoreEasy` answers with themselves, but a lambda. -/
def isStuckHeadC : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .const .. | .lit _ => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.isStuckHeadC on TExpr

-- ConLeche/Cached/CoreC.lean:242
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **`whnfCore`'s easy cases** (official `whnf_core`, "handle easy
cases"): the kinds that are their own head normal form
(`whnfCoreStepI`'s `.done e` arm).  The loop returns them before the
memo, at every step: no lookup, no insert.  A free variable is never a
let-variable here (lets are ζ-reduced by instantiation), so it is easy,
as official's non-let `FVar`. -/
@[inline] def whnfCoreEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.whnfCoreEasy on TExpr

-- ConLeche/Cached/CoreC.lean:254
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **A `whnfCore` memo key**: a term of an arm official `whnf_core`
stores (`src/kernel/type_checker.cpp`, `whnf_core`: the `Proj`, `Let`
and `App` cases, the insert after the `switch`) — a projection, a
let-expression, or an application whose head is not its own head normal
form.  An application with a stuck head (`isStuckHeadC`) is official's
`f == f0` arm, the ι step or the stuck answer, which `return`s before
the insert: it is never stored, so the loop does not look it up.  `h`
is the term's spine head (`Expr.getAppFn`), computed once per step. -/
@[inline] def whnfCoreKeyC (h : Expr) : Expr → Bool
  | .app _ _ => !isStuckHeadC h
  | .proj .. | .letE .. => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.whnfCoreKeyC on TExpr

-- ConLeche/Cached/CoreC.lean:264
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- A key whose step ended the chain with `v` is stored, but for an
application answered by itself: its head normalized to itself (a stuck
projection), official's `f == f0` arm again.  A stuck
projection is stored (official's `Proj` case stores `r = e`).  `key` is
`whnfCoreKeyC` of `e`. -/
@[inline] def whnfCoreStoresDone (key : Bool) (e v : Expr) : Bool :=
  match e with
  | .app .. => key && !(v == e)
  | _ => key
end ConLeche.Cached
end
-- frontx_ind Cached.whnfCoreStoresDone on TExpr

-- ConLeche/Cached/CoreC.lean:275
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **A step the two modes take alike**: a let-expression, or an
application whose head is a lambda or stuck; neither normalizes a
projection or a head that could contain one.  A chain of such steps
answers the same in the cheap mode as in the full one
(`whnfCoreStepW_cheap`), so the full mode's loop also stores its keys
in the cheap mode's memo.  `h` is the term's spine head. -/
@[inline] def whnfCoreCheapSafeC (h : Expr) : Expr → Bool
  | .app _ _ =>
    match h with
    | .lam .. => true
    | h => isStuckHeadC h
  | .letE .. => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.whnfCoreCheapSafeC on TExpr

-- ConLeche/Cached/CoreC.lean:297
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- The pending keys past a step on `e`: `e` joins them where it is
stored (`b`). -/
@[inline] def pushKey (b : Bool) (e : Expr) (pend : List Expr) : List Expr :=
  if b then e :: pend else pend
end ConLeche.Cached
end
-- frontx_ind Cached.pushKey on TExpr

-- ConLeche/Cached/CoreC.lean:303
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- The cheap mode's pending keys past a step on `e`: kept, and joined by
`e` where it is stored (`b`), past a step the two modes take alike
(`safe`, `whnfCoreCheapSafeC`); dropped past any other. -/
@[inline] def pushCheapKey (safe b : Bool) (e : Expr) (pendC : List Expr) : List Expr :=
  if safe then pushKey b e pendC else []
end ConLeche.Cached
end
-- frontx_ind Cached.pushCheapKey on TExpr

-- ConLeche/Cached/CoreC.lean:322
section
namespace ConLeche.Cached
open ConLeche
variable {m : Type → Type}
/-- **`whnf`'s easy cases** (official `whnf`, "Do not cache easy
cases"): sorts, free variables, Π-types and literals, which neither
head-normalize, reduce as literals nor unfold.  A constant or a
lambda-expression still goes through the memo, as in official `whnf`. -/
@[inline] def whnfEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lit _ => true
  | _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.whnfEasy on TExpr

-- ConLeche/Cached/IndPositivity.lean:188
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-! ## Positivity through containers -/
/-- The cached `whnfWalkFuel`: the depth by `depthC`. -/
def whnfWalkFuelC (e : Expr) : Nat := Expr.depthC e + fuelSlack
end ConLeche.Cached
end
-- frontx_ind Cached.whnfWalkFuelC on TExpr

-- ConLeche/Cached/IndPositivity.lean:273
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-- The cached `structUsedLater`: the occurrence by `hasLooseBVarBC`. -/
def structUsedLaterC (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => Expr.hasLooseBVarBC 0 rest
  | none => false
end ConLeche.Cached
end
-- frontx_ind Cached.structUsedLaterC on TExpr

-- ConLeche/Cached/IndPositivity.lean:445
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-- The cached `Expr.piDomsOcc`. -/
def piDomsOccC (names : List Name) (lo hi : Nat) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, .forallE d b => Expr.nestOccC names lo hi d || piDomsOccC names lo hi n b
  | _ + 1, _ => false
end ConLeche.Cached
end
-- frontx_ind Cached.piDomsOccC on TExpr

-- ConLeche/Cached/IndRec.lean:123
section
namespace ConLeche.Cached
open ConLeche
/-- The cached `classGenRecTy`. -/
def classGenRecTyC (g : ClassGen) (c : Nat) : Option Expr := do
  let pre := g.pre
  let rP := pre.length
  let (ifs, maj) ← g.majorC c rP
  let t : Expr := .fvar (rP + ifs.length) maj
  pure (Expr.closeTelescopeC (pre ++ ifs.map g.binder ++ [maj]) 0
    (Expr.mkAppN (g.motVar c) (ifs ++ [t])))
end ConLeche.Cached
end
-- frontx_ind Cached.classGenRecTyC on TExpr

-- ConLeche/Cached/ExprOpsC.lean:934
section
namespace ConLeche.Expr
/-! ## Free-variable replacement (task #498)

`Expr.replaceFVars f`: every free variable `f` maps replaced whole (its
annotation is not descended into), every other one kept.  The cutoff
is the fvar range: a node without a free variable is returned
unchanged.  No cursor (the replacement does not depend on the binder
depth: `f`'s values are spliced as they are). -/
/-- The plain descent of `replaceFVarsC`: the reference of
`replaceFVarsXP` (`replaceFVarsP_spec`, `Verify/Cached/OpsC.lean`). -/
def replaceFVarsP (f : Nat → Option Expr) (e : Expr) : Expr :=
  if e.fvarB = 0 then e else
  match e with
  | .fvar i ty .. => (f i).getD (.fvar i ty)
  | .bvar .. | .sort .. | .const .. | .lit .. => e
  | .app a b .. => mkApp (replaceFVarsP f a) (replaceFVarsP f b)
  | .lam ty body .. => mkLam (replaceFVarsP f ty) (replaceFVarsP f body)
  | .forallE ty body .. => mkForallE (replaceFVarsP f ty) (replaceFVarsP f body)
  | .letE ty val body .. =>
    mkLetE (replaceFVarsP f ty) (replaceFVarsP f val) (replaceFVarsP f body)
  | .proj sn i sub .. => mkProj sn i (replaceFVarsP f sub)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:952
section
namespace ConLeche.Expr
/-- The child step of `replaceFVarsXP`: the cutoff, the compound test,
the exclusivity read. -/
@[inline] def enterRFV (f : @& Nat → Option Expr) (e : @& Expr)
    (memo : MemoXP0 (replaceFVarsP f))
    (rec : (hcut : ¬ e.fvarB = 0) → Squash (ResXP0 (replaceFVarsP f) e)) :
    Squash (ResXP0 (replaceFVarsP f) e) :=
  if hcut : e.fvarB = 0 then Squash.mk (⟨e, (replaceFVarsP_cut hcut).symm⟩, memo)
  else if !isCompound e then rec hcut
  else withExcl e fun excl =>
    if excl then rec hcut else memo.shared e fun _ => rec hcut
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:962
section
namespace ConLeche.Expr
/-- The walk of `replaceFVarsC` (the node is past the cutoff). -/
def replaceFVarsXP (f : @& Nat → Option Expr) (memo : MemoXP0 (replaceFVarsP f)) (e : @& Expr)
    (hcut : ¬ e.fvarB = 0) : Squash (ResXP0 (replaceFVarsP f) e) :=
  match e with
  | .fvar i ty .. =>
    Squash.mk (⟨(f i).getD (.fvar i ty), by rw [replaceFVarsP]; simp [hcut]⟩, memo)
  | .bvar j .. => Squash.mk (⟨.bvar j, by rw [replaceFVarsP]; simp [hcut]⟩, memo)
  | .sort u .. => Squash.mk (⟨.sort u, by rw [replaceFVarsP]; simp [hcut]⟩, memo)
  | .const n us .. => Squash.mk (⟨.const n us, by rw [replaceFVarsP]; simp [hcut]⟩, memo)
  | .lit l .. => Squash.mk (⟨.lit l, by rw [replaceFVarsP]; simp [hcut]⟩, memo)
  | .app a b .. =>
    enterRFV f a memo (fun h => replaceFVarsXP f memo a h) |>.lift fun (⟨a', ha⟩, memo) =>
    enterRFV f b memo (fun h => replaceFVarsXP f memo b h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkApp a' b', by rw [replaceFVarsP]; simp [hcut, ha, hb, mkApp]⟩, memo)
  | .lam ty body .. =>
    enterRFV f ty memo (fun h => replaceFVarsXP f memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRFV f body memo (fun h => replaceFVarsXP f memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLam ty' b', by rw [replaceFVarsP]; simp [hcut, ht, hb, mkLam]⟩, memo)
  | .forallE ty body .. =>
    enterRFV f ty memo (fun h => replaceFVarsXP f memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRFV f body memo (fun h => replaceFVarsXP f memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkForallE ty' b', by rw [replaceFVarsP]; simp [hcut, ht, hb, mkForallE]⟩, memo)
  | .letE ty val body .. =>
    enterRFV f ty memo (fun h => replaceFVarsXP f memo ty h) |>.lift fun (⟨ty', ht⟩, memo) =>
    enterRFV f val memo (fun h => replaceFVarsXP f memo val h) |>.lift fun (⟨v', hv⟩, memo) =>
    enterRFV f body memo (fun h => replaceFVarsXP f memo body h) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨mkLetE ty' v' b', by rw [replaceFVarsP]; simp [hcut, ht, hv, hb, mkLetE]⟩, memo)
  | .proj sn i sub .. =>
    enterRFV f sub memo (fun h => replaceFVarsXP f memo sub h) |>.lift fun (⟨s', hs⟩, memo) =>
    Squash.mk (⟨mkProj sn i s', by rw [replaceFVarsP]; simp [hcut, hs, mkProj]⟩, memo)
end ConLeche.Expr
end

-- ConLeche/Cached/ExprOpsC.lean:993
section
namespace ConLeche.Expr
/-- The cached `Expr.replaceFVars f`: the cutoff, then the walk. -/
def replaceFVarsC (f : Nat → Option Expr) (e : @& Expr) : Expr :=
  if hcut : e.fvarB = 0 then e else
  resTerm (replaceFVarsXP f none e hcut)
end ConLeche.Expr
end

-- ConLeche/Cached/IndRec.lean:158
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-! ## The class match -/
/-- The cached `targetCanonParams`. -/
def targetCanonParamsC (pfvs : List Expr) (e : Expr) : Expr :=
  Expr.replaceFVarsC (fun i => pfvs[i]?) e
end ConLeche.Cached
end
-- frontx_ind Cached.targetCanonParamsC on TExpr

-- ConLeche/Cached/IndRec.lean:162
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-- The cached `Expr.eraseFVarTys`. -/
def eraseFVarTysC (e : Expr) : Expr :=
  Expr.replaceFVarsC (fun i => some (.fvar i (.sort .zero))) e
end ConLeche.Cached
end
-- frontx_ind Cached.eraseFVarTysC on TExpr

-- ConLeche/Kernel/ExprOps.lean:880
section
namespace ConLeche.Expr
/-- The body of a syntactic `∀`-telescope (the expression itself when
it is not a `∀`). -/
def piResult : Expr → Expr
  | .forallE _ b => piResult b
  | e => e
end ConLeche.Expr
end

-- ConLeche/Cached/IndBlock.lean:203
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-! ## The classes: the pre-pass -/
/-- The cached `classReadMinor`: the minor's telescope opened by
`openPisAtFvarsC`, the spines read by `getAppArgsC`. -/
def classReadMinorC (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    Option ClassSlot := do
  let n := dom.piBinders.1.length
  let (fvs, concl) ← openPisAtFvarsC n dom d
  let .fvar p _ := concl.getAppFn | none
  let c ← classOfMotiveVar nP motPos p
  let .const C _ := (← (Expr.getAppArgsC concl).getLast?).getAppFn | none
  let ihs := (List.range fvs.length).filterMap fun q =>
    match (fvs.getD q default).fvarTypeD.piResult.getAppFn with
    | .fvar p' _ =>
      match classOfMotiveVar nP motPos p' with
      | some t =>
        match (Expr.getAppArgsC (fvs.getD q default).fvarTypeD.piResult).getLast? with
        | some a =>
          match a.getAppFn with
          | .fvar f _ => if d ≤ f then some (f - d, t) else none
          | _ => none
        | none => none
      | none => none
    | _ => none
  pure (.minor c C ihs)
end ConLeche.Cached
end
-- frontx_ind Cached.classReadMinorC on TExpr

-- ConLeche/Cached/IndBlock.lean:259
section
namespace ConLeche.Cached
open ConLeche
variable (mode : CheckMode)
/-! ## The classes: the keys and the majors -/
/-- The cached `classKeyCanon`. -/
def classKeyCanonC (params : List Expr) (k : ClassKey) : ClassKey :=
  { k with ds := k.ds.map (targetCanonParamsC params) }
end ConLeche.Cached
end
-- frontx_ind Cached.classKeyCanonC on TExpr

-- ConLeche/Cached/CheckerC.lean:30
section
namespace ConLeche.Cached
open ConLeche
/-!
# The cached declaration driver

The declaration checker *above* `CheckerOps` is shared verbatim with
the generic one: only the core is replaced.  What lives here is the
thin per-declaration phase-driver layer at `CheckCM`, plus the
entry-point record over the cached core.

What the layer is *for*: the per-declaration phase driver that the
parsed-declaration driver (`ConLeche/Cached/ParsedC.lean`) and its bridges
consume — at a `CheckMode` (see `ParsedC.lean`'s header).
-/
/-! ### The direct installers' walker (task #214) -/
/-- `structProjBodiesGo` at the memoised substitution
(`structProjBodiesGoC_eq`). -/
def structProjBodiesGoC (T : Name) (vs : List Expr) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body =>
    (structProjBodiesGoC T (structProjArgP T i :: vs) k (i + 1) body).map
      (Expr.instantiateLiftC fdom vs :: ·)
  | _ + 1, _, _ => none
end ConLeche.Cached
end
-- frontx_ind Cached.structProjBodiesGoC on TExpr

-- ConLeche/Cached/CheckerC.lean:73
section
namespace ConLeche.Cached
open ConLeche
/-- The cached `Expr.dropVars`: each variable dropped by `instantiate1C`
(`dropVarsC_eq`). -/
def Expr.dropVarsC : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.dropVarsC n (Expr.instantiate1C e (.sort .zero))
end ConLeche.Cached
end
-- frontx_ind Cached.Expr.dropVarsC on TExpr


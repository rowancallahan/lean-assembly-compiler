# Astra round 10 — parser task machine for if/let/calls/self-calls + first whole-source run (ADVICE; owner may override)

Relayed advice, not owner decisions. Test oracle: `NANO_V2_ASTRA10_TailTest.lean` (type-checked on Lean 4.29;
note: only ~17/200 generated trees at depth 5 are accepted — bias the generator toward valid trees too).

## Core idea
One PROVISIONAL bit per operand-stack entry: "this subtree contains a self-call that still needs a tail context".
Catches `f n s + 1` AND `(if a == b then f n s else s) + 1`. Confirm once, when the whole successor clause parsed.
Assumptions: function table gives source arity; locals shadow function names; unparenthesised application args
are atoms (`g (x + y)` one arg; `g x + y` = `(g x) + y`); compound args need parentheses; `==`/`<` are NOT in OPS
(IF consumes the comparator).

## Task table (scheduled tasks listed in execution order; push in reverse). t = tail bit, p = precedence,
strict = pop operand and reject if its bit is set.
| 1 EXPR(p,t)    | schedule ATOM(t), OPS(p,t) |
| 2 OPS(p,t)     | next arith op prec q ≥ p: reject provisional left, consume, schedule EXPR(q+1,0), REDUCE(op), OPS(p,t); else finish |
| 3 ATOM(t)      | literal/local push; dispatch `(`, if, let, call, prim, self-call |
| 4 RPAREN       | consume `)`, keep operand + bit |
| 5 REDUCE(op)   | strict-pop r, l; push BIN(op,l,r) bit 0 |
| 6 CMP(t)       | consume == / <; schedule EXPR(0,0), THEN(cmp,t) |
| 7 THEN(cmp,t)  | consume then; schedule EXPR(0,t), ELSE, EXPR(0,t), BUILDIF(cmp) |
| 8 ELSE         | consume else |
| 9 BUILDIF(cmp) | pop e, tb; strict b, a; push IF, bit = max(tb.bit, e.bit) |
| 10 BIND(x,t)   | consume `;`; strict-pop value; install fresh local; schedule EXPR(0,t), ENDLET(mark) |
| 11 ENDLET(mark)| pop body; restore scope; push LET with body's bit |
| 12 ARGS(frame) | next arg via ARGATOM, or build call when all present (all bits 0) |
| 13 ARGATOM     | literal/local or `( EXPR(0,0) )` |
| 14 SELFEND     | strict-pop next state; check shape; push PENDING_SELF bit 1 |
| 15 FINISH(mode)| at clause boundary, exactly one result; bit 1 allowed only in successor clause; commit root |

## One step (pseudo-code; helpers expand to bget/bset + cursor updates, every write threads h)
```text
require sp>0; sp := sp-1; (c,a,t) := read3(taskBase+3*sp); k := peek()
c==1: schedule(ATOM(t), OPS(a,t))
c==2: if arithmetic(k): q := prec(k); if q<a: done; require top().bit==0; advance(); schedule(EXPR(q+1,0), REDUCE(k), OPS(a,t))
c==3: "(" -> advance; schedule(EXPR(0,t), RPAREN)
      "if" -> advance; schedule(EXPR(0,0), CMP(t))
      "let" -> advance; x := takeName(); need(":="); schedule(EXPR(0,0), BIND(x,t))
      literal -> put(CONST(w),0)
      name d := resolve: local -> require ordinary data; put(LOCAL(slot,width),0)
             d==currentFunction -> require successorClause, t==1, arity==2, next name resolves to predecessor binder;
                                   schedule(ARGATOM, SELFEND)
             else -> push(12, newCallFrame(d, arity(d), vp), 0)
c==4: need(")")
c==5: r := strict(); l := strict(); put(BIN(a,l,r),0)
c==6: cmp := takeComparator(); schedule(EXPR(0,0), THEN(cmp,t))
c==7: need("then"); schedule(EXPR(0,t), ELSE, EXPR(0,t), BUILDIF(a))
c==8: need("else")
c==9: e := pop(); b := pop(); y := strict(); x := strict(); put(IF(a,x,y,b.id,e.id), max(b.bit,e.bit))
c==10: need(";"); v := strict(); mark := scopeHeight; bindFresh(a,v); schedule(EXPR(0,t), ENDLET(mark))
c==11: b := pop(); d := bindingAt(a); scopeHeight := a; put(LET(d.slot,d.width,d.value,b.id), b.bit)
c==12: remaining==0 -> copy operand ids (source order) to a contiguous child range AFTER parsing, verify bits 0,
       restore vp, put(call/prim,0); else decrement; schedule(ARGATOM, ARGS(a))
c==13: "(" -> advance; schedule(EXPR(0,0), RPAREN) else put(literal or local,0)
c==14: s := strict(); checkStateShape(s); put(PENDING_SELF(s),1)
c==15: require clause boundary; require vp==savedBase+1; if top().bit==1 require successor; commitRoot(top().id)
else reject
```
Details: Z starts EXPR(0,0)+FINISH, B starts EXPR(0,1)+FINISH; missing/extra args and leftover tokens fail.
Parens preserve the bit; IF/LET propagate; arithmetic rejects; nothing silently clears it.
Pairs: at `(` schedule a delimiter task; `,` rejects provisional first field, later fields bit 0, build PAIR.
Same strict rule for primitives. Flatten only committed roots: emit tag+payload, push child ids in reverse at
30000, PENDING_SELF emitted as CONTINUE; calls/pairs store (childBase,count).
Invariant: a bit-1 subtree only passes through tail-preserving edges (if branch, let body, grouping), so every
committed self-call has a tail path to the successor root.

## First whole-source run
1. Freeze s, κ, ABI, image format, load policy. Run ordinary Lean Cκ(s) first; record status, length, bytes,
   per-region high-water marks.
2. B₂ := B₁(s). Diff vs ordinary Lean at each boundary: tokens, committed AST + metadata, code bytes; if code
   differs with equal ASTs, compare labels/fixups. Save exactly the output slice.
3. Fresh machine: B₃ := B₂(s), same s and κ; capture the same stage outputs; first differing stage = where to look.
4. Check status, length, every byte of B₂ vs B₃. Repeat with different initial work-memory fill.
   Proved milestone: certify Cκ(s) = ok B₂ and apply B₂'s Sail theorem on s.
Rule out NOW in C: stale records/counters (reset on entry, init every field; test two scratch fill patterns);
padding/capacity bytes in output (serialize exactly the declared length); ID/label/emission order (source
traversal order, specified fixup order, labels relative to layout); work addresses leaking into code (indices +
symbolic labels); scale boundaries (region ends, width conversions, branch ranges, image length).
CAPACITY WARNING: operand region [5000,10000) at 2 words = 2,500 operands; nodes [10000,30000) at 8 words =
2,500 nodes. A 23 KB source will exceed this. Put all capacities in ONE layout descriptor, compute region bases
by checked prefix sums, fuel as a separate κ field. Record per stage: token words, nodes, child ids, task depth,
operand depth, bindings, flatten depth, code bytes, fixups, fuel used.

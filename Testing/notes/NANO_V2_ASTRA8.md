# Astra round 8 — least code to self-compile (ADVICE; owner may override)

Relayed advice, not owner decisions.

Architecture: restricted Lean parser -> small structured AST (flat word-buffer records) -> fixed-frame
stack code generator with label fixups (expand+assemble fused operationally, specs kept separate).
NO inliner, real calls, no register allocation, no branch relaxation, no parser generator.

Ranking (estimates): 1 restrict C's source syntax; 2 real calls instead of inliner; 3 uniform stack codegen;
4 fuse expand+assemble; 5 small keyword/operator tables; 6 direct parser->machine code / general tables: defer.

Call convention: flatten pairs to fixed word widths; args in fixed frame slots; results in caller-provided
slots; save ra + old fp; one slot per local (no reuse); empty expr stack at statement boundaries and loop
headers; self-tail recursion -> local loop jumps; remaining call graph ACYCLIC (callee-before-caller order).
Prove functions in call-graph order using callee contracts; loops by fuel induction.
Obligations: frame allocation, stack bounds, ra preservation, buffer ownership across calls.

AST nodes: const, local read, prim op, let, pair build/decompose, if, call, loop/continue/return, buffer prims.
Codegen: memory expr stack + frame slots; loop continue = compute all new state, then commit, dec fuel, jump.
Branches: short inverted branch over fixed-size long jump; fixed-size long calls; global code-size bound.

Remove from C's source: Int64, && || <= >= != spellings, general match, HOFs, arbitrary recursion,
polymorphism, alternate literal/projection syntax, implicit conversions. Keep UInt64, small cmp set, if, let,
direct calls, Nat fuel tail loops (Nat only in fuel role), nested pairs, buffer size/read/write/append/new + I/O.

First: one vertical example — buffer-processing fuel loop calling a helper that has its own loop and returns a pair.

# TINYSELF: smallest-scale self-hosting data point (branch `tinyself`)

Files: `Riscv/Frontx/TinySelf.lean` (`tc`/`tinyCompile`, `tinyRun`), `Riscv/Frontx/TinySmall.lean` (3-op subset, machine theorem),
`Testing/asm/emit_tiny.lean` (words, cases), `Testing/asm/tiny/{driver.c,tiny_test.py}` (run compiled tiny code on qemu-riscv64),
`Testing/asm/frontx_test.py check N tinysm` (front-end binary on QEMU + Sail).

## Language
Program = pairs `(op, arg)`. Registers: acc = t0; a0 = input ptr, a1 = remaining count, a2 = output ptr. One op = one RISC-V word.
`0 ADDI k` acc += sext k · `1 XORI k` · `2 LOAD` acc = *a0 · `3 STORE` *a2 = acc · `4 JNZ k` pc += sext k if acc ≠ 0 ·
`5 LEN` acc = a1 · `6 JZ k` · `7 INCIN` a0++ · `8 INCOUT` a2++ · `9 DECN` a1-- · else nop. Compiled code ends with `ret`.
`tinyCompile : ByteArray → List UInt8` (= `tc xs.data.toList`), reference `tinyRun prog input`.

## Results
| | |
|---|---|
| `tinyCompile` accepted by front end | yes: `tc.view` 27 vars / 19 slots, 78 obligations, 53 s (needs `maxHeartbeats 0`), 1235 words; `tinyCompile.exec` (source level) with only propext/Classical.choice/Quot.sound |
| `tinyCompile.implements1` (machine theorem) | **no**: needs `slots ≤ 16`, has 19 |
| (a) front-end binary of `tinyCompile` vs Lean on QEMU | **no**: the 19-slot binary does not terminate on QEMU or Sail (even case 1). Cause not isolated beyond "slots > 16" (the 12-slot subset works; CRC-32 has 12) |
| (a) for subset `TinySmall` (ops LOAD, STORE, nop; 12 slots, 212 words) | **yes**: `tinySm.implements1` generated (the usual 77 model axioms); 47 cases (5 programs + 40 random byte strings + edge cases) QEMU == Sail == Lean `tinyCompile`-subset |
| (b) Lean `tinyCompile` output on qemu-riscv64 vs `tinyRun` | yes, 85 (program, input) cases, 5 programs (xor-copy, length, +1, countdown, branch-skip) incl. forward/backward `JNZ`/`JZ` |
| (b) with the front-end binary as compiler | not reached (blocked by (a)); only the subset is covered |
| (c) true bootstrap (compiler written in the tiny language) | not attempted: one accumulator, no table lookup / no second register / no random access to input |

Run: `lake build Riscv.Frontx.TinySelf Riscv.Frontx.TinySmall; lake env lean --tstack=400000 Testing/asm/emit_tiny.lean; python3 Testing/asm/tiny/tiny_test.py; python3 Testing/asm/frontx_test.py check 50 tinysm`.
(Setup on a fresh box: `Testing/setup/box.sh`; Sail C simulator in `/home/user/deps/sailsim`.)

## Front-end rejections hit, and the change made
1. `UInt8` `a <<< 4`, `<<< 7`: `frontx: could not prove … simp made no progress` (shift on UInt8). → `(a.toUInt64 <<< 4).toUInt8`. (`>>>` and `&&&`, `|||` on UInt8 are fine.)
2. UInt64 sign extension `(k.toUInt64 ^^^ 128) - 128`, and the `if a < 128 then … else k + 0xFF…00` form, then `<<<`/`>>>`/`&&&` of it: obligation `BExp.denote … = r8 …` not provable. → no 64-bit sign extension; branch-immediate bytes derived by hand on `UInt8` (valid since offset = 4·sext k fits 10 bits).
3. `if` result used inside `+` with a shift (`sg a + (sg a >>> 1)`): same unprovable obligation. → write the constant directly in an `if`.
4. `let b := a + a; …` in a term: `unsupported term`.
5. Size: 8 arms × 12-byte cons chains (one tiny op = 3 words): `frontx_compile` heartbeat timeout, then > 35 min with `maxHeartbeats 0` (44 vars / 36 slots, 388 obligations) — abandoned. → one op = one word (4-byte chains); then 10 arms × chains still hit the heartbeat limit (needs `set_option maxHeartbeats 0 in`, 28 s); tables `W0..W3` (hygiene-off macros, not helper functions: each helper-call argument became a variable, 21 → 19 slots) cut the obligations to 78 but time to 53 s.
6. A phase counter to cut the chain length (`tc ph op a ys`, recursion passing the same list unchanged, or re-consing `op :: a :: rest`): `frontx_view` loops (`tc.eq_1` "possibly looping simp theorem", max recursion), or Lean cannot prove termination; with a hand `termination_by` the view says `the match does not reduce` (match on a `Nat` literal phase with several scrutinees). Abandoned.
7. Machine theorem: `frontx_implements_list` needs `slots ≤ 16` (`decide`) — the number of variables (user + temporaries) is the limit that blocks scaling: 19 slots for a 10-op dispatch, 12 for 3 ops. Every extra output byte expression per arm costs variables.
8. Not rejected but relevant: `tinyRun` (fuel loop, `Array`, `Nat`, UInt64) is plain Lean, outside the front end (state-carrying loop with an array would need an array/heap parameter).

## What blocks self-hosting at this scale
(i) the 16-slot limit (variable count) in the machine theorem and apparently in the generated code; a dispatch over ~10 ops with byte arithmetic needs ~19; (ii) no way to split a function into several non-tail pieces or to carry a phase through a list view (items 5–6); (iii) elaboration cost of wide `if` trees (heartbeats, ~1 min); (iv) UInt8 shifts and 64-bit sign extension unsupported (items 1–3). Not hit but expected next: a real compiler needs label/offset resolution (a second pass over its own output) — output is write-only (`List UInt8` destination passing), no read-back.

# Experiments
Format: id / branch/commit / target / variant / measure / time limit / claimed by / result.

## Lexer-halves bisection (posted by main session; owner: split until every piece is < 5 min)
Setup for all: branch lexsplit-probe. Build ONLY the deps: `lake build Nano.ElabBSplit Nano.ElabBSplitE Nano.CheckedSpill Riscv.Frontx.ListOutExamples Riscv.Frontx.Impl1` (NOT `lake build Nano`).
Run: `/usr/bin/time -f '%e s %U user %M KB' timeout 45m lake env lean --tstack=4000000 <file> 2>&1 | tail -60`.
Measure: wall/user/RSS, OK/FAIL, and for *_full every profiler line (per-command times). Report to main session via send_message.

## id: lx-E-full
- target: Testing/nano/lexsplit/E_full.lean (emitter half, whole file with listCS, profiled)
- claimed by: pool runner session_01MfKuVc8tEdvy6giK55Yuj7 (claim written by main session)
## id: lx-V-full
- target: Testing/nano/lexsplit/V_full.lean (validator half, whole file, profiled)
- claimed by: profiler session_01MfKuVaD8AUJ4tttPqcW459 (claim written by main session)
## id: lx-E-compile
- target: Testing/nano/lexsplit/E_compile.lean (through frontx_compile only)
- claimed by: CI tender session_01MfKuVayioXkLETjySYQfkw (claim written by main session)
## id: lx-V-compile
- target: Testing/nano/lexsplit/V_compile.lean (through frontx_compile only)
- claimed by: CI tender session_01MfKuVa2yyxQiaKEDu6hkHa (claim written by main session)
## result lx-V-compile (CI tender ir-strong, 08:38)
- FAIL at the frontx_compile line: "No goals to be solved". 186.9 s wall, 2.41 GB. translate+step 107 s, kernel 0.4 s, induction 72 s, exec thm 2.4 s; 79 vars, 71 slots, 986 obligations. Sent to nano-final.
## note (08:55)
- The nano-final tender's `lake build` shows ElabBESelf AND ElabBVSelf at 57+ min (with listCS). frontx_compile alone is ~3-4 min, so the time is after it: suspect pickSpill's 7 spill-all modes all fail optB and it falls back to pickC (the hour-long search).
## id: lx-E-pick
- target: Testing/nano/lexsplit/E_pick.lean (compile + entry, then per mode: colorB / optB result + ms; no implements)
- measure: wall, and every "mode N: ..." line
- claimed by: CI tender session_01MfKuVa2yyxQiaKEDu6hkHa (claim written by main session)

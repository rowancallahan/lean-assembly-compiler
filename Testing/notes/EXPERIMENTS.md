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

# BUILD_PROFILE

Measurement and plan only; no compiler source was changed. Lean 4.29.0, 4 cores, 15 GB, `../deps/sail-riscv-lean` restored from `origin/build-cache`.

**Method.** The 190 modules of `Spec`, `Compiler`, `Riscv.{Steps,Direct,Back,Examples}` and `Riscv.Frontx` (`Riscv/Legacy` excluded) were built one at a time in dependency order with `lake build +Module` (flags from `lakefile.toml`: `--tstack=400000 --threads=2`). Each time is that module's wall time, including ~0.4 s of lake start-up (about 75 s over all 190). The memory column is peak RSS of the lake process tree (`wait4`). The top 10 were re-run with `lean -Dprofiler=true` to see what dominates. `Arm.CompilerArm` is 45 lines and builds in 0.5 s. Raw data: the table in section 1.

**Totals.**
- Sequential sum: 2181 s (36 min).
- Median module: 2.6 s. 69 modules take under 2 s.
- 40 modules take at least 10 s and account for 1765 s (81%).
- Peak RSS: 5.0 GB (`Frontx.TinySelf`), then 3.7 GB (`Frontx.MulExamples`). Anything importing the Sail model starts at about 1.4 GB. Four such jobs in parallel can exceed this box's 15 GB, so the memory budget limits `-j`.
- Simulated wall time (list scheduling, 4 workers, one slot per module): 770 s today. An unlimited number of workers gives the critical path, 731 s. Real `lake build -j4` wall time was not measured.

## 1. Per-module table (sorted by seconds)

The last column is a grep of the file for constructs, not a measurement. The measured cause for the top 10 is in section 3.

| # | module | s | lines | peak RSS MB | s/100 lines | constructs in file (grep heuristic, not measured) |
|--:|---|--:|--:|--:|--:|---|
| 1 | Riscv.Examples.PipeExamples | 261.6 | 216 | 1631 | 121.1 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, simp |
| 2 | Riscv.Frontx.MulExamples | 240.0 | 62 | 3702 | 387.1 | compile%/frontx commands (interpreter+exec thm) |
| 3 | Riscv.Frontx.TinySelf | 129.6 | 66 | 5039 | 196.4 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 4 | Riscv.Steps.GenMem | 126.9 | 237 | 2726 | 53.5 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 5 | Riscv.Steps.GenALU | 73.5 | 128 | 2466 | 57.4 | decide/rfl kernel, simp |
| 6 | Riscv.Back.BootReset | 72.5 | 173 | 1982 | 41.9 | Sail-model eval (sailEval), decide/rfl kernel, simp |
| 7 | Riscv.Frontx.NameExamples | 61.7 | 49 | 2112 | 125.9 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 8 | Riscv.Frontx.Translate | 60.1 | 3619 | 2079 | 1.7 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 9 | Riscv.Frontx.WaExp | 45.9 | 518 | 1680 | 8.9 | decide/rfl kernel, omega, simp |
| 10 | Riscv.Steps.GenBranch | 45.4 | 83 | 2231 | 54.7 | simp |
| 11 | Riscv.Frontx.Ind2Examples | 45.2 | 176 | 1997 | 25.7 | compile%/frontx commands (interpreter+exec thm), simp |
| 12 | Riscv.Frontx.IndExamples | 42.6 | 150 | 2247 | 28.4 | compile%/frontx commands (interpreter+exec thm) |
| 13 | Riscv.Frontx.ExceptBook | 41.8 | 257 | 2006 | 16.3 | compile%/frontx commands (interpreter+exec thm) |
| 14 | Riscv.Frontx.WaMul | 41.5 | 115 | 2412 | 36.1 | defs/structural |
| 15 | Riscv.Frontx.BookExamples | 38.1 | 157 | 1787 | 24.3 | compile%/frontx commands (interpreter+exec thm), omega, simp |
| 16 | Riscv.Frontx.ExceptExamples | 32.9 | 155 | 1939 | 21.2 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 17 | Riscv.Frontx.IndCmpExamples | 31.7 | 112 | 2082 | 28.3 | compile%/frontx commands (interpreter+exec thm) |
| 18 | Riscv.Frontx.PairExamples | 31.5 | 137 | 1896 | 23.0 | compile%/frontx commands (interpreter+exec thm) |
| 19 | Riscv.Steps.GenMul | 26.8 | 85 | 1865 | 31.5 | decide/rfl kernel, omega, simp |
| 20 | Riscv.Frontx.WaLeanZip | 26.0 | 88 | 2051 | 29.5 | defs/structural |
| 21 | Riscv.Steps.Step | 25.1 | 395 | 1747 | 6.4 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 22 | Riscv.Back.BootV | 22.1 | 193 | 1852 | 11.5 | Sail-model eval (sailEval), decide/rfl kernel, simp |
| 23 | Riscv.Steps.Regs | 21.6 | 1351 | 1715 | 1.6 | decide/rfl kernel, omega, simp |
| 24 | Riscv.Frontx.ForExamples | 18.5 | 129 | 1683 | 14.3 | compile%/frontx commands (interpreter+exec thm) |
| 25 | Riscv.Steps.GenTac | 15.9 | 308 | 2031 | 5.2 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 26 | Compiler.IndOk | 15.0 | 924 | 853 | 1.6 | decide/rfl kernel, omega, simp |
| 27 | Riscv.Direct.SortMergeSrc | 14.6 | 416 | 2042 | 3.5 | decide/rfl kernel, omega, simp |
| 28 | Riscv.Frontx.ListOutExamples | 13.5 | 124 | 1673 | 10.9 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 29 | Riscv.Examples.MsortB | 13.4 | 435 | 2040 | 3.1 | decide/rfl kernel, omega, simp |
| 30 | Riscv.Back.Implements1 | 13.2 | 226 | 1741 | 5.8 | decide/rfl kernel, omega, simp |
| 31 | Riscv.Frontx.Machine | 13.0 | 146 | 1911 | 8.9 | compile%/frontx commands (interpreter+exec thm) |
| 32 | Riscv.Frontx.ScalarExamples | 12.9 | 102 | 1748 | 12.6 | compile%/frontx commands (interpreter+exec thm) |
| 33 | Riscv.Examples.Implements1Opt | 12.6 | 294 | 2379 | 4.3 | decide/rfl kernel, omega, simp |
| 34 | Riscv.Back.Top | 12.5 | 268 | 1651 | 4.7 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 35 | Riscv.Frontx.IndCmd | 12.4 | 1248 | 1790 | 1.0 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 36 | Riscv.Frontx.TinySmall | 11.2 | 19 | 1933 | 58.9 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 37 | Riscv.Frontx.WaCmd | 10.9 | 831 | 1808 | 1.3 | decide/rfl kernel, omega, simp |
| 38 | Riscv.Examples.MsortBOpt | 10.8 | 139 | 2401 | 7.8 | decide/rfl kernel, omega, simp |
| 39 | Riscv.Frontx.RecExamples | 10.4 | 37 | 1807 | 28.1 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 40 | Riscv.Frontx.Examples | 10.0 | 121 | 1645 | 8.3 | compile%/frontx commands (interpreter+exec thm), omega, simp |
| 41 | Riscv.Steps.Branch | 8.8 | 219 | 1756 | 4.0 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 42 | Riscv.Direct.Loop | 8.8 | 289 | 1694 | 3.0 | decide/rfl kernel, omega, simp |
| 43 | Compiler.Front.PipeSrc | 8.4 | 815 | 1789 | 1.0 | decide/rfl kernel, omega, simp |
| 44 | Riscv.Examples.VacuityBase | 8.2 | 173 | 1644 | 4.7 | decide/rfl kernel, omega, simp |
| 45 | Spec.Riscv | 8.1 | 88 | 1494 | 9.2 | defs/structural |
| 46 | Compiler.Front.PipeStdBMachine | 8.1 | 245 | 1944 | 3.3 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 47 | Riscv.Direct.SortMergeMachine | 7.5 | 182 | 1827 | 4.1 | decide/rfl kernel, omega, simp |
| 48 | Riscv.Frontx.ListExamples | 7.3 | 128 | 1614 | 5.7 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 49 | Riscv.Frontx.WaComp | 7.3 | 268 | 1696 | 2.7 | decide/rfl kernel, omega, simp |
| 50 | Riscv.Back.SortMerge | 7.1 | 239 | 1843 | 3.0 | decide/rfl kernel, omega, simp |
| 51 | Riscv.Frontx.Fast | 7.1 | 1584 | 1752 | 0.4 | decide/rfl kernel, omega, simp |
| 52 | Riscv.Back.Calls | 7.0 | 215 | 1802 | 3.3 | decide/rfl kernel, omega, simp |
| 53 | Compiler.CStmt | 6.8 | 661 | 710 | 1.0 | decide/rfl kernel, omega, simp |
| 54 | Riscv.Back.CallsImpl1W | 6.0 | 170 | 1768 | 3.5 | decide/rfl kernel, omega, simp |
| 55 | Riscv.Steps.GenRegs | 5.9 | 114 | 1611 | 5.2 | Sail-model eval (sailEval), decide/rfl kernel, simp |
| 56 | Riscv.Examples.Implements1Ex | 5.6 | 403 | 1769 | 1.4 | decide/rfl kernel, omega, simp |
| 57 | Riscv.Frontx.CallExamples | 5.6 | 47 | 1610 | 11.9 | compile%/frontx commands (interpreter+exec thm) |
| 58 | Riscv.Frontx.WaStmt | 5.6 | 749 | 1734 | 0.7 | decide/rfl kernel, omega, simp |
| 59 | Riscv.Back.Implements1Opt | 5.5 | 325 | 1757 | 1.7 | decide/rfl kernel, omega, simp |
| 60 | Compiler.IndMain | 5.5 | 411 | 657 | 1.3 | decide/rfl kernel, omega, simp |
| 61 | Riscv.Frontx.WaPg | 5.2 | 595 | 1694 | 0.9 | decide/rfl kernel, omega, simp |
| 62 | Compiler.BStmt | 5.1 | 684 | 603 | 0.7 | decide/rfl kernel, omega, simp |
| 63 | Compiler.Front.PipeStdSrc | 5.1 | 938 | 1682 | 0.5 | decide/rfl kernel, omega, simp |
| 64 | Compiler.IndDec | 4.9 | 611 | 608 | 0.8 | decide/rfl kernel, omega, simp |
| 65 | Riscv.Back.CallsImpl1 | 4.9 | 150 | 1689 | 3.3 | decide/rfl kernel, omega, simp |
| 66 | Riscv.Direct.Arr2F | 4.8 | 387 | 1621 | 1.2 | decide/rfl kernel, omega, simp |
| 67 | Compiler.Front.PipeIMachine | 4.8 | 204 | 1742 | 2.4 | decide/rfl kernel, omega, simp |
| 68 | Riscv.Examples.MutationSort | 4.6 | 159 | 1785 | 2.9 | decide/rfl kernel, omega, simp |
| 69 | Riscv.Frontx.RecCmd | 4.6 | 387 | 1672 | 1.2 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 70 | Riscv.Back.Wide | 4.5 | 543 | 1607 | 0.8 | decide/rfl kernel, omega, simp |
| 71 | Riscv.Steps.Compat | 4.4 | 242 | 1640 | 1.8 | decide/rfl kernel, omega, simp |
| 72 | Riscv.Back.Boot | 4.2 | 440 | 1678 | 1.0 | decide/rfl kernel, omega, simp |
| 73 | Riscv.Steps.GenUse | 4.0 | 113 | 1587 | 3.5 | decide/rfl kernel, simp |
| 74 | Riscv.Steps.SailEval | 3.8 | 390 | 1500 | 1.0 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 75 | Riscv.Frontx.Tree | 3.8 | 722 | 1628 | 0.5 | decide/rfl kernel, omega, simp |
| 76 | Compiler.Front.PipeOk | 3.7 | 308 | 1692 | 1.2 | decide/rfl kernel, omega, simp |
| 77 | Riscv.Examples.InsB | 3.7 | 336 | 1701 | 1.1 | decide/rfl kernel, omega, simp |
| 78 | Riscv.Frontx.WaUpd | 3.7 | 354 | 1616 | 1.0 | decide/rfl kernel, omega, simp |
| 79 | Riscv.Examples.CallExamples | 3.6 | 233 | 1636 | 1.5 | decide/rfl kernel, omega, simp |
| 80 | Riscv.Direct.Arr2 | 3.5 | 298 | 1599 | 1.2 | decide/rfl kernel, omega, simp |
| 81 | Compiler.Front.PipeI | 3.5 | 341 | 1666 | 1.0 | decide/rfl kernel, omega, simp |
| 82 | Riscv.Direct.Arr | 3.4 | 406 | 1608 | 0.8 | decide/rfl kernel, omega, simp |
| 83 | Compiler.Opt.SR | 3.4 | 1183 | 614 | 0.3 | decide/rfl kernel, omega, simp |
| 84 | Riscv.Frontx.WaLang | 3.3 | 329 | 1584 | 1.0 | decide/rfl kernel, omega, simp |
| 85 | Compiler.Front.PipeFront | 3.1 | 395 | 1654 | 0.8 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 86 | Riscv.Frontx.WaImpl | 3.1 | 399 | 1664 | 0.8 | decide/rfl kernel, omega, simp |
| 87 | Riscv.Direct.Compiler | 3.0 | 358 | 1581 | 0.8 | decide/rfl kernel, omega, simp |
| 88 | Riscv.Direct.SortIns | 3.0 | 304 | 1588 | 1.0 | decide/rfl kernel, omega, simp |
| 89 | Compiler.Front.PipeStdB | 3.0 | 429 | 1647 | 0.7 | decide/rfl kernel, omega, simp |
| 90 | Riscv.Frontx.DataExamples | 3.0 | 34 | 1580 | 8.8 | compile%/frontx commands (interpreter+exec thm), omega |
| 91 | Riscv.Frontx.StringExamples | 2.9 | 21 | 1576 | 13.8 | compile%/frontx commands (interpreter+exec thm) |
| 92 | Riscv.Frontx.Impl1 | 2.8 | 329 | 1621 | 0.9 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 93 | Compiler.Opt.Sel | 2.6 | 694 | 579 | 0.4 | decide/rfl kernel, omega, simp |
| 94 | Riscv.Frontx.Rep | 2.6 | 345 | 1569 | 0.8 | decide/rfl kernel, omega, simp |
| 95 | Riscv.Frontx.Bytes | 2.6 | 156 | 1563 | 1.7 | omega, simp |
| 96 | Riscv.Examples.ArrExamples | 2.5 | 283 | 1558 | 0.9 | decide/rfl kernel, omega, simp |
| 97 | Compiler.Opt.Lower | 2.5 | 754 | 583 | 0.3 | decide/rfl kernel, omega, simp |
| 98 | Riscv.Direct.SortMergeGen | 2.5 | 109 | 1598 | 2.3 | decide/rfl kernel, omega, simp |
| 99 | Riscv.Back.Call | 2.5 | 177 | 1559 | 1.4 | decide/rfl kernel, omega, simp |
| 100 | Riscv.Examples.Crc | 2.5 | 359 | 1628 | 0.7 | decide/rfl kernel, omega, simp |
| 101 | Riscv.Frontx.Checked | 2.5 | 137 | 1618 | 1.8 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 102 | Riscv.Steps.MemSteps | 2.4 | 126 | 1534 | 1.9 | omega, simp |
| 103 | Riscv.Back.Iface | 2.4 | 365 | 1555 | 0.7 | decide/rfl kernel, omega, simp |
| 104 | Riscv.Frontx.Sub | 2.4 | 423 | 1557 | 0.6 | decide/rfl kernel, omega, simp |
| 105 | Riscv.Steps.MemStep | 2.3 | 105 | 1529 | 2.2 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 106 | Riscv.Back.OptB | 2.3 | 376 | 1592 | 0.6 | decide/rfl kernel, omega, simp |
| 107 | Riscv.Examples.TreeEval | 2.3 | 146 | 1582 | 1.6 | decide/rfl kernel, omega, simp |
| 108 | Compiler.Opt.BSel | 2.2 | 460 | 570 | 0.5 | decide/rfl kernel, omega, simp |
| 109 | Compiler.CProg | 2.1 | 236 | 547 | 0.9 | omega, simp |
| 110 | Riscv.Direct.ArrExp | 2.1 | 218 | 1552 | 1.0 | decide/rfl kernel, omega, simp |
| 111 | Riscv.Direct.SortMachine | 2.1 | 159 | 1557 | 1.3 | decide/rfl kernel, omega, simp |
| 112 | Riscv.Back.Arr | 2.1 | 204 | 1556 | 1.0 | decide/rfl kernel, omega, simp |
| 113 | Riscv.Frontx.MulRep | 2.1 | 137 | 1550 | 1.5 | decide/rfl kernel, omega, simp |
| 114 | Riscv.Frontx.Ind | 2.1 | 218 | 1597 | 1.0 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 115 | Riscv.Direct.MemCompiler | 2.0 | 122 | 1536 | 1.6 | decide/rfl kernel, omega, simp |
| 116 | Compiler.Opt.Flow | 2.0 | 611 | 591 | 0.3 | decide/rfl kernel, simp |
| 117 | Riscv.Direct.Arr2Exp | 2.0 | 119 | 1553 | 1.7 | decide/rfl kernel, omega, simp |
| 118 | Compiler.Opt.BFn | 2.0 | 251 | 560 | 0.8 | decide/rfl kernel, omega, simp |
| 119 | Compiler.Ind | 2.0 | 532 | 521 | 0.4 | decide/rfl kernel, omega, simp |
| 120 | Riscv.Examples.Implements1Pipe | 2.0 | 121 | 1605 | 1.7 | omega, simp |
| 121 | Riscv.Examples.VacuityTop | 2.0 | 104 | 1608 | 1.9 | decide/rfl kernel, omega, simp |
| 122 | Compiler.Arr | 1.9 | 281 | 528 | 0.7 | omega, simp |
| 123 | Compiler.Front.PipeMachine | 1.9 | 221 | 1602 | 0.9 | omega, simp |
| 124 | Compiler.Front.PipeStdMachine | 1.9 | 180 | 1604 | 1.1 | omega, simp |
| 125 | Riscv.Steps.Arr2Step | 1.9 | 66 | 1518 | 2.9 | Sail-model eval (sailEval), decide/rfl kernel, simp |
| 126 | Riscv.Steps.CompatArr2 | 1.9 | 93 | 1563 | 2.0 | decide/rfl kernel, omega, simp |
| 127 | Riscv.Back.BStmt | 1.9 | 209 | 1571 | 0.9 | decide/rfl kernel, omega, simp |
| 128 | Riscv.Examples.LoopExamples | 1.9 | 144 | 1550 | 1.3 | decide/rfl kernel, omega, simp |
| 129 | Compiler.Front.Pipe | 1.8 | 254 | 1542 | 0.7 | simp |
| 130 | Compiler.Front.PipeStd | 1.8 | 264 | 1545 | 0.7 | decide/rfl kernel, simp |
| 131 | Riscv.Direct.Arr2Code | 1.8 | 194 | 1543 | 0.9 | simp |
| 132 | Riscv.Back.Frame | 1.8 | 189 | 1550 | 1.0 | decide/rfl kernel, omega, simp |
| 133 | Riscv.Back.Keep | 1.8 | 78 | 1540 | 2.3 | decide/rfl kernel, omega, simp |
| 134 | Compiler.Front.Reify | 1.8 | 105 | 1528 | 1.7 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel |
| 135 | Riscv.Back.Stmt | 1.8 | 105 | 1532 | 1.7 | decide/rfl kernel, omega, simp |
| 136 | Riscv.Examples.VacuityExp | 1.8 | 139 | 1538 | 1.3 | decide/rfl kernel, omega, simp |
| 137 | Riscv.Frontx.For | 1.8 | 213 | 1550 | 0.8 | decide/rfl kernel, omega, simp |
| 138 | Riscv.Frontx.Exc | 1.8 | 121 | 1541 | 1.5 | decide/rfl kernel, omega, simp |
| 139 | Compiler.Exp | 1.7 | 221 | 540 | 0.8 | decide/rfl kernel, omega, simp |
| 140 | Riscv.Examples.VacuitySort | 1.7 | 133 | 1578 | 1.3 | decide/rfl kernel, omega, simp |
| 141 | Riscv.Direct.MemModel | 1.6 | 169 | 1501 | 0.9 | decide/rfl kernel, omega, simp |
| 142 | Riscv.Back.Exp | 1.6 | 83 | 1528 | 1.9 | decide/rfl kernel, omega, simp |
| 143 | Compiler.Opt.Live | 1.6 | 447 | 525 | 0.4 | decide/rfl kernel, simp |
| 144 | Riscv.Examples.BootEx | 1.6 | 88 | 1617 | 1.8 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 145 | Riscv.Examples.MutationBase | 1.6 | 159 | 1534 | 1.0 | decide/rfl kernel, omega, simp |
| 146 | Riscv.Frontx.IndStr | 1.6 | 74 | 1592 | 2.2 | compile%/frontx commands (interpreter+exec thm), decide/rfl kernel, omega |
| 147 | Riscv.Frontx.Rec | 1.6 | 62 | 1597 | 2.6 | decide/rfl kernel, omega, simp |
| 148 | Riscv.Back.Opt | 1.5 | 96 | 1542 | 1.6 | decide/rfl kernel |
| 149 | Riscv.Examples.GcdOpt | 1.5 | 137 | 1563 | 1.1 | decide/rfl kernel, omega, simp |
| 150 | Spec.Machines | 1.4 | 41 | 457 | 3.4 | defs/structural |
| 151 | Riscv.Direct.LoopRule | 1.4 | 45 | 1506 | 3.1 | defs/structural |
| 152 | Riscv.Direct.Arr2Src | 1.4 | 103 | 1523 | 1.4 | decide/rfl kernel, simp |
| 153 | Riscv.Examples.MutationExp | 1.4 | 91 | 1542 | 1.5 | decide/rfl kernel, omega, simp |
| 154 | Compiler.BExp | 1.3 | 133 | 517 | 1.0 | omega, simp |
| 155 | Compiler.Front.PipeEncode | 1.3 | 23 | 1514 | 5.7 | decide/rfl kernel, simp |
| 156 | Riscv.Back.OptArr | 1.3 | 77 | 1550 | 1.7 | simp |
| 157 | Spec.Implements1 | 1.3 | 72 | 1476 | 1.8 | defs/structural |
| 158 | Spec.RiscvMachine | 1.3 | 45 | 1491 | 2.9 | defs/structural |
| 159 | Riscv.Steps.WordsBase | 1.2 | 36 | 1492 | 3.3 | Sail-model eval (sailEval), decide/rfl kernel, omega |
| 160 | Compiler.Wide | 1.2 | 161 | 496 | 0.7 | decide/rfl kernel, simp |
| 161 | Compiler.IndSup | 1.2 | 207 | 511 | 0.6 | omega, simp |
| 162 | Spec.Ty | 1.2 | 129 | 498 | 0.9 | decide/rfl kernel, omega, simp |
| 163 | Compiler.Opt.Arr | 1.1 | 212 | 516 | 0.5 | decide/rfl kernel, omega, simp |
| 164 | Compiler.Rec | 1.1 | 185 | 505 | 0.6 | omega, simp |
| 165 | Riscv.Steps.MemDebug | 1.1 | 44 | 1439 | 2.5 | defs/structural |
| 166 | Compiler.Opt.IR | 1.0 | 155 | 495 | 0.6 | omega |
| 167 | Compiler.Opt.Alloc | 1.0 | 194 | 487 | 0.5 | decide/rfl kernel, simp |
| 168 | Compiler.Opt.Hoist | 1.0 | 339 | 501 | 0.3 | decide/rfl kernel, omega, simp |
| 169 | Compiler.Stmt | 1.0 | 142 | 497 | 0.7 | decide/rfl kernel, omega, simp |
| 170 | Compiler.Frame | 0.9 | 184 | 485 | 0.5 | omega, simp |
| 171 | Compiler.Opt.Peep | 0.9 | 220 | 509 | 0.4 | decide/rfl kernel, simp |
| 172 | Compiler.Iface | 0.8 | 186 | 474 | 0.4 | defs/structural |
| 173 | Riscv.Direct.SortMergeList | 0.8 | 84 | 499 | 1.0 | omega, simp |
| 174 | Spec.Code | 0.7 | 105 | 474 | 0.7 | defs/structural |
| 175 | Compiler.Logic | 0.7 | 119 | 466 | 0.6 | omega, simp |
| 176 | Compiler.Mem | 0.7 | 112 | 475 | 0.6 | omega, simp |
| 177 | Spec.Encode | 0.7 | 104 | 480 | 0.7 | decide/rfl kernel, omega, simp |
| 178 | Spec.Tree | 0.7 | 83 | 484 | 0.8 | decide/rfl kernel, omega, simp |
| 179 | Compiler.BLang | 0.6 | 94 | 472 | 0.6 | defs/structural |
| 180 | Compiler.Call | 0.6 | 104 | 477 | 0.6 | decide/rfl kernel, omega |
| 181 | Riscv.Steps.Imm12 | 0.6 | 22 | 470 | 2.7 | decide/rfl kernel, omega, simp |
| 182 | Compiler.Opt.Fn | 0.6 | 152 | 491 | 0.4 | simp |
| 183 | Compiler.Opt.Color | 0.6 | 75 | 468 | 0.8 | decide/rfl kernel |
| 184 | Spec.ArrCode | 0.5 | 88 | 471 | 0.6 | omega |
| 185 | Compiler.CLang | 0.5 | 81 | 469 | 0.6 | defs/structural |
| 186 | Compiler.Opt.Exp | 0.5 | 64 | 484 | 0.8 | decide/rfl kernel, omega, simp |
| 187 | Compiler.Opt.Stmt | 0.5 | 69 | 486 | 0.7 | decide/rfl kernel, omega |
| 188 | Spec.Top | 0.4 | 94 | 462 | 0.4 | defs/structural |
| 189 | Compiler.AllocSpec | 0.4 | 93 | 460 | 0.4 | defs/structural |
| 190 | Compiler.MOp | 0.4 | 19 | 459 | 2.1 | defs/structural |
## 2. Critical path (the chain that bounds a fully parallel build): 731 s

Cumulative seconds in brackets. This is the longest path of the import graph weighted by the times above.

```
Spec.Riscv 8.1 [8] -> Steps.Regs 21.6 [30] -> Steps.Step 25.1 [55] -> Steps.WordsBase 1.2 -> Steps.Branch 8.8 [65]
 -> Steps.GenTac 15.9 [81] -> Steps.GenALU 73.5 [154] -> Steps.GenBranch 45.4 [200] -> Steps.GenMem 126.9 [327]
 -> Steps.Compat 4.4 -> Direct.Compiler 3.0 -> Direct.LoopRule 1.4 -> Direct.Loop 8.8 [344] -> Direct.Arr2Code 1.8
 -> Direct.Arr2Src 1.4 -> Frontx.Sub 2.4 -> Frontx.Tree 3.8 -> Frontx.Fast 7.1 [361] -> Frontx.Rep 2.6 -> Frontx.Exc 1.8
 -> Frontx.MulRep 2.1 -> Frontx.Translate 60.1 [427] -> Frontx.BookExamples 38.1 [465] -> Frontx.Machine 13.0
 -> Frontx.ScalarExamples 12.9 [491] -> Frontx.MulExamples 240.0 [731]
```

Three modules account for 427 s of the 731 s: `GenALU`, `GenBranch` and `GenMem` (246 s, a chain of three) and `MulExamples` (240 s). The chain `GenALU -> GenBranch -> GenMem` is not needed by the lemmas themselves. `GenBranch` uses only `encI_eq` and `enc_bits` from `GenALU`, and `GenMem` uses only `enc_bits` (transitively). Both are cheap lemmas at the top of `GenALU.lean`.

The next-longest paths are close: `PipeExamples -> BootEx` ends at 665 s, `TinySelf` at 578 s, `NameExamples` at 599 s. Splitting only the critical path moves the bottleneck, so the plan below covers all of them. Simulated results are in the last paragraph of section 3.

## 3. Split plans for the 10 slowest modules

Common technique: **keep the old module name as a file containing only `import`s of the new pieces**, so downstream imports and `Testing/scripts/axioms_*.lean` do not change. The lakefile uses globs, so new files are picked up automatically. Every plan needs a build and `check.sh` afterwards. Which lemma uses which name was read from the files but not compiled, so each import list below is a hypothesis for the first build to confirm.

Measured causes (from `-Dprofiler=true`, thresholds 0.5 s):

### 3.1 `Riscv.Examples.PipeExamples`: 261.6 s, 216 lines

Dominated by `interpretation`: 247 s of 261 s. Seven `compile%` calls take 30 to 65 s each, run through the interpreter at elaboration time. A `trace.profiler` run (threshold 15 s) gives the lines:

| def | s |
|---|--:|
| `mapsort` | 31 |
| `sort` | 30 |
| `sortdesc` | 33 |
| `mid` | 29 |
| `foldsorted` | 32 |
| `twosort` | 65 |
| `filtsort` | 31 |

Every other def is under 15 s. All seven use `mergeSort`; `simp` and the kernel are about 4 s in total. The defs are independent of each other and each imports only `Compiler.Front.PipeFront`.

- **Split:** `PipeSort1..7`, one per def above, each with its own `_ok` / `_mapped` theorem (`mapsort_ok`, `mapsort_mapped` go with `mapsort`; the `simp [mapsort, …]` and `decide` at lines 117 to 122 belong there). `PipeRest` holds the cheap defs, the `#guard_msgs` examples and the remaining theorems (about 10 s). `PipeExamples.lean` becomes the import aggregator, so `BootEx` is untouched.
- **Gain:** 262 s becomes about 66 s (`twosort` is the floor); total CPU unchanged. Splitting `twosort` further is not possible without changing its source.

### 3.2 `Riscv.Frontx.MulExamples`: 240 s, 62 lines, 3.7 GB (critical path)

Six `frontx_implementsC` commands. Each costs `interpretation` of a `_tmp` term of 47 to 52 s, plus `type checking` of 15 s, plus an "exec theorem" of 14 to 16 s. `translate + step proof` is under 1 s. Cumulative: interpretation 169 s, kernel type checking 57 s.

- **Split:** `MulOps64` (`ops64At/E`), `MulOps32`, `MulOpsN`, `MulGcd` (`frontx_compile Nat.gcd` and `gcdAt/E`). Each imports `ScalarExamples` and `Checked`, as now. `MulExamples.lean` becomes the aggregator. The `open` and `namespace` lines at lines 7 to 9 and 49 to 56 are repeated per file.
- **Gain:** 240 s becomes about 75 s (estimated from the per-command numbers: 55 / 70 / 75 / 45). This takes it off the critical path, which then ends at `TinySelf` (below).
- **Memory:** 3.7 GB per job now. The split pieces should each be smaller.

### 3.3 `Riscv.Frontx.TinySelf`: 129.6 s, 66 lines, 5.0 GB (the highest memory)

The command `frontx_compile tc.view` takes 48 s ("translate + step proof 48131 ms", 78 `simp` obligations of 1 to 3 s each). Then `frontx_implements_listC tinyCompile` costs 51 s of interpretation plus 24 s of type checking. These are a dependency chain (view, then compile, then entry), so a file split gives no parallelism.

- **Split (little gain):** `TinyView` (lines 1 to 38, the `tc` compile, about 50 s) and `TinyEntry` (lines 39 to 66, about 80 s). This only helps downstream modules, and nothing imports `TinySelf`. It is not worth doing unless it comes with a change to the command itself, e.g. checking the 78 obligations in parallel tasks inside `frontx_compile`. That would be a change to `Translate.lean` and is out of scope here.
- **Gain:** about 0 s on wall time through a file split. It becomes the end of the critical path after every other split (see "Result" below).

### 3.4 `Riscv.Steps.GenMem`: 126.9 s, 237 lines (critical path)

Eleven step lemmas (`step_lbu ld lb lh lhu lw lwu`, `step_sb sd sh sw`), each costing: `interpretation of SailEval.evalSailEval` 6 to 8.6 s, `instantiate metavars` about 1.2 s, kernel about 0.8 s. About 10 to 11 s per lemma and no shared work, so the lemmas are independent. Lines 1 to 176 (page lemmas `same_page_n`, `pageG`, `page8G..`, `encL/encS`, `encL_eq`, `encS_eq`, the macros `gmem_core`, `genm`) are shared and cheap.

- **Split:**
  - `GenMemBase` holds lines 1 to 176. Imports: `GenEnc` (see 3.5) and `MemStep`.
  - `GenLoad1` has `step_lbu, step_ld, step_lb`.
  - `GenLoad2` has `step_lh, step_lhu`.
  - `GenLoad3` has `step_lw, step_lwu`.
  - `GenStore1` has `step_sb, step_sd`.
  - `GenStore2` has `step_sh, step_sw`.
  - Each of those imports `GenMemBase`.
  - `GenMem.lean` becomes the aggregator, so `Compat` and `GenUse` are untouched.
- **Gain:** 127 s becomes about 34 s (6 s base plus 28 s). Another 12 s are saved because `GenMem` no longer waits for `GenBranch`.

### 3.5 `Riscv.Steps.GenALU`: 73.5 s, 128 lines (critical path)

About 20 step lemmas, each 1.2 to 3 s of `tactic execution of sailEvalStx` plus 0.5 s of kernel. `enc_bits`, `encR_eq`, `encI_eq`, `encSh_eq`, `encU_eq`, `bv_tb` and `genc` (lines 15 to 73) are cheap and are used by `GenBranch`, `GenMem` and `GenMul`.

- **Split:**
  - `GenEnc` holds lines 15 to 73 (the encodings and macros). It imports `GenTac`. About 3 s.
  - `GenALUR` has `step_add sub and or xor sll srl sra slt sltu` (R-type).
  - `GenALUI` has `step_addi andi ori xori slti sltiu` (I-type).
  - `GenALUSh` has `step_slli srli srai lui`.
  - Each imports `GenEnc`. `GenALU.lean` becomes the aggregator. `GenMul` can import `GenEnc` directly, since it uses only `genc`, `encR_eq` and `divu`.
- **Gain:** 73.5 s becomes about 3 s plus 25 s, and `GenALU` leaves the `GenBranch -> GenMem` chain entirely.

### 3.6 `Riscv.Steps.GenBranch`: 45.4 s, 83 lines (critical path)

Six branch pairs `*_t` / `*_n` (12 lemmas) plus `step_jal` and `step_jalr`. Each costs `tactic execution of sailEvalStx` of 1.4 to 2.4 s plus about 0.6 s of kernel.

- **Split:** `GenBranchB` (`beq bne blt bge bltu bgeu`, `_t` / `_n`) and `GenBranchJ` (`wJ_eq`, `jalr_eq`, `step_jal`, `step_jalr`), both importing `GenEnc`. If `GenBranchB` is still above 25 s, divide it into `beq/bne/blt` and `bge/bltu/bgeu`. The shared lemmas `wB_eq`, `slt_iff`, `ult_iff` and the `genb` macro (lines 15 to 41) go to a small `GenBranchBase`.
- **Gain:** 45 s becomes about 23 s, and it stops chaining behind `GenALU`.

### 3.7 `Riscv.Back.BootReset`: 72.5 s, 173 lines

Two `interpretation of SailEval.evalSailEval` calls take 23 s and 27 s (50 s of 72 s). The rest is `simp` (0.6 to 3.9 s each) and 4 s of kernel type checking. Which theorem owns each call was not determined; the likely candidates are `reset_ok` and `bootStart_ok`.

- **Split:** `BootDefs` (defs, `cb_*`, `tcs_*`, `vu_rep`, `presentRegs`, lines 1 to 122), then `BootInit` (`initBoard_ok`, `get_of_present`), `BootResetOk` (`reset_ok`) and `BootStart` (`bootStart_ok`, `bootStart_reset`), each importing `BootDefs`. `BootReset.lean` is the aggregator, so `BootV` is untouched.
- **Gain:** 72 s becomes about 5 s plus 30 s, about 35 s. This is off the critical path (`BootReset` ends at 486 s, but `BootV` adds only 22 s).

### 3.8 `Riscv.Frontx.NameExamples`: 61.7 s, 49 lines

Four `frontx_ind` commands plus two `frontx_ind_type` commands, each costing `simp` (1 to 2.3 s, many) plus 1 to 1.5 s of type checking.

- **Split:** `NameExName` (lines 12 to 37: `NameT`, `ConLeche.Name.beq`, `nameBEq`) and `NameExLevel` (lines 38 to 49: `LevelN ... nesting ConLeche.Name`, `ConLeche.Level.beq`, `levelBEq`), both importing `Ind2Examples`. The `BEq Name` and `Level` instances at lines 15 to 22 go in both files, or in a tiny `NameExBase`. It is not confirmed that `LevelN` does not need `NameT` (it nests `Name`); if it does, the gain is zero.
- **Gain:** 62 s becomes about 32 s. Nothing imports `NameExamples`.

### 3.9 `Riscv.Frontx.Translate`: 60.1 s, 3619 lines (critical path)

Mostly meta-programming code (the translator). Per the profile, `compilation (LCNF base)` takes 35 s (one definition takes 20.2 s, two more about 4 s each) and `elaboration` plus `typeclass inference` take about 20 s. No kernel proofs are involved.

- **First lever (no split):** find the 20 s definition (it follows an `elaboration took 2.84s`; a `trace.profiler` run with threshold 3 s gives its line) and break it into smaller `def`s. The code generator's cost is superlinear in the size of one definition. Expected gain: up to about 25 s on the critical path.
- **Split:** sections 2397 to 3085 (`Except` / `Option` normalisation) and 3086 to 3376 (list views, `frontx_spec`, general `match`) look independent of each other but both depend on lines 1 to 2396. A split into `TranslateCore` (1 to 2396), `TranslateExc` and `TranslateList` (parallel), and `TranslateEntry` (3445 to 3619, the entry points) gives a gain of about 10 to 15 s. The `mutual` block at line 420 must stay in one file.
- **Gain:** 60 s becomes about 35 s if both are done. This is uncertain: it depends on which `def`s are shared, and it was not tried.

### 3.10 `Riscv.Frontx.WaExp`: 45.9 s, 518 lines (not on the critical path)

`grind` takes 31.7 s cumulative (10 calls of 3 s each, all in `E.comp_ok` at line 410, which has `maxHeartbeats 1000000`); `grind canon` is 3.6 s of that. The kernel and `simp` are small.

- **Split:** `WaExpDef` (lines 1 to 141: defs, `Below`, `Rel.below`), `WaExpLoad` (142 to 305: `load_ok`, `getCode_ok`, `E.toB_ok`, `pureOr_ok`), `WaExpOps` (306 to 407: `r*_divM/modM`, `mword_ok`, `binS_ok`), and `WaExpComp` (`E.comp_ok`, which joins the others).
- **Gain:** about 46 s becomes about 8 + 24 s = 32 s. The `grind` cases inside `E.comp_ok` cannot be split without changing it into several lemmas, one per constructor of `E`. That would reduce the 24 s to about 10 s (10 cases at 3 s, with 4 cores).

### Result (simulation)

With the new file times from this section (the per-file figures are estimates from the profile numbers above, not builds) and the other 180 modules unchanged:

| | critical path | simulated wall, 4 workers | simulated wall, 8 workers | sum of module times |
|---|--:|--:|--:|--:|
| today | 731 s | 770 s | 731 s | 2181 s |
| all splits above | 369 s | 596 s | 386 s | 2228 s |

After the splits the critical path is `Spec.Riscv -> Regs -> Step -> Branch -> GenTac -> GenEnc -> GenMemBase -> GenLoad1 -> Compat -> Direct.* -> Frontx.* -> Translate -> ListExamples -> ListOutExamples -> TinySelf`, ending in `TinySelf` (130 s), which has no file-level split (3.3). With 4 workers the build is bound by CPU (2228 s of work / 4 = 557 s), not by the path, so on this box the gain is about 770 s to about 600 s (−22%). On 8 or more cores the gain is about 730 s to about 390 s (−47%). Each Lean process uses `--threads=2`, so on 4 cores two jobs already fill the machine in the heavy proof modules: the splits help most on boxes with more cores than that.

**Order of work by payoff on the critical path:** (1) `GenEnc` plus the `GenALU`/`GenBranch`/`GenMem` split (about −210 s on the path); (2) `MulExamples` (−165 s); (3) `PipeExamples` (−195 s, on the second-longest path); (4) `Translate`'s 20 s definition; (5) the rest.

## 4. `Testing/scripts/check.sh`: build vs axiom prints vs tests

Measured on this box with the build already done (so the build step is a no-op here):

| step | seconds | note |
|---|--:|---|
| `lake build Spec Compiler Riscv Arm Frontx` | 0.9 | up to date. From clean, the sum of module times is 2181 s serial, about 770 s with 4 workers (simulated). |
| `#print axioms`: 23 files `axioms_a..w.lean`, run one after the other | 338 | each is a `lake env lean` run that imports the whole library; per file 2.8 to 94 s, `axioms_m` = 93.6 s, `axioms_k` 18.7, `axioms_l` 16.3, `axioms_s` 30.8, `axioms_u` 21.8, `axioms_v` 30.6, `axioms_w` 21.0 |
| `wa_check.sh` (`axioms_wa.lean`) | 39 | |
| forbidden-word grep (`nocomment.py`) | 0.9 | |
| `spec_check.sh` | 0.02 | |
| `statement_check.sh` | 83 | exits 1 here ("a headline statement or a definition it depends on changed"); `check.sh` only prints a WARNING for it. Not investigated: it may be caused by this toolchain/checkout, or by the other agent's work. |
| `frontx_tests.sh` (QEMU/Sail tests) | not run | not part of `check.sh`. Fails immediately in this container (exit 127: `riscv64-linux-gnu-gcc` is missing), so there is no timing. |

Outside the build, `check.sh` takes 461 s: axioms 338 s (73%), `statement_check` 83 s (18%), `wa_check` 39 s (9%), the rest under 1 s. There are no tests in `check.sh`.

Ratio: from a clean tree the build is 2181 s serial (or about 770 s with 4 workers) against 461 s of checks, so the build is 83% of `check.sh` serial, or about 63% with a parallel build. With the build cached, 100% of the time is the axiom prints, `wa_check` and `statement_check`.

Cheap wins, none made here:
- The 23 axiom files are independent, so run them with `xargs -P4`: 338 s becomes about 94 s (`axioms_m` is the floor); then split `axioms_m`. Memory for 4 parallel processes was not checked.
- `wa_check.sh` and `statement_check.sh` can run in parallel with the axioms: 461 s becomes about 100 s.

## Reproduce

```
git show origin/build-cache:sail-riscv-lean.tar.zst > /tmp/s.tar.zst && mkdir -p ../deps && zstd -dc /tmp/s.tar.zst | tar xf - -C ../deps
lake build +Module          # one call per module, in import order; time each
lake env lean --tstack=400000 --threads=2 -Dprofiler=true -Dprofiler.threshold=500 Riscv/Steps/GenALU.lean
```
(`zstd` was not installed in the container; `pip install zstandard` and a short Python decompress loop was used instead.)

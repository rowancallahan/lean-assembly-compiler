# book_s2: the retry behind BOOK_S2.md

Same harness as `book_tries3/` (branch `booksurvey3`), run on the 98 blocked rows of the second third of the example files.
`ids.json`: declaration ids (from `extract.py` on fp-lean @0abeea5) of those rows. `results_s2.json`: per row, the front ends
tried and their messages. `run.py` is `python3 -I run.py "$(cat ids.json)"` with `BS3_ROOT` (fp-lean/, work/ = this repo,
decls.json), `LEAN_BIN` set. The higher-order (`frontx_hof`) and `frontx_implements` retries were done by hand in
`Riscv/Frontx/BookS2.lean`, not by this script.

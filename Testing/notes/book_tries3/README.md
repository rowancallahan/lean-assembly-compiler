# book_tries3: harness of BOOK_SURVEY3.md

Not part of the build. Needs: Lean 4.29.0 on `PATH` (`LEAN_BIN`), a copy of this repo with `lakefile.toml` unchanged and `../deps/sail-riscv-lean` built
(`lake build Riscv.Frontx.Translate Riscv.Frontx.RecCmd Riscv.Frontx.IndCmd Riscv.Frontx.WaCmd` once), `fp-lean` checked out at 0abeea5.

    BS3_ROOT=<dir with fp-lean/, work/ (the repo copy), old/Testing/notes/book_survey.csv (from booksurvey2), mainx/, runs/>
    export BS3_ROOT LEAN_BIN=<lean>/bin
    python3 -I extract.py $BS3_ROOT/fp-lean/examples $BS3_ROOT/decls.json          # book commands, file:line
    python3 -I extract.py <repo>/Riscv/Frontx $BS3_ROOT/mainx/decls.json           # main's examples
    J=4 TAG=all python3 -I run.py all                                              # one Lean run per (def, front end); ~15 min on 4 cores -> $BS3_ROOT/results_all.json
    python3 -I gt.py                                                               # book defs that equal a def of Riscv/Frontx/*.lean + its frontx_* command
    python3 -I survey3.py                                                          # statuses, blockers -> rows.json, anyc.json
    python3 -I final.py <out dir>                                                  # book_survey3.csv, BOOK_SURVEY3.part.md

`compiled/`: the generated Lean file of each of the 56 rows accepted by the default command (the def is verbatim after the `-- TARGET file:line-end` marker,
its book context before it); `lake env lean <file>` in the repo reproduces the accepted run (compiler success line after `@@MARK@@`).
`mainx/` etc. are generated and not committed.

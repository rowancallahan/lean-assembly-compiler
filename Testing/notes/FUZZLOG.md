# Fuzz log

One line per round of `Testing/scripts/fuzz_all.sh`: numbers are checked inputs / pairs (all agree unless the last column says otherwise).
Generators: `exp` = expressions (std RV64 + AArch64, 4-way), `fast` = expressions, unproved fast backends (4-way), `pipe` = random `Pipe`s
through `compileP`, `loop` = random terminating `Stmt` programs, `arr` = random `AStmt` programs with in-bounds loads/stores, `sort` = merge/insertion sort
machine code on adversarial inputs. Checks: Lean meaning == RV64 QEMU == Sail C emulator (== AArch64 QEMU for exp/fast).

| date (UTC) | commit | seed | exp | fast | pipe | loop | arr | sort | minutes | result |
|---|---|---|---|---|---|---|---|---|---|---|

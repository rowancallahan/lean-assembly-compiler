# nano onto the S3 calculus, one construct per link (branch nano-s3, 2026-11-17)

Goal (owner, ROADMAP "INTERPOLATE"): a second, S3-based back end for nano, proved by design: a chain of calculi,
each differing from the previous by ONE construct, each link a proved meaning-preservation lemma.

## Setup notes
- Branch base: origin/ir-s3 merged with origin/main and origin/nano-parse. Conflicts only in
  Testing/scripts/expected-axioms.txt (two appended blocks, both kept: ir-s3 then nano) and check.sh's axiom loop
  (ir-s3 placed before the nano-* files, matching that order).
- Toolchain: elan.lean-lang.org was DENIED by the network policy (403 at the proxy). Not routed around: the Lean
  4.29.0 release tarball was taken from releases.lean-lang.org (an allowed host), lean/lake symlinked into
  /usr/local/bin. Build cache restored per build-cache README (zstd).

## The chain
| link | calculus | the one construct | translation | theorem |
|---|---|---|---|---|
| L0 | nano `Ex` (`den`, `Prog.eval`) | — | — | — (spec) |
| L1 | `E1` (Nano/S3L1.lean) | no `call` (own environment) | `tr1`: call ↦ lets + `shift` args + `cut` body | `tr1_eval` |
| L2 | `A` (Nano/S3L2.lean) | operands are variables (ANF; add/sub/mul → `bin o i j`) | `tr2`: `a ⊕ b` ↦ `let x := a; let y := b↑; x ⊕ y` | `tr2_eval` |

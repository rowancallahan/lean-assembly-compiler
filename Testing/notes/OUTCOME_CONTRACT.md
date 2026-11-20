# Step 6 design: one outcome-indexed contract (ok / cap / room)

Read-only design against cleanup-pr1 d0b0917. Nothing implemented.

## Today
* Two semantics per node: `sv`/`st` (Option) and the kinded `svF`/`stF` (`Except Fail`, `Fail` = cap | room | stuck),
  tied by `oW (svF K fsX e) = sv K e` (`CapNode.ovS/otS/olS`).
* Success contracts over the Option semantics: `EVHwS`, `EVHtS`, `DefXS` (EVSDefs). Failure contracts over the kinded
  one, already generic in the kind: `CapW fk tg`, `CapT fk tg`, `CapD fk tg` (CapRun), `tg = stubW fk` (6 / 1).
  So there are two copies, not three: success, and failure-by-kind.
* Each composite failure rule takes the success contract of its prefix too (`pairCap (hA : EVHwS … (oW SA)) (cA : CapW …)
  (cB : CapW …)`), so the failure node induction `runVCap/TCap/LCap` (CapNode, 302 lines) re-derives every side
  condition of `runVS/TS/LS` (EVSRun, 254 lines) and calls it for prefixes. Same for `progCap` vs `progRunS` and
  `start_capX` vs `start_runX`.

## New contract
Over the kinded semantics only; the outcome is the semantics' own result, no separate index type:
```
structure EVO (KL C pc len p nl Inv G hb E0 R W w) (S : SemWX) : Prop where
  ok   : EVHwS KL C pc len p nl Inv hb E0 R W w (oW S)
  fail : ∀ fk, fk ≠ .stuck → CapW fk (stubW fk) KL C pc p nl Inv G hb E0 R S
```
and likewise `EVOt` (= `EVHtS (oT S)` + `CapT`) and `DefO` (= `DefXS (oD Sd)` + `CapD`). `EVHwS`/`CapW` stay as the
two projections, so every existing fragment lemma keeps its statement and proof.

Rejected: a single `run` field with `match S env sp H with | .ok … | .error fk …`. It forces all ~30 fragment proofs
(EVSComp/Tail/Loop/Call/Fin ≈ 1700 lines, CapRun 851) to be restated and re-proved; the proofs of the two halves
differ after the prefix (success continues, failure jumps), so little proof text would be shared.

## Mapping
| today | after |
|---|---|
| `pairXS` + `pairCap`, `ifXS` + `ifCap`, `letXS` + `letCap`, `loopXS` + `loopWCap`, `callXS` + `callCap`, `defXS` + `defCap`, `fin1..3` + `fin1..3Cap`, tail `valTS/contTS/ifTS'/letTS'` + `exitCap/contCap/ifTCap/letTCap` | one 3–5 line wrapper each: `pairO (a : EVO …) (b : EVO …) : EVO … := ⟨pairXS a.ok b.ok …, fun fk hk => pairCap a.ok (a.fail fk hk) (b.fail fk hk) …⟩` |
| leaves: `EVSLeaf` + `RoomRun.leafRoom/constRoom/…` + `noCap` | `leafO` wrappers (room from RoomRun, cap by `noCap`) |
| `RunCxS` + `CapCx` | one context: `RunCxS` + `defs : DefO`, `h6`, `kap`, `hb2k`, `C.length < 2^18` |
| `runVS/TS/LS` + `runVCap/TCap/LCap` | one `runVO/TO/LO : … → EVO/EVOt …` (one case per node kind, side conditions derived once) |
| `defRunS` + `defCapRun`, `progRunS` + `progCap`, `gen_defs_runS` + `gen_defs_cap` | `defRunO`, `progRunO` (one strong induction giving `DefO` for every def), `gen_defs_runO` |
| `start_runX` + `start_capX` | kept as two lemmas (different conclusions), both fed by main's `DefO` |

## Downstream statements
* `GenRunS.gen_runS`: statement unchanged (it already has the success conjunct and the `∀ fk ≠ stuck` conjunct);
  its proof calls `gen_defs_runO` once instead of `gen_defs_runS` + `gen_defs_cap`.
* `HostOk`, `HostOom`, `GenMain*`, Main: unchanged. REVIEW unchanged.
* Changed statements are internal only: the node/def/program theorems and the two contexts.

## Size and risk
| part | lines now | after | risk |
|---|---|---|---|
| EVO/EVOt/DefO + wrappers | 0 | +120 | low |
| EVSRun + CapNode | 556 | ≈ 380 | medium: the extra premise `h + lnV K e < C.length` of the Cap side becomes a premise of the merged theorem (already available at every call site of `runVS`); `runVCap`'s `cases fk` moves into the leaf wrappers |
| EVSProg + CapProg | 158 | ≈ 100 | low |
| StartAllS + CapStart, GenRunS | 231 | ≈ 215 | low |
Net ≈ −130 lines; the gain is structural: a new node kind = one success rule, one failure rule, one wrapper, ONE
induction case (today two cases in two files). No fixed-width or RISC-V assumption is added (stub words stay `stubW`).
Not in scope: merging the fragment proofs themselves (see Rejected); `Fail.stuck` stays excluded as today.

Order: (1) EVO defs + wrappers (additive, builds alone); (2) `runVO/TO/LO`, delete EVSRun's and CapNode's
inductions; (3) prog/start/GenRunS. Each step builds on its own. Depends on CL2's `…S` rename landing first (same
files).

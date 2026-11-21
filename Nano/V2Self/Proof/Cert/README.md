# Proof/Cert — the C-wide meaning certificate

Proves that the **source text of the compiler** (`Testing/nano/v2self/self_S_input.txt`, parsed once into the data
`PC.all : List DefA`) *means* the Lean function that the rest of the proof reasons about: `Cert.sem_C`
(a REVIEW theorem) says `Ref (Sem κC PC.all inp) (Sh.mLean inp)` for every `inp` shorter than 2^64 bytes, i.e. the
word-level meaning `Sem` (buffer capacity `κC = 524288`) of the parsed defs either hits the buffer capacity or equals
`Sh.mLean inp` (= `C.g41 …`, the Lean compiler). It is the link between "the self-hosted source text" and "the Lean
functions `C.*` that Gen/Machine/Main prove correct".

Where it sits: imports `Main/Sem` (`Sem`, `defMean`, `κC`), `Parser/ParSpec` (`DefA`, `Nd`) and `C/*` (the Lean defs).
Consumed by `REVIEW.lean`, `Main/SelfLink`, `SrcLink/Top`, `Tests/SelfIn*`. `CertArm/` repeats the pipeline for the
rv2arm translator with the same `Rules`/`Tac`.

## Files
* `Rules.lean` — hand-written. `Ref` (hit capacity or equal), `DenT/DenP/DenK` (node/arg-list/loop-tail denotes a Lean
  value, encoded by `Enc`), one rule per node kind, `loop_*`, `defMean_ref/den/loop`, `Good`.
* `Tac.lean` — hand-written. Tactics `den`, `den_unfold`, `den_let`, `den_call`: walk a `DenT` goal by node constructor
  and Lean value shape; calls use the generated `Cert.call_<i>`.
* `Asm.lean` — hand-written. `AllOk`, `means_all`, `sem_of_good`: assemble per-def certificates (each def sees the
  meanings before it).
* `OutSpec.lean` — hand-written. Word-level shadows `g40/g42/g41/m` of the output-building defs (`put ↦ bpush`,
  `[] ↦ bnew`) and `*_map`: their low bytes are the Lean defs.
* `PC.lean` — GENERATED: the reference parse `PC.b<i>`, `PC.d<i>`, `PC.all` (output of `dump_pc.lean`, pasted).
* `Specs.lean` — GENERATED: `Spec<i>` per def (refines `C.<name>`), `call_<i>` rules, `specs`.
* `Defs0..Defs43.lean` — GENERATED: `ok_<i>`, one proof per def by `den`, chunked by size (`o38`, `o39` alone: slow).
* `All.lean` — GENERATED: imports all, `all_ok`, and `sem_C`.

## Design decisions
* **Syntax-directed proof, generated.** One rule per node kind plus a tactic that applies them by the shape of the Lean
  value; per-def proofs are produced by `Testing/nano/v2self/cert/gen_cert.py`. Rejected: a general evaluator proof /
  `decide` on `Sem` (the defs are far too large; `Sem` is not computable to a closed value for arbitrary `inp`).
* **`Ref`, not equality.** `Sem` may stop at buffer capacity (Lean's `bpush`/`put` have none); the certificate says
  "capacity, or exactly the Lean value". The capacity case is excluded later by `SelfIn`.
* **Per-def specs with `Good`.** Def `k` is proved against specs of defs `< k` only (`Good specs ms k`), so the
  certificate follows the call order without a global induction over the program.
* **Output defs by hand-shadow.** `Sem` keeps whole words in the output buffer; `OutSpec` states the word-level
  versions and proves their byte images are the Lean defs.
* **Parse pasted, not proved.** `PC.all` is the dumped parse; that it is the parse of the source file is checked by
  the SrcLink stage, not here.

## Main results
`All.lean:sem_C` (assumes `inp.length < 2^64`; guarantees `Ref (Sem κC PC.all inp) (Sh.mLean inp)`),
`Asm.lean:means_all`, `Asm.lean:sem_of_good`, `Rules.lean:defMean_den`, `OutSpec.lean:m_map`.

## Build / check
`lake build Nano.V2Self.Proof.Cert.All` (Defs* are heavy: `Defs40` OOMs at 4 parallel jobs; build with 2).
Regenerate: `lake env lean --run Testing/nano/v2self/cert/dump_pc.lean Testing/nano/v2self/self_S_input.txt > pc.txt;
python3 Testing/nano/v2self/cert/gen_cert.py pc.txt` (never hand-edit `PC/Specs/Defs*/All`).
`Testing/scripts/review_axioms.sh` pins the axioms of `sem_C`.

## Known limits
* The generated files are not shortened here; dedupe belongs in `gen_cert.py` (e.g. repeated `den_unfold; den` tails).
* `gen_cert.py`'s docstring still mentions a hand-written `Cert/Out.lean`; it is now `OutSpec.lean`.

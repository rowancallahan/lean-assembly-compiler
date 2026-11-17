# Archived nano modules (not built by `lake build Nano`; branch nano-final, NANO_CLOSE.md section F)

* `InlPSelf.lean` (close B, paged inliner): cannot compile — its loop bodies exceed the conditional-branch range
  `Wide.wf` checks (4187 words with every local spilled), so no register choice passes `optB`.
* `ElabBVSelf.lean`, `ElabBESelf.lean` (close A, lexer halves through frontx listCS, 57+ min builds),
  `SelfHostedA.lean` (six-stage composition over them), `SelfHostS3.lean` (seven-stage composition with stage 2a as a
  hypothesis): superseded by `Nano/LexS3*.lean` (stage 1 + parser 2a as ONE S3 stage) and `Nano/SelfHostFinal.lean`
  (`Nano.selfHosted`).
* `InlQ.lean`, `InlR*.lean` (nano-final, inliner as P/Q/W stages; `Nano.IR.inlR_eq` proved): superseded by the S3
  inliner `Nano.IS.inlS3_implements` (every input, no fits condition).
To build one again, move it back under `Nano/` (imports unchanged).

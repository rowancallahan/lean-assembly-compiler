# Notice and acknowledgements

Copyright 2026 the lean-assembly-compiler authors.

Licensed under the Apache License, Version 2.0 (see LICENSE). Distributed on an "AS IS" BASIS, WITHOUT WARRANTIES
OR CONDITIONS OF ANY KIND. Third-party code included or compiled verbatim keeps its own licence (below).

## Inspiration (no code copied unless stated in the file itself)

- **CompCert** (INRIA and AbsInt Angewandte Informatik GmbH; INRIA Non-Commercial License Agreement, some files
  LGPL 2.1+): the design of the shared IR (RTL/LTL/Linear-style levels, simulation proofs per pass, translation
  validation of register allocation) and other proof strategies are inspired by CompCert. https://compcert.org
- **Certora/clean** (CompCert fork with a Lean 4 Clight semantics; non-commercial): studied for its Lean port of
  the Clight semantics and program logic. https://github.com/Certora/clean

## Trusted base

Only the Sail RISC-V and ARM models (and the Lean kernel) are trusted; CompCert's proofs and models are not
part of the trusted base.

## Third-party code used or compiled verbatim

Library and book code compiled verbatim carries its provenance (file:line@rev) in the file it is copied into;
see each source's own licence: fp-lean (Functional Programming in Lean), lean-zip, lean-svg, con-leche, Lean core,
the Sail-generated RISC-V and ARM models, DeepMind's AArch64 model (Apache-2.0).

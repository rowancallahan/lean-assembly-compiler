# NANO_ELAB: `nanoElab` as byte-level stages for the front end (branch `nano-elab`)

Owner task: `nanoElabB` = `nanoElab` as byte-level state machine(s) the front end accepts, proved equal for ALL inputs,
compiled with machine theorems, tested on QEMU + Sail. Files `Nano/ElabB*.lean`.

## Decisions / log
* Spec = `nanoElab` of `nano-int` (name shape + reserved list, CR only before LF, glued numerals rejected). nano-e2e
  has a different lexer (`wordTok`, `adjOk`, column-0 rule); when it reaches nano-int the stage-1 machine must follow.

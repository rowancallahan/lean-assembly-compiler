/- **`A64Sem armDM XD WD`**: the abstract AArch64 interface of the ARM adapter, instantiated on DeepMind's model
(`armDM`; `XD` executable bytes, `WD` readable+writable bytes). Every field is proved from the `dm_*` lemmas except
`perm_init`, which is a HYPOTHESIS: Spec's `StartCorrect` constrains only what `observe` shows, and DeepMind's
permissions are not observable (W^X: no byte is both executable and writable), so "the loader mapped the code r-x
and the data blocks rw-" cannot follow from it.
WARNING: `PermInit` quantifies over ALL `StartCorrect` states, and some of them map the code non-executable, so
`PermInit` is FALSE for `armDM` and `a64DM` must not be composed as is: it shows that every per-form field of
`A64Sem` holds on DeepMind exactly as stated. The usable form needs `perm_init` as a per-start-state premise of the
ARM top theorem (sent to E): the loader's r-x / rw- layout is an assumption about the start state on a W^X model. -/
import Blocks.A64DM
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open Proven.Top

/-- the loader's permission layout at a call's start (the `perm_init` field of `A64Sem`) -/
def PermInit : Prop :=
  ∀ (s : armDM.State) (call : Call) (code x : List UInt8), StartCorrect armDM s call code x →
    (∀ a, (armDM.observe s).programCounter.toNat ≤ a → a < (armDM.observe s).programCounter.toNat + code.length → XD s a) ∧
    (∀ a, JT.InBlocks call a → WD s a)

theorem a64DM (hinit : PermInit) : JT.A64Sem armDM XD WD where
  map := rfl
  ram := by decide
  perm_init := hinit
  movz s d i hc hp hx hd hi hw := F_movz s d i hc hp hx hd hi hw
  movk s d i h hc hp hx hd hi hh hw := F_movk s d i h hc hp hx hd hi hh hw
  addi s d n i hc hp hx hd hn hi hw := F_addi s d n i hc hp hx hd hn hi hw
  subi s d n i hc hp hx hd hn hi hw := F_subi s d n i hc hp hx hd hn hi hw
  alu s op d n m hc hp hx h1 h2 hd hn hm hw := F_alu s op d n m hc hp hx h1 h2 hd hn hm hw
  cmpbr s c n m f hc hp hx hc4 hn hm hf1 hf2 h8 hw0 hw1 := F_cmpbr s c n m f hc hp hx hc4 hn hm hf1 hf2 h8 hw0 hw1
  cbz s r f hc hp hx hr hf1 hf2 hw := F_cbz s r f hc hp hx hr hf1 hf2 hw
  b s f hc hp hx hf1 hf2 hw := F_b s f hc hp hx hf1 hf2 hw
  bl s f hc hp hx hf1 hf2 hw := F_bl s f hc hp hx hf1 hf2 hw
  br s n hc hp hx hn hw := F_br s n hc hp hx hn hw
  ldr s r n f v hc hp hx hr hn hf8 hf hl hal hlo hhi hW hv hw := F_ldr s r n f v hc hp hx hr hn hf8 hf hl hal hlo hhi hW hv hw
  str s r n f hc hp hx hr hn hf8 hf hl hal hlo hhi hW hw := F_str s r n f hc hp hx hr hn hf8 hf hl hal hlo hhi hW hw
  ldrb s r n f b hc hp hx hr hn hf hl hlo hhi hW hv hw := F_ldrb s r n f b hc hp hx hr hn hf hl hlo hhi hW hv hw
  strb s r n f hc hp hx hr hn hf hl hlo hhi hW hw := F_strb s r n f hc hp hx hr hn hf hl hlo hhi hW hw

end Proven.Apc.Blocks

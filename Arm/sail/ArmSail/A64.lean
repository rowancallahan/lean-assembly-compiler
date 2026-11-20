/- **`A64Sem armSail TT TT`**: the abstract AArch64 interface of the ARM adapter
(`Nano/V2Self/Proof/Machine/A64Sem.lean`) on the official Sail ARM model (`armSail`). Sail does not model page
permissions here (MMU off, EL3), so both permission predicates are `True` and the loader contract `ArmLoader TT TT`
holds for every start state. Every field from the Sail `full_*` lemmas (`Fields.lean`). -/
import ArmSail.Fields
set_option linter.unusedVariables false
namespace ArmSail
open Proven.Top

theorem a64Sail : JT.A64Sem armSail TT TT where
  map := rfl
  ram := by decide
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

end ArmSail

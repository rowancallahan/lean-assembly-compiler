/- Specification: what it means for RV64 machine code to implement a function, on the Sail model. -/
import LeanRV64D
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven

abbrev St := SequentialState RegisterType trivialChoiceSource

/-- The control state we fix (Sail reset values): M-mode, hart active, `mstatus.MIE = 0` (no
interrupts), PMP entries off, `mseccfg = 0`, no HTIF, one PMA region = RAM `[0x80000000, 0x100000000)` (rwx),
instret counting on, no landing pad pending.  Everything else is arbitrary but must be present. -/
structure Cfg (s : St) : Prop where
  priv : s.regs.get? .cur_privilege = some .Machine
  hart : s.regs.get? .hart_state = some (.HART_ACTIVE ())
  misa : s.regs.get? .misa = some 0x800000000014112F#64
  mstatus : s.regs.get? .mstatus = some 0x0000000A00000000#64
  mcountinhibit : s.regs.get? .mcountinhibit = some 0#32
  minstretcfg : s.regs.get? .minstretcfg = some 0#64
  pmpcfg : s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0#8)
  htif : s.regs.get? .htif_tohost_base = some none
  elp : s.regs.get? .elp = some 0#1
  mseccfg : s.regs.get? .mseccfg = some 0#64
  pma : ∃ a b, s.regs.get? .pma_regions = some [⟨0x80000000#64, 0x80000000#64, a, b⟩] ∧
    a.executable ∧ a.readable ∧ a.writable
  present : ∀ r ∈ [Register.mideleg, .mip, .mie, .sig_meip, .sig_seip, .pmpaddr_n, .minstret, .PC,
    .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31],
    s.regs.contains r

/-- One instruction retires: `try_step` finishes normally and the hart's step result was
`Retire_Success` (no trap, no model error).  `run_hart_active` never reads `minstret_increment`,
the only register `try_step` writes before calling it, so running it on `s` gives the same result. -/
def Retires (s s' : St) : Prop :=
  (∃ w s₁, run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), w)) s₁) ∧
  try_step 0 false s = .ok false s'

def Steps : Nat → St → St → Prop
  | 0, s, s' => s' = s
  | n + 1, s, s' => ∃ s₁, Retires s s₁ ∧ Steps n s₁ s'

def runsTo (s : St) (P : St → Prop) : Prop := ∃ n s', Steps n s s' ∧ P s'

def reg (s : St) (r : Register) : Option (RegisterType r) := s.regs.get? r

def bytesAt (s : St) (a n : Nat) : List (Option (BitVec 8)) := (List.range n).map (s.mem[a + ·]?)

structure Region where
  base : Nat
  len : Nat

def Region.inRAM (r : Region) : Prop := 0x80000000 ≤ r.base ∧ r.base + r.len ≤ 0x100000000
def disjoint (r₁ r₂ : Region) : Prop := r₁.base + r₁.len ≤ r₂.base ∨ r₂.base + r₂.len ≤ r₁.base

def unchangedOutside (s s' : St) (rs : List Region) : Prop :=
  ∀ a, (∀ r ∈ rs, a < r.base ∨ r.base + r.len ≤ a) → s'.mem[a]? = s.mem[a]?

def calleeSavedKept (s s' : St) : Prop :=
  ∀ r ∈ [Register.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    s'.regs.get? r = s.regs.get? r

end Proven

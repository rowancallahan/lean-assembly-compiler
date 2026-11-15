/- The bare-metal start state: the Sail model's own power-on (`sail_model_init`), the board config
(`board`: reset vector at the RAM base, only the default config's main-memory PMA region), then the model's
`reset`.  `reset` calls the declared axiom `cancel_reservation` (no Lean body), so it is taken as the
parameter `cancel` of a verbatim copy (`reset_eq`); the start needs only that it leaves the state alone.
Result (`bootStart_ok`): `Cfg` except `misa.V` (set by the model's reset; the stub clears it), PC at the RAM
base, memory the loaded image. -/
import Riscv.Back.Top
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Proven.Boot
open Register Privilege HartState extension MemoryRegionType

noncomputable section

/-- `reset_sys` (`SysControl.lean`) with the reservation hook `cancel` as a parameter -/
def resetSysWith (cancel : SailM Unit) : SailM Unit := do
  writeReg cur_privilege Machine
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3 0#1)
  writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
  (reset_tvecs ())
  (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
  (reset_misa ())
  cancel
  writeReg PC (← readReg pc_reset_address)
  writeReg nextPC (← readReg pc_reset_address)
  writeReg mcause (zeros (n := 64))
  (csr_name_write_callback "mcause" (← readReg mcause))
  (reset_pmp ())
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 9 9
    (bool_to_bit (false : Bool)))
  writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 8 8
    (bool_to_bit (false : Bool)))
  if ((hartSupports Ext_Zicfilp) : Bool)
  then writeReg mseccfg (Sail.BitVec.updateSubrange (← readReg mseccfg) 10 10 0#1)
  else (pure ())
  (reset_stateen ())
  writeReg vstart (zeros (n := 64))
  writeReg vl (zeros (n := 64))
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 2 1 0b00#2)
  writeReg vcsr (Sail.BitVec.updateSubrange (← readReg vcsr) 0 0 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 1) (64 -i 1) 1#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) (64 -i 2) 8
    (zeros (n := (64 -i 9))))
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 7 7 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 6 6 0#1)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 5 3 0b000#3)
  writeReg vtype (Sail.BitVec.updateSubrange (← readReg vtype) 2 0 0b000#3)

/-- `reset` (`Model.lean`) with the reservation hook as a parameter -/
def resetWith (cancel : SailM Unit) : SailM Unit := do
  writeReg hart_state (HART_ACTIVE ())
  (resetSysWith cancel)
  (reset_vmem ())
  (reset_elp ())
  (pure (ext_reset ()))

/-- the copy is the model's `reset` -/
theorem reset_eq : reset () = resetWith (cancel_reservation ()) := rfl

/-- **board config**: reset vector at the RAM base; of the default config's PMA regions only main memory
(no boot ROM, no CLINT) -/
def board : SailM Unit := do
  set_pc_reset_address 0x80000000#64
  writeReg pma_regions ((← readReg pma_regions).filter (·.attributes.mem_type == MainMemory))

/-- power-on: the model's register init, then the board config -/
def initBoard : SailM Unit := do
  sail_model_init ()
  board

/-- **the bare-metal start**: power-on and reset from the default state with memory `image` -/
def bootStart (cancel : SailM Unit) (image : Std.ExtHashMap Nat (BitVec 8)) : St :=
  match (do initBoard; resetWith cancel) { (default : St) with mem := image } with
  | .ok _ s => s
  | .error _ s => s

/-! ## `misa` -/

/-- `misa` after the model's reset (`V` set) -/
def vMisa : BitVec 64 := 0x800000000034112F#64
/-- `misa` as `Cfg` fixes it (`V` clear) -/
def cfgMisa : BitVec 64 := 0x800000000014112F#64

def unV (s : St) : St := { s with regs := s.regs.insert .misa cfgMisa }

/-- `Cfg` up to `misa.V` -/
def CfgV (s : St) : Prop := Cfg (unV s) ∧ s.regs.get? .misa = some vMisa

/-! ## Evaluation -/

theorem cb_mstatus (v : BitVec 64) (s : St) : csr_name_write_callback "mstatus" v s = .ok () s := rfl
theorem cb_mcause (v : BitVec 64) (s : St) : csr_name_write_callback "mcause" v s = .ok () s := rfl
theorem cb_misa (v : BitVec 64) (s : St) : csr_name_write_callback "misa" v s = .ok () s := rfl
@[simp] theorem tcs_next (p x) : trivialChoiceSource.nextState p x = () := rfl
@[simp] theorem tcs_bv (n x) : trivialChoiceSource.choose (.bitvector n) x = (0 : BitVec n) := rfl

theorem vu_rep {α} {n : Nat} (a : α) (i : Nat) :
    vectorUpdate (Vector.replicate n a) i a = Vector.replicate n a := by
  apply Vector.ext; intro j hj; simp [vectorUpdate, Vector.set!]

/-- registers `reset` reads (or `Cfg` asks for) that power-on leaves present -/
def presentRegs : List Register := [.mtvec, .stvec, .vcsr, .vtype, .mideleg, .mip, .mie, .sig_meip, .sig_seip,
  .pmpaddr_n, .minstret, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
  .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- what power-on leaves -/
structure PowerOn (s : St) : Prop where
  mstatus : s.regs.get? .mstatus = some 0x0000000A00000000#64
  misa : s.regs.get? .misa = some 0x8000000000000000#64
  reset : s.regs.get? .pc_reset_address = some 0x80000000#64
  pmpcfg : s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0#8)
  mseccfg : s.regs.get? .mseccfg = some 0#64
  mcountinhibit : s.regs.get? .mcountinhibit = some 0#32
  minstretcfg : s.regs.get? .minstretcfg = some 0#64
  htif : s.regs.get? .htif_tohost_base = some none
  pma : ∃ a b, s.regs.get? .pma_regions = some [⟨0x80000000#64, 0x80000000#64, a, b⟩] ∧
    a.executable ∧ a.readable ∧ a.writable
  present : ∀ r ∈ presentRegs, s.regs.contains r

theorem initBoard_ok (s0 : St) : ∃ s, initBoard s0 = .ok () s ∧ s.mem = s0.mem ∧ PowerOn s := by
  refine ⟨?s, ?h, ?g⟩
  case h => sail_eval [initBoard, board]
  case g =>
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) [presentRegs, Std.ExtDHashMap.get?_insert,
        Std.ExtDHashMap.contains_insert]

theorem get_of_present {s : St} {r : Register} (h : s.regs.contains r) : ∃ v, s.regs.get? r = some v :=
  Option.isSome_iff_exists.mp (by rwa [Std.ExtDHashMap.contains_eq_isSome_get?] at h)

theorem reset_ok (s : St) (h : PowerOn s) :
    ∃ s', resetWith (pure ()) s = .ok () s' ∧ s'.mem = s.mem ∧ CfgV s' ∧
      s'.regs.get? .PC = some 0x80000000#64 := by
  have hp := h.present
  simp only [presentRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
  obtain ⟨_, h1⟩ := get_of_present hp.1
  obtain ⟨_, h2⟩ := get_of_present hp.2.1
  obtain ⟨_, h3⟩ := get_of_present hp.2.2.1
  obtain ⟨_, h4⟩ := get_of_present hp.2.2.2.1
  obtain ⟨a, b, hpma, ha⟩ := h.pma
  have hm := hp
  simp only [← Std.ExtDHashMap.mem_iff_contains] at hm
  refine ⟨?s, ?h, ?g⟩
  case h =>
    sail_eval [cb_mstatus, cb_mcause, cb_misa, h.mstatus, h.misa, h.reset, h.pmpcfg, h.mseccfg, h1, h2, h3, h4]
  case g =>
    refine ⟨rfl, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨a, b, ?_, ha⟩, ?_⟩, ?_⟩, ?_⟩
    all_goals simp (config := { decide := true }) [unV, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.contains_insert,
      vu_rep, h.mcountinhibit, h.minstretcfg, h.htif, hpma, cfgMisa, vMisa, hm]

/-- **the start state**, with the reservation hook a no-op: `Cfg` up to `misa.V`, PC at the RAM base,
memory the image -/
theorem bootStart_ok (image : Std.ExtHashMap Nat (BitVec 8)) :
    CfgV (bootStart (pure ()) image) ∧ (bootStart (pure ()) image).regs.get? .PC = some 0x80000000#64 ∧
      (bootStart (pure ()) image).mem = image := by
  obtain ⟨s1, h1, hm1, hp1⟩ := initBoard_ok { (default : St) with mem := image }
  obtain ⟨s2, h2, hm2, hc2, hpc2⟩ := reset_ok s1 hp1
  have e : (do initBoard; resetWith (pure ()) : SailM Unit) { (default : St) with mem := image } = .ok () s2 := by
    show (initBoard >>= fun _ => resetWith (pure ())) _ = _
    rw [SailEval.bind_ok _ h1]; exact h2
  unfold bootStart; rw [e]; exact ⟨hc2, hpc2, hm2.trans hm1⟩

/-- with the model's own `cancel_reservation`, if it leaves the state alone -/
theorem bootStart_reset (hcancel : ∀ s : St, cancel_reservation () s = .ok () s) (image) :
    bootStart (cancel_reservation ()) image = bootStart (pure ()) image := by
  have : cancel_reservation () = (pure () : SailM Unit) := funext hcancel
  rw [this]

end
end Proven.Boot

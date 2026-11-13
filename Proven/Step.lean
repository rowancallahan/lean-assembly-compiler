/- Step lemmas for the Sail RV64 model under `Cfg`. -/
import Proven.Regs
import Proven.SailEval
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven

/-! ## Normal forms used by `sail_eval` -/

@[simp] theorem bits_of_virtaddr_mk (x : BitVec 64) : bits_of_virtaddr (.Virtaddr x) = x := rfl
@[simp] theorem bits_of_physaddr_mk (x : BitVec 64) : bits_of_physaddr (.Physaddr x) = x := rfl
@[simp] theorem toNatInt_eq {w} (x : BitVec w) : Sail.BitVec.toNatInt x = (x.toNat : Int) := rfl
@[simp] theorem addInt_zero {w} (x : BitVec w) : BitVec.addInt x 0 = x := by simp [BitVec.addInt]
@[simp] theorem zero_extend_64 (x : BitVec 64) : zero_extend (m := 64) x = x := by
  simp [zero_extend, Sail.BitVec.zeroExtend]
@[simp] theorem regval_from_reg_eq (v : BitVec 64) : regval_from_reg v = v := rfl
@[simp] theorem regval_into_reg_eq (v : BitVec 64) : regval_into_reg v = v := rfl
@[simp] theorem addInt_eq {w} (x : BitVec w) (i : Int) : BitVec.addInt x i = x + BitVec.ofInt w i := rfl
@[simp] theorem upd_full (x : BitVec 32) : Sail.BitVec.updateSubrange (0#32) 31 0 x = x := by
  ext i hi; simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

@[simp] theorem upd_full8 (x : BitVec 8) : Sail.BitVec.updateSubrange (0#8) 7 0 x = x := by
  ext i hi; simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
@[simp] theorem extend_value_true {k} (x : BitVec k) : extend_value true x = x.setWidth 64 := by
  simp [extend_value, zero_extend, Sail.BitVec.zeroExtend]
@[simp] theorem extractLsb_zero {n} (x : BitVec n) (hi : Nat) :
    Sail.BitVec.extractLsb x hi 0 = x.setWidth (hi + 1) := by
  ext i hi'; simp [Sail.BitVec.extractLsb]
@[simp] theorem insert_insert_same {m : Regs} {r : Register} {v w : RegisterType r} :
    (m.insert r v).insert r w = m.insert r w := by
  ext k; simp only [Std.ExtDHashMap.get?_insert]; split <;> rfl
@[simp] theorem shift_bits_left_eq {n m} (x : BitVec n) (y : BitVec m) :
    shift_bits_left x y = x <<< y.toNat := rfl
/-- big constants (negative offsets) as subtraction: keeps `BitVec` literals `< 2^(w-1)`.  (The
kernel hits "deep recursion" checking some `simp` proofs about `x + c#64` with `c ≥ 2^63`.) -/
@[simp] theorem add_big {w : Nat} (x : BitVec w) (n : Nat) (h : 2 ^ w < 2 * n ∧ n < 2 ^ w) :
    x + BitVec.ofNat w n = x - BitVec.ofNat w (2 ^ w - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h.2, Nat.mod_eq_of_lt (by omega : 2 ^ w - n < 2 ^ w)]
  congr 1; omega
@[simp] theorem subInt_eq {w} (x : BitVec w) (i : Int) : BitVec.subInt x i = x - BitVec.ofInt w i := rfl
@[simp] theorem not_eq (b : Bool) : Functions.not b = !b := rfl
@[simp] theorem pm_transform_PA_0 (x : BitVec 64) : pm_transform_PA (.Virtaddr x) 0 = .Virtaddr x := by
  simp [pm_transform_PA, zero_extend, Sail.BitVec.extractLsb, Sail.BitVec.zeroExtend, Functions.xlen]
  ext i hi; simp [BitVec.getLsbD_eq_getElem (by omega : i < 64)]
@[simp] theorem aligned_v1 (x : BitVec 64) : is_aligned_vaddr (.Virtaddr x) 1 = true := by
  simp [is_aligned_vaddr]
@[simp] theorem aligned_p1 (x : BitVec 64) : is_aligned_paddr (.Physaddr x) 1 = true := by
  simp [is_aligned_paddr]

@[simp] theorem access_update0 (x : BitVec 64) : Sail.BitVec.access (Sail.BitVec.update x 0 0#1) 0 = 0#1 := by
  simp [Sail.BitVec.access, Sail.BitVec.update, Sail.BitVec.updateSubrange']
@[simp low] theorem access0_iff (x : BitVec 64) : (Sail.BitVec.access x 0 = 0#1) ↔ x.toNat % 2 = 0 := by
  simp [Sail.BitVec.access, BitVec.getElem_eq_testBit_toNat, Nat.testBit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> simp [h]
theorem update0_even (x : BitVec 64) (h : x.toNat % 2 = 0) : Sail.BitVec.update x 0 0#1 = x := by
  have : ∀ j < 63, (18446744073709551614#64).getLsbD (j+1) = true := by decide
  ext i hi
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
  intro hx
  rcases i with _ | i
  · rw [BitVec.getElem_eq_testBit_toNat] at hx; simp [Nat.testBit, h] at hx
  · rw [← BitVec.getLsbD_eq_getElem]; exact this i (by omega)

/-! ## Address side conditions from plain arithmetic -/

theorem access0 {pc : BitVec 64} (h : pc.toNat % 4 = 0) : Sail.BitVec.access pc 0 = 0#1 := by
  have : pc[0] = false := by rw [BitVec.getElem_eq_testBit_toNat]; simp [Nat.testBit]; omega
  simp [Sail.BitVec.access, this]

theorem aligned_v {pc : BitVec 64} (h : pc.toNat % 4 = 0) : is_aligned_vaddr (.Virtaddr pc) 4 = true := by
  simp [is_aligned_vaddr, toNatInt_eq, Int.tmod_eq_emod]; omega

theorem aligned_p {pc : BitVec 64} (h : pc.toNat % 4 = 0) : is_aligned_paddr (.Physaddr pc) 4 = true := by
  simp [is_aligned_paddr, toNatInt_eq, Int.tmod_eq_emod]; omega

theorem in_ram {a : BitVec 64} {n : Nat} (hn : n < 2 ^ 12) (lo : 0x80000000 ≤ a.toNat)
    (hi : a.toNat + n ≤ 0x100000000) :
    range_subset a (BitVec.ofNat 64 n) 0x80000000#64 0x80000000#64 = true := by
  simp [range_subset, zopz0zIzJ_u, toNatInt_eq, BitVec.toNat_sub, BitVec.toNat_add]; omega

/-! ## `Cfg` bookkeeping -/

def ctrlRegs : List Register := [.cur_privilege, .hart_state, .misa, .mstatus, .mcountinhibit,
  .minstretcfg, .pmpcfg_n, .htif_tohost_base, .elp, .mseccfg, .pma_regions]

theorem Cfg.get {s : St} (h : Cfg s) {r : Register} (hr : r ∈ [Register.mideleg, .mip, .mie, .sig_meip,
    .sig_seip, .pmpaddr_n, .minstret, .PC, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11,
    .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27,
    .x28, .x29, .x30, .x31]) : ∃ v, s.regs.get? r = some v := by
  have := h.present r hr
  rw [Std.ExtDHashMap.contains_eq_isSome_get?] at this
  exact Option.isSome_iff_exists.mp this

theorem Cfg.insert {s : St} (h : Cfg s) {r : Register} {v} (hr : r ∉ ctrlRegs) :
    Cfg { s with regs := s.regs.insert r v } := by
  simp only [ctrlRegs, List.mem_cons, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hr
  obtain ⟨a, b, hp, hx⟩ := h.pma
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨a, b, ?_, hx⟩,
    fun r' hr' => by simp [Std.ExtDHashMap.contains_insert, h.present r' hr']⟩ <;>
    simp [Std.ExtDHashMap.get?_insert, *, h.priv, h.hart, h.misa,
      h.mstatus, h.mcountinhibit, h.minstretcfg, h.pmpcfg, h.htif, h.elp, h.mseccfg]

theorem Cfg.setMem {s : St} (h : Cfg s) (m) : Cfg { s with mem := m } :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12⟩

theorem Cfg.x1 {s : St} (h : Cfg s) : s.regs.get? .x1 = some (getX s 1) := by
  obtain ⟨v, hv⟩ := h.get (r := .x1) (by simp); simp [xval, hv]
theorem Cfg.x2 {s : St} (h : Cfg s) : s.regs.get? .x2 = some (getX s 2) := by
  obtain ⟨v, hv⟩ := h.get (r := .x2) (by simp); simp [xval, hv]
theorem Cfg.x3 {s : St} (h : Cfg s) : s.regs.get? .x3 = some (getX s 3) := by
  obtain ⟨v, hv⟩ := h.get (r := .x3) (by simp); simp [xval, hv]
theorem Cfg.x4 {s : St} (h : Cfg s) : s.regs.get? .x4 = some (getX s 4) := by
  obtain ⟨v, hv⟩ := h.get (r := .x4) (by simp); simp [xval, hv]
theorem Cfg.x5 {s : St} (h : Cfg s) : s.regs.get? .x5 = some (getX s 5) := by
  obtain ⟨v, hv⟩ := h.get (r := .x5) (by simp); simp [xval, hv]
theorem Cfg.x6 {s : St} (h : Cfg s) : s.regs.get? .x6 = some (getX s 6) := by
  obtain ⟨v, hv⟩ := h.get (r := .x6) (by simp); simp [xval, hv]
theorem Cfg.x7 {s : St} (h : Cfg s) : s.regs.get? .x7 = some (getX s 7) := by
  obtain ⟨v, hv⟩ := h.get (r := .x7) (by simp); simp [xval, hv]
theorem Cfg.x8 {s : St} (h : Cfg s) : s.regs.get? .x8 = some (getX s 8) := by
  obtain ⟨v, hv⟩ := h.get (r := .x8) (by simp); simp [xval, hv]
theorem Cfg.x9 {s : St} (h : Cfg s) : s.regs.get? .x9 = some (getX s 9) := by
  obtain ⟨v, hv⟩ := h.get (r := .x9) (by simp); simp [xval, hv]
theorem Cfg.x10 {s : St} (h : Cfg s) : s.regs.get? .x10 = some (getX s 10) := by
  obtain ⟨v, hv⟩ := h.get (r := .x10) (by simp); simp [xval, hv]
theorem Cfg.x11 {s : St} (h : Cfg s) : s.regs.get? .x11 = some (getX s 11) := by
  obtain ⟨v, hv⟩ := h.get (r := .x11) (by simp); simp [xval, hv]
theorem Cfg.x12 {s : St} (h : Cfg s) : s.regs.get? .x12 = some (getX s 12) := by
  obtain ⟨v, hv⟩ := h.get (r := .x12) (by simp); simp [xval, hv]
theorem Cfg.x13 {s : St} (h : Cfg s) : s.regs.get? .x13 = some (getX s 13) := by
  obtain ⟨v, hv⟩ := h.get (r := .x13) (by simp); simp [xval, hv]
theorem Cfg.x14 {s : St} (h : Cfg s) : s.regs.get? .x14 = some (getX s 14) := by
  obtain ⟨v, hv⟩ := h.get (r := .x14) (by simp); simp [xval, hv]
theorem Cfg.x15 {s : St} (h : Cfg s) : s.regs.get? .x15 = some (getX s 15) := by
  obtain ⟨v, hv⟩ := h.get (r := .x15) (by simp); simp [xval, hv]
theorem Cfg.x16 {s : St} (h : Cfg s) : s.regs.get? .x16 = some (getX s 16) := by
  obtain ⟨v, hv⟩ := h.get (r := .x16) (by simp); simp [xval, hv]
theorem Cfg.x17 {s : St} (h : Cfg s) : s.regs.get? .x17 = some (getX s 17) := by
  obtain ⟨v, hv⟩ := h.get (r := .x17) (by simp); simp [xval, hv]
theorem Cfg.x18 {s : St} (h : Cfg s) : s.regs.get? .x18 = some (getX s 18) := by
  obtain ⟨v, hv⟩ := h.get (r := .x18) (by simp); simp [xval, hv]
theorem Cfg.x19 {s : St} (h : Cfg s) : s.regs.get? .x19 = some (getX s 19) := by
  obtain ⟨v, hv⟩ := h.get (r := .x19) (by simp); simp [xval, hv]
theorem Cfg.x20 {s : St} (h : Cfg s) : s.regs.get? .x20 = some (getX s 20) := by
  obtain ⟨v, hv⟩ := h.get (r := .x20) (by simp); simp [xval, hv]
theorem Cfg.x21 {s : St} (h : Cfg s) : s.regs.get? .x21 = some (getX s 21) := by
  obtain ⟨v, hv⟩ := h.get (r := .x21) (by simp); simp [xval, hv]
theorem Cfg.x22 {s : St} (h : Cfg s) : s.regs.get? .x22 = some (getX s 22) := by
  obtain ⟨v, hv⟩ := h.get (r := .x22) (by simp); simp [xval, hv]
theorem Cfg.x23 {s : St} (h : Cfg s) : s.regs.get? .x23 = some (getX s 23) := by
  obtain ⟨v, hv⟩ := h.get (r := .x23) (by simp); simp [xval, hv]
theorem Cfg.x24 {s : St} (h : Cfg s) : s.regs.get? .x24 = some (getX s 24) := by
  obtain ⟨v, hv⟩ := h.get (r := .x24) (by simp); simp [xval, hv]
theorem Cfg.x25 {s : St} (h : Cfg s) : s.regs.get? .x25 = some (getX s 25) := by
  obtain ⟨v, hv⟩ := h.get (r := .x25) (by simp); simp [xval, hv]
theorem Cfg.x26 {s : St} (h : Cfg s) : s.regs.get? .x26 = some (getX s 26) := by
  obtain ⟨v, hv⟩ := h.get (r := .x26) (by simp); simp [xval, hv]
theorem Cfg.x27 {s : St} (h : Cfg s) : s.regs.get? .x27 = some (getX s 27) := by
  obtain ⟨v, hv⟩ := h.get (r := .x27) (by simp); simp [xval, hv]
theorem Cfg.x28 {s : St} (h : Cfg s) : s.regs.get? .x28 = some (getX s 28) := by
  obtain ⟨v, hv⟩ := h.get (r := .x28) (by simp); simp [xval, hv]
theorem Cfg.x29 {s : St} (h : Cfg s) : s.regs.get? .x29 = some (getX s 29) := by
  obtain ⟨v, hv⟩ := h.get (r := .x29) (by simp); simp [xval, hv]
theorem Cfg.x30 {s : St} (h : Cfg s) : s.regs.get? .x30 = some (getX s 30) := by
  obtain ⟨v, hv⟩ := h.get (r := .x30) (by simp); simp [xval, hv]
theorem Cfg.x31 {s : St} (h : Cfg s) : s.regs.get? .x31 = some (getX s 31) := by
  obtain ⟨v, hv⟩ := h.get (r := .x31) (by simp); simp [xval, hv]

/-! ## Summaries of the instruction-independent parts of a step -/

theorem fetch_ok (s : St) (a : PMA) (b : Bool) (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hpriv : s.regs.get? .cur_privilege = some .Machine) (hpc : s.regs.get? .PC = some pc)
    (hmisa : s.regs.get? .misa = some 0x800000000014112F#64)
    (hmst : s.regs.get? .mstatus = some 0x0000000A00000000#64)
    (hpma : s.regs.get? .pma_regions = some [⟨0x80000000#64, 0x80000000#64, a, b⟩])
    (hx : a.executable = true)
    (hpmp : s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0#8))
    {pa : _} (hpa : s.regs.get? .pmpaddr_n = some pa)
    (hhtif : s.regs.get? .htif_tohost_base = some none)
    (hal : pc.toNat % 4 = 0) (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ 0x100000000)
    (m0 : s.mem[pc.toNat]? = some b0) (m1 : s.mem[pc.toNat + 1]? = some b1)
    (m2 : s.mem[pc.toNat + 2]? = some b2) (m3 : s.mem[pc.toNat + 3]? = some b3)
    (hrvc : isRVC (BitVec.setWidth 16 (b3 ++ b2 ++ b1 ++ b0)) = false) :
    fetch () s = .ok (.F_Base (b3 ++ b2 ++ b1 ++ b0)) s := by
  have := access0 hal; have := aligned_v hal; have := aligned_p hal
  have := in_ram (n := 4) (by decide) hlo hhi
  sail_eval [*, hartSupports, matching_pma_region, matching_pma_region_bits_range, override_PMA,
    Functions.not]
  all_goals rfl

theorem pmp_none (s : St) (a : BitVec 64) (w : Nat) (acc : MemoryAccessType mem_payload)
    (hpmp : s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0#8))
    (hpa : s.regs.contains .pmpaddr_n = true) :
    pmpCheck (.Physaddr a) w acc .Machine s = .ok none s := by
  rw [Std.ExtDHashMap.contains_eq_isSome_get?] at hpa
  obtain ⟨pa, hpa⟩ := Option.isSome_iff_exists.mp hpa
  sail_eval [*]
  all_goals rfl

theorem dispatch_none (s : St) (hpriv : s.regs.get? .cur_privilege = some .Machine)
    (hmisa : s.regs.get? .misa = some 0x800000000014112F#64) (hmst : s.regs.get? .mstatus = some 0x0000000A00000000#64)
    {v1 v2 v3 v4 v5 : _} (h1 : s.regs.get? .mideleg = some v1) (h2 : s.regs.get? .mip = some v2)
    (h3 : s.regs.get? .mie = some v3) (h4 : s.regs.get? .sig_meip = some v4)
    (h5 : s.regs.get? .sig_seip = some v5) :
    dispatchInterrupt .Machine s = .ok none s := by
  sail_eval [*]

/-- `try_step` from a retiring `run_hart_active`. -/
theorem try_step_of {s s₁ : St} {w : BitVec 32} (h : Cfg s)
    (hr : run_hart_active 0 { s with regs := s.regs.insert .minstret_increment true } =
      .ok (.Step_Execute (.Retire_Success (), w)) s₁)
    {n m : BitVec 64} (hh : s₁.regs.get? .hart_state = some (.HART_ACTIVE ()))
    (hn : s₁.regs.get? .nextPC = some n) (hm : s₁.regs.get? .minstret = some m)
    (hi : s₁.regs.get? .minstret_increment = some true) :
    try_step 0 false s = .ok false { s₁ with regs := (s₁.regs.insert .PC n).insert .minstret (m + 1) } := by
  sail_eval frozen[run_hart_active] [hr, hh, hn, hm, hi, h.priv, h.hart, h.mcountinhibit, h.minstretcfg]
  all_goals rfl

/-- `run_hart_active` lemma + bookkeeping facts ⇒ `Retires`. -/
theorem retires_of {s : St} {w : BitVec 32} {F : St → St} {P : St → Prop}
    (hr : ∀ s, Cfg s → P s → run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), w)) (F s))
    (h : Cfg s) (hP : P s) (hP' : P { s with regs := s.regs.insert .minstret_increment true })
    {n m : BitVec 64}
    (hh : (F { s with regs := s.regs.insert .minstret_increment true }).regs.get? .hart_state =
      some (.HART_ACTIVE ()))
    (hn : (F { s with regs := s.regs.insert .minstret_increment true }).regs.get? .nextPC = some n)
    (hm : (F { s with regs := s.regs.insert .minstret_increment true }).regs.get? .minstret = some m)
    (hi : (F { s with regs := s.regs.insert .minstret_increment true }).regs.get? .minstret_increment =
      some true) :
    Retires s { F { s with regs := s.regs.insert .minstret_increment true } with
      regs := ((F { s with regs := s.regs.insert .minstret_increment true }).regs.insert .PC n).insert
        .minstret (m + 1) } :=
  ⟨⟨_, _, hr s h hP⟩, try_step_of h (hr _ (h.insert (by decide)) hP') hh hn hm hi⟩

/-- Introduce every `Cfg` fact as a hypothesis (for `sail_eval [*]`). -/
macro "cfg_facts " h:ident : tactic => `(tactic| (have := ($h).priv; have := ($h).hart; have := ($h).misa; have := ($h).mstatus; have := ($h).mcountinhibit; have := ($h).minstretcfg; have := ($h).pmpcfg; have := ($h).htif; have := ($h).elp; have := ($h).mseccfg; have := ($h).x1; have := ($h).x2; have := ($h).x3; have := ($h).x4; have := ($h).x5; have := ($h).x6; have := ($h).x7; have := ($h).x8; have := ($h).x9; have := ($h).x10; have := ($h).x11; have := ($h).x12; have := ($h).x13; have := ($h).x14; have := ($h).x15; have := ($h).x16; have := ($h).x17; have := ($h).x18; have := ($h).x19; have := ($h).x20; have := ($h).x21; have := ($h).x22; have := ($h).x23; have := ($h).x24; have := ($h).x25; have := ($h).x26; have := ($h).x27; have := ($h).x28; have := ($h).x29; have := ($h).x30; have := ($h).x31))

/-! ## Per-instruction step lemmas -/

def pcOK (pc : BitVec 64) : Prop := pc.toNat % 4 = 0 ∧ 0x80000000 ≤ pc.toNat ∧ pc.toNat + 4 ≤ 0x100000000

/-- the 4 bytes of instruction word `w` are at `pc` -/
def instrAt (s : St) (pc : BitVec 64) (w : BitVec 32) : Prop :=
  s.mem[pc.toNat]? = some (w.extractLsb' 0 8) ∧ s.mem[pc.toNat + 1]? = some (w.extractLsb' 8 8) ∧
  s.mem[pc.toNat + 2]? = some (w.extractLsb' 16 8) ∧ s.mem[pc.toNat + 3]? = some (w.extractLsb' 24 8)

theorem fetch_cfg {s : St} (h : Cfg s) {pc : BitVec 64} {w : BitVec 32} (hpc : s.regs.get? .PC = some pc)
    (hok : pcOK pc) (hi : instrAt s pc w)
    (hrvc : isRVC (BitVec.setWidth 16 (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8)) = false) :
    fetch () s = .ok (.F_Base (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++
      w.extractLsb' 0 8)) s := by
  obtain ⟨a, b, hp, hx, -⟩ := h.pma
  obtain ⟨pa, hpa⟩ := h.get (r := .pmpaddr_n) (by simp)
  exact fetch_ok s a b pc _ _ _ _ h.priv hpc h.misa h.mstatus hp hx h.pmpcfg hpa h.htif hok.1 hok.2.1
    hok.2.2 hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hrvc

theorem dispatch_cfg {s : St} (h : Cfg s) : dispatchInterrupt .Machine s = .ok none s := by
  obtain ⟨_, h1⟩ := h.get (r := .mideleg) (by simp)
  obtain ⟨_, h2⟩ := h.get (r := .mip) (by simp)
  obtain ⟨_, h3⟩ := h.get (r := .mie) (by simp)
  obtain ⟨_, h4⟩ := h.get (r := .sig_meip) (by simp)
  obtain ⟨_, h5⟩ := h.get (r := .sig_seip) (by simp)
  exact dispatch_none s h.priv h.misa h.mstatus h1 h2 h3 h4 h5

theorem ctrl_ne : ∀ r ∈ ctrlRegs, r ∉ xregs ∧ r ≠ .PC ∧ r ≠ .minstret ∧ r ≠ .nextPC ∧
    r ≠ .minstret_increment := by decide

@[simp] theorem xval_insert_mi {m : Regs} {b} (j : Fin 32) :
    xval (m.insert .minstret_increment b) j = xval m j := xval_insert_other (by decide) j
@[simp] theorem xval_insert_npc {m : Regs} {b} (j : Fin 32) :
    xval (m.insert .nextPC b) j = xval m j := xval_insert_other (by decide) j

/-- `Cfg` only looks at non-`x` registers, plus presence. -/
theorem Cfg.of {s s' : St} (h : Cfg s) (hg : ∀ r ∈ ctrlRegs, s'.regs.get? r = s.regs.get? r)
    (hc : ∀ r, s.regs.contains r → s'.regs.contains r) : Cfg s' := by
  obtain ⟨a, b, hp, hx⟩ := h.pma
  simp only [ctrlRegs, List.mem_cons, forall_eq_or_imp] at hg
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, -⟩ := hg
  exact ⟨g1 ▸ h.priv, g2 ▸ h.hart, g3 ▸ h.misa, g4 ▸ h.mstatus, g5 ▸ h.mcountinhibit,
    g6 ▸ h.minstretcfg, g7 ▸ h.pmpcfg, g8 ▸ h.htif, g9 ▸ h.elp, g10 ▸ h.mseccfg, ⟨a, b, g11 ▸ hp, hx⟩,
    fun r hr => hc r (h.present r hr)⟩

/-- The shape of a retiring instruction's effect: `nextPC`, memory, `x[rd]`. -/
def stepF (rd : Fin 32) (v npc : St → BitVec 64) (mem : St → Std.ExtHashMap Nat (BitVec 8)) (s : St) : St :=
  { s with regs := xset (s.regs.insert .nextPC (npc s)) rd (v s), mem := mem s }

/-- `s'` is `s` after one retired instruction that set `pc := pc'`, `x[rd] := v`, `mem := m`. -/
structure Next (s s' : St) (pc' : BitVec 64) (rd : Fin 32) (v : BitVec 64)
    (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  ret : Retires s s'
  cfg : Cfg s'
  pc : s'.regs.get? .PC = some pc'
  x : ∀ j, getX s' j = if j = rd ∧ j ≠ 0 then v else getX s j
  mem : s'.mem = m

/-- A per-word `run_hart_active` lemma of `stepF` shape gives `Next`.  `v`, `npc`, `mem` must
not depend on `minstret_increment` (the register `try_step` writes first). -/
theorem next_of {s : St} {pc : BitVec 64} {w : BitVec 32} {rd : Fin 32} {v npc : St → BitVec 64}
    {mem : St → Std.ExtHashMap Nat (BitVec 8)} {Q : St → Prop}
    (hr : ∀ s, Cfg s → s.regs.get? .PC = some pc → instrAt s pc w → Q s →
      run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), w)) (stepF rd v npc mem s))
    (h : Cfg s) (hpc : s.regs.get? .PC = some pc) (hi : instrAt s pc w) (hQ : Q s)
    (hQ' : Q { s with regs := s.regs.insert .minstret_increment true })
    (hv : v { s with regs := s.regs.insert .minstret_increment true } = v s)
    (hn : npc { s with regs := s.regs.insert .minstret_increment true } = npc s)
    (hm : mem { s with regs := s.regs.insert .minstret_increment true } = mem s) :
    ∃ s', Next s s' (npc s) rd (v s) (mem s) := by
  have hr' : ∀ s, Cfg s → (s.regs.get? .PC = some pc ∧ instrAt s pc w ∧ Q s) →
      run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), w)) (stepF rd v npc mem s) :=
    fun s h ⟨a, b, c⟩ => hr s h a b c
  have hP : s.regs.get? .PC = some pc ∧ instrAt s pc w ∧ Q s := ⟨hpc, hi, hQ⟩
  have hP' : (s.regs.insert .minstret_increment true).get? .PC = some pc ∧ instrAt s pc w ∧
      Q { s with regs := s.regs.insert .minstret_increment true } :=
    ⟨by simp [hpc, Std.ExtDHashMap.get?_insert], hi, hQ'⟩
  obtain ⟨mi, hmi⟩ := h.get (r := .minstret) (by simp)
  have hx : ∀ r, r ∉ xregs → (stepF rd v npc mem { s with regs := s.regs.insert .minstret_increment true }).regs.get? r =
      ((s.regs.insert .minstret_increment true).insert .nextPC (npc s)).get? r := by
    intro r hr; simp only [stepF, xset_get_other hr, hn]
  refine ⟨_, retires_of (n := npc s) (m := mi) hr' h hP hP'
    (by simp [hx _ (by decide : Register.hart_state ∉ xregs), h.hart, Std.ExtDHashMap.get?_insert])
    (by simp [hx _ (by decide : Register.nextPC ∉ xregs), Std.ExtDHashMap.get?_insert])
    (by simp [hx _ (by decide : Register.minstret ∉ xregs), hmi, Std.ExtDHashMap.get?_insert])
    (by simp [hx _ (by decide : Register.minstret_increment ∉ xregs), Std.ExtDHashMap.get?_insert]), ?_, ?_, ?_, ?_⟩
  · refine h.of (fun r hr => ?_) (fun r hr => ?_)
    · obtain ⟨h0, h1, h2, h3, h4⟩ := ctrl_ne r hr
      simp [Std.ExtDHashMap.get?_insert, stepF, xset_get_other h0, Ne.symm h1, Ne.symm h2,
        Ne.symm h3, Ne.symm h4]
    · simp [Std.ExtDHashMap.contains_insert, stepF]
      exact Or.inr (Or.inr (xset_contains (by simp [Std.ExtDHashMap.contains_insert, hr])))
  · simp [Std.ExtDHashMap.get?_insert]
  · intro j
    simp only [getX_eq, xval_insert_other (by decide : Register.minstret ∉ xregs),
      xval_insert_other (by decide : Register.PC ∉ xregs), stepF, xval_xset, hv,
      xval_insert_other (by decide : Register.nextPC ∉ xregs),
      xval_insert_other (by decide : Register.minstret_increment ∉ xregs)]
  · simp [stepF, hm]

set_option hygiene false in
/-- the `run_hart_active` part of `step_word` -/
macro "step_word_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := Proven.fetch_cfg h hpc hok hi (by decide)
    have hd := Proven.dispatch_cfg h
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck] [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.zopz0zIzJ_u,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      BitVec.toNat_sub, BitVec.toNat_add]
    all_goals simp [Proven.stepF, Proven.xset, Proven.update0_even, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- Prove `∃ s', Next s s' npc rd v m` for one concrete instruction word, from `h : Cfg s`,
`hpc : s.regs.get? .PC = some pc`, `hok : pcOK pc`, `hi : instrAt s pc w`; every other hypothesis
mentioning `s` (e.g. a branch condition, a load address in RAM) is passed on as a side condition. -/
elab "step_word" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "step_word: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "step_word: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "step_word: {e} mentions s'"
    Term.exprToSyntax (← mkLambdaFVars #[s] e)
  let (npc, v, mem) := (← fn args[2]!, ← fn args[4]!, ← fn args[5]!)
  -- side conditions: hypotheses about `s` other than `h hpc hi`
  let mut side : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || [`h, `hpc, `hi].contains d.userName then continue
    let t ← instantiateMVars d.type
    if (← isProp t) && t.containsFVar s.fvarId! then side := side.push d.toExpr
  let qBody ← side.foldrM (fun p acc => do mkAppM ``And #[← inferType p, acc]) (mkConst ``True)
  let qPf ← side.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) (mkConst ``True.intro)
  let q ← Term.exprToSyntax (← mkLambdaFVars #[s] qBody)
  let hq ← Term.exprToSyntax qPf
  let sT ← Term.exprToSyntax s
  evalTactic (← `(tactic| refine Proven.next_of (s := $sT) (npc := $npc) (v := $v) (mem := $mem)
    (Q := $q) ?_ $(mkIdent `h) $(mkIdent `hpc) $(mkIdent `hi) $hq
    (by set_option linter.unnecessarySimpa false in simpa using $hq) ?_ ?_ ?_))
  evalTactic (← `(tactic| step_word_core))

end Proven

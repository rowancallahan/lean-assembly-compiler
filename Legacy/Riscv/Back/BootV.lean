/- The two boot-stub instructions that run before `Cfg` holds (`misa.V` still set by the model's reset):
`lui t2, 0x200` and `csrrc x0, misa, t2`, which clears `misa.V`.  Proved by symbolic evaluation of the Sail
step, as the step lemmas of `Riscv/Steps/Step.lean` are, from `CfgV` (`Cfg` up to `misa`). -/
import Legacy.Riscv.Back.BootReset
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace Proven.Boot

theorem fetch_okV (s : St) (a : PMA) (b : Bool) (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (hpriv : s.regs.get? .cur_privilege = some .Machine) (hpc : s.regs.get? .PC = some pc)
    (hmisa : s.regs.get? .misa = some vMisa)
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
    LeanRV64D.Functions.fetch () s = .ok (.F_Base (b3 ++ b2 ++ b1 ++ b0)) s := by
  have := access0 hal; have := aligned_v hal; have := aligned_p hal
  have := in_ram (n := 4) (by decide) hlo hhi
  simp only [vMisa] at hmisa
  sail_eval [*, hartSupports, matching_pma_region, matching_pma_region_bits_range, override_PMA,
    Functions.not]
  all_goals rfl

theorem dispatch_noneV (s : St) (hpriv : s.regs.get? .cur_privilege = some .Machine)
    (hmisa : s.regs.get? .misa = some vMisa) (hmst : s.regs.get? .mstatus = some 0x0000000A00000000#64)
    {v1 v2 v3 v4 v5 : _} (h1 : s.regs.get? .mideleg = some v1) (h2 : s.regs.get? .mip = some v2)
    (h3 : s.regs.get? .mie = some v3) (h4 : s.regs.get? .sig_meip = some v4)
    (h5 : s.regs.get? .sig_seip = some v5) :
    dispatchInterrupt .Machine s = .ok none s := by
  simp only [vMisa] at hmisa
  sail_eval [*]

@[simp] theorem xval_insert_misa {m : Regs} {v} (j : Fin 32) : xval (m.insert .misa v) j = xval m j :=
  xval_insert_other (by decide) j

theorem gi_ne {m : Regs} {r q : Register} {v} (h : (r == q) = false) : (m.insert r v).get? q = m.get? q := by
  rw [Std.ExtDHashMap.get?_insert]; simp at h; simp [h]

set_option hygiene false in
/-- the facts of `h : Cfg (unV s)` about `s` -/
macro "v_facts" : tactic => `(tactic| (
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    obtain ⟨pa, hpa⟩ := h.get (r := .pmpaddr_n) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .mideleg) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .mip) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .mie) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .sig_meip) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .sig_seip) (by simp)
    obtain ⟨_, _⟩ := h.get (r := .minstret) (by simp)
    simp (disch := decide) only [unV, gi_ne, getX_eq, xval_insert_misa] at *
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := fetch_okV s _ _ pc _ _ _ _ (by assumption) hpc hm (by assumption) (by assumption) (by assumption)
      (by assumption) hpa (by assumption) hok.1 hok.2.1 hok.2.2 hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (by decide)
    have hd := dispatch_noneV s (by assumption) hm (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)))

/-- `lui t2, 0x200` -/
def luiW : BitVec 32 := 0x002003b7#32
/-- `csrrc x0, misa, t2` -/
def csrW : BitVec 32 := 0x3013b073#32

theorem wr_misa (v : BitVec 64) : write_CSR 0x301#12 v = (do
    let m ← readReg Register.misa; let m' ← legalize_misa m v; writeReg Register.misa m'
    let r ← readReg Register.misa; pure (Result.Ok r)) := by rfl
theorem acc_misa (p a) (s : St) : is_CSR_accessible 0x301#12 p a s = .ok true s := by rfl
theorem se_misa (p a) (s : St) : stateen_allows_CSR_access 0x301#12 p a s = .ok true s := by rfl

set_option hygiene false in
macro "v_eval" : tactic => `(tactic| (
  sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt,
    LeanRV64D.Functions.pmpCheck] [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel,
    LeanRV64D.Functions.matching_pma_region, LeanRV64D.Functions.matching_pma_region_bits_range,
    LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.range_subset,
    LeanRV64D.Functions.zopz0zIzJ_u, LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u,
    LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
    BitVec.toNat_sub, BitVec.toNat_add, luiW, csrW, acc_misa, se_misa, wr_misa]
  all_goals first | rfl | simp))

theorem run_lui (s : St) (h : Cfg (unV s)) (hm : s.regs.get? .misa = some vMisa) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc luiW) :
    run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), luiW))
      { s with regs := (s.regs.insert .nextPC (pc + 4)).insert .x7 0x200000#64 } := by
  v_facts; v_eval

theorem run_csr (s : St) (h : Cfg (unV s)) (hm : s.regs.get? .misa = some vMisa) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc csrW)
    (h7 : s.regs.get? .x7 = some 0x200000#64) :
    run_hart_active 0 s = .ok (.Step_Execute (.Retire_Success (), csrW))
      { s with regs := (s.regs.insert .nextPC (pc + 4)).insert .misa cfgMisa } := by
  v_facts; v_eval


theorem try_stepV {s s₁ : St} {w : BitVec 32} (hpriv : s.regs.get? .cur_privilege = some .Machine)
    (hhart : s.regs.get? .hart_state = some (.HART_ACTIVE ())) (hmc : s.regs.get? .mcountinhibit = some 0#32)
    (hmcfg : s.regs.get? .minstretcfg = some 0#64)
    (hr : run_hart_active 0 { s with regs := s.regs.insert .minstret_increment true } =
      .ok (.Step_Execute (.Retire_Success (), w)) s₁)
    {n m : BitVec 64} (hh : s₁.regs.get? .hart_state = some (.HART_ACTIVE ()))
    (hn : s₁.regs.get? .nextPC = some n) (hm : s₁.regs.get? .minstret = some m)
    (hi : s₁.regs.get? .minstret_increment = some true) :
    try_step 0 false s = .ok false { s₁ with regs := (s₁.regs.insert .PC n).insert .minstret (m + 1) } := by
  sail_eval frozen[run_hart_active] [hr, hh, hn, hm, hi, hpriv, hhart, hmc, hmcfg]
  all_goals rfl

/-- `CfgV` survives register writes outside the control registers -/
theorem CfgV.of {s s' : St} (h : CfgV s) (hg : ∀ r ∈ ctrlRegs, s'.regs.get? r = s.regs.get? r)
    (hc : ∀ r, s.regs.contains r → s'.regs.contains r) : CfgV s' := by
  refine ⟨h.1.of (fun r hr => ?_) (fun r hr => ?_), (hg _ (by decide)).trans h.2⟩
  · simp only [unV, Std.ExtDHashMap.get?_insert]; split
    · rfl
    · exact hg r hr
  · simp only [unV, Std.ExtDHashMap.contains_insert] at hr ⊢
    rcases Bool.or_eq_true _ _ ▸ hr with hr | hr
    · simp [hr]
    · simp [hc r hr]

/-- `Cfg` once `misa` is `Cfg`'s -/
theorem cfg_of_V {s s' : St} (h : CfgV s) (hmisa : s'.regs.get? .misa = some cfgMisa)
    (hg : ∀ r ∈ ctrlRegs, r ≠ .misa → s'.regs.get? r = s.regs.get? r)
    (hc : ∀ r, s.regs.contains r → s'.regs.contains r) : Cfg s' := by
  refine h.1.of (fun r hr => ?_) (fun r hr => ?_)
  · simp only [unV, Std.ExtDHashMap.get?_insert]; split
    · next he => simp at he; subst he; simpa using hmisa
    · next he => exact hg r hr (fun e => he (by simp [e]))
  · simp only [unV, Std.ExtDHashMap.contains_insert] at hr
    rcases Bool.or_eq_true _ _ ▸ hr with hr | hr
    · simp at hr; subst hr; rw [Std.ExtDHashMap.contains_eq_isSome_get?, hmisa]; rfl
    · exact hc r hr

theorem cfgV_facts {s : St} (h : CfgV s) : s.regs.get? .cur_privilege = some .Machine ∧
    s.regs.get? .hart_state = some (.HART_ACTIVE ()) ∧ s.regs.get? .mcountinhibit = some 0#32 ∧
    s.regs.get? .minstretcfg = some 0#64 ∧ ∃ m, s.regs.get? .minstret = some m := by
  have h1 := h.1
  obtain ⟨m, hm⟩ := h1.get (r := .minstret) (by simp)
  have := h1.priv; have := h1.hart; have := h1.mcountinhibit; have := h1.minstretcfg
  simp (disch := decide) only [unV, gi_ne] at *
  exact ⟨by assumption, by assumption, by assumption, by assumption, m, hm⟩

theorem CfgV.mi {s : St} (h : CfgV s) : CfgV { s with regs := s.regs.insert .minstret_increment true } :=
  h.of (fun r hr => by
    simp only [ctrlRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Std.ExtDHashMap.get?_insert])
    (fun r hr => by simp [Std.ExtDHashMap.contains_insert, hr])

/-- **`lui t2, 0x200`** from `CfgV` -/
theorem step_luiV {s : St} (h : CfgV s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
    (hi : instrAt s pc luiW) :
    ∃ s', Retires s s' ∧ CfgV s' ∧ s'.regs.get? .PC = some (pc + 4) ∧ s'.regs.get? .x7 = some 0x200000#64 ∧
      s'.mem = s.mem := by
  obtain ⟨hp, hh, hc, hcfg, m, hm⟩ := cfgV_facts h
  have h1 := h.mi
  have hr := run_lui _ h1.1 h1.2 (by simpa [Std.ExtDHashMap.get?_insert] using hpc) hok hi
  refine ⟨_, ⟨⟨_, _, run_lui _ h.1 h.2 hpc hok hi⟩, try_stepV (n := pc + 4) (m := m) hp hh hc hcfg hr
    (by simpa [Std.ExtDHashMap.get?_insert] using hh) (by simp [Std.ExtDHashMap.get?_insert])
    (by simpa [Std.ExtDHashMap.get?_insert] using hm) (by simp [Std.ExtDHashMap.get?_insert])⟩, ?_, ?_, ?_, rfl⟩
  · refine h.of (fun r hr => ?_) (fun r hr => by simp [Std.ExtDHashMap.contains_insert, hr])
    simp only [ctrlRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]

/-- **`csrrc x0, misa, t2`** from `CfgV` with `t2 = 1 << 21`: `Cfg` from here on -/
theorem step_csrV {s : St} (h : CfgV s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
    (hi : instrAt s pc csrW) (h7 : s.regs.get? .x7 = some 0x200000#64) :
    ∃ s', Retires s s' ∧ Cfg s' ∧ s'.regs.get? .PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨hp, hh, hc, hcfg, m, hm⟩ := cfgV_facts h
  have h1 := h.mi
  have hr := run_csr _ h1.1 h1.2 (by simpa [Std.ExtDHashMap.get?_insert] using hpc) hok hi
    (by simpa [Std.ExtDHashMap.get?_insert] using h7)
  refine ⟨_, ⟨⟨_, _, run_csr _ h.1 h.2 hpc hok hi h7⟩, try_stepV (n := pc + 4) (m := m) hp hh hc hcfg hr
    (by simpa [Std.ExtDHashMap.get?_insert] using hh) (by simp [Std.ExtDHashMap.get?_insert])
    (by simpa [Std.ExtDHashMap.get?_insert] using hm) (by simp [Std.ExtDHashMap.get?_insert])⟩, ?_, ?_, rfl⟩
  · refine cfg_of_V h (by simp [Std.ExtDHashMap.get?_insert]) (fun r hr hne => ?_)
      (fun r hr => by simp [Std.ExtDHashMap.contains_insert, hr])
    simp only [ctrlRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hne | simp [Std.ExtDHashMap.get?_insert]
  · simp [Std.ExtDHashMap.get?_insert]

end Proven.Boot

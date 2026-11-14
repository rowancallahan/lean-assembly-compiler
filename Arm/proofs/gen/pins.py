# Pinned configuration registers of `ArmFull` (field, register, value). Prints the Lean `Pins` block.
PINS = [
  ("feat", "FeatureImpl", "featV"),
  ("scr", "SCR_EL3", "0"),
  ("edscr", "_EDSCR", "edscrV"),
  ("mdccsr", "MDCCSR_EL0", "0"),
  ("oslsr", "OSLSR_EL1", "0"),
  ("mdcr3", "MDCR_EL3", "0"),
  ("gic", "__GIC_Pending", "none"),
  ("mpam3", "_MPAM3_EL3", "0"),
  ("mpam2", "MPAM2_EL2", "0"),
  ("pa", "__supported_pa_size", "48"),
  ("tcr3", "TCR_EL3", "0"),
  ("sctlr3", "SCTLR_EL3", "0"),
  ("mair3", "MAIR_EL3", "0"),
  ("mdscr", "MDSCR_EL1", "0"),
  ("spe", "SPESampleInFlight", "false"),
  ("dbgen", "DBGEN", ".Signal_Low"),
  ("spiden", "SPIDEN", ".Signal_Low"),
  ("edesr", "EDESR", "0"),
  ("emu", "__emulator_termination_opcode", "none"),
  ("pmcr", "PMCR_EL0", "0"),
  ("mdcr2", "MDCR_EL2", "0"),
  ("cntcr", "CNTCR", "0"),
  ("cntp", "CNTP_CTL_EL0", "0"),
  ("cnthp", "CNTHP_CTL_EL2", "0"),
  ("cntps", "CNTPS_CTL_EL1", "0"),
  ("cntv", "CNTV_CTL_EL0", "0"),
  ("brbfcr", "BRBFCR_EL1", "0"),
  ("pcount", "PhysicalCount", "0"),
  ("cnthpcv", "CNTHP_CVAL_EL2", "1"),
]
import sys
out = []
out.append("/-- the pinned configuration registers (and the PSTATE fields) the full step relies on -/")
out.append("structure Pins (m : Regs) : Prop where")
out.append("  ps : ∃ p : ProcState, m.get? .PSTATE = some p ∧ p.EL = 3#2 ∧ p.nRW = 0#1 ∧ p.IL = 0#1")
for f, r, v in PINS:
  out.append(f"  {f} : m.get? .{r} = some {v}")
out.append("")
out.append("/-- `true` on registers outside `Pins` -/")
out.append("def NotPinned (r : Register) : Bool := !(r == .PSTATE || " + " || ".join(f"r == .{r}" for _, r, _ in PINS) + ")")
out.append("")
out.append("theorem np_ne {r r' : Register} (h : NotPinned r = true) (h' : NotPinned r' = false) : ¬ (r == r') = true := by")
out.append("  intro e; rw [beq_iff_eq] at e; subst e; rw [h] at h'; cases h'")
out.append("")
out.append("theorem pins_insert {m : Regs} {r : Register} (v : RegisterType r) (h : NotPinned r = true) :")
out.append("    Pins (m.insert r v) ↔ Pins m := by")
out.append("  constructor <;> intro hc")
for d in range(2):
  out.append("  · refine ⟨?_, " + ", ".join(["?_"] * len(PINS)) + "⟩")
  out.append("    · obtain ⟨p, hp, hpp⟩ := hc.ps; exact ⟨p, by simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .PSTATE) h rfl)] using hp, hpp⟩")
  for i, (f, r, v) in enumerate(PINS):
    out.append(f"    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (np_ne (r' := .{r}) h rfl)] using hc.{f}")
out.append("")
out.append("theorem pins_pstate {m : Regs} (q : ProcState) (hq : q.EL = 3#2 ∧ q.nRW = 0#1 ∧ q.IL = 0#1) (hc : Pins m) :")
out.append("    Pins (m.insert .PSTATE q) := by")
out.append("  refine ⟨⟨q, by simp [Std.ExtDHashMap.get?_insert], hq⟩, " + ", ".join(["?_"] * len(PINS)) + "⟩")
for i, (f, r, v) in enumerate(PINS):
  out.append(f"  · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (Register.PSTATE == Register.{r}) = true by decide)] using hc.{f}")
out.append("")
out.append("theorem xreg_ne' {r : Register} (h : r.ctorIdx < 1059 ∨ 1089 < r.ctorIdx) : ∀ i < 31, xreg i ≠ r := by")
out.append("  intro i hi e; have := xreg_idx i hi; rw [e] at this; omega")
out.append("")
out.append("/-- `Pins` survives any change that leaves every pinned register except PSTATE alone and keeps EL/nRW/IL -/")
out.append("theorem pins_frame {m m' : Regs} (hc : Pins m)")
out.append("    (hfr : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .PSTATE → r ≠ .SEE → m'.get? r = m.get? r)")
out.append("    (hps : ∀ p, m.get? .PSTATE = some p → ∃ q, m'.get? .PSTATE = some q ∧ q.EL = p.EL ∧ q.nRW = p.nRW ∧ q.IL = p.IL) :")
out.append("    Pins m' := by")
out.append("  refine ⟨?_, " + ", ".join(["?_"] * len(PINS)) + "⟩")
out.append("  · obtain ⟨p, hp, h1, h2, h3⟩ := hc.ps; obtain ⟨q, hq, e1, e2, e3⟩ := hps p hp")
out.append("    exact ⟨q, hq, e1 ▸ h1, e2 ▸ h2, e3 ▸ h3⟩")
for i, (f, r, v) in enumerate(PINS):
  out.append(f"  · rw [hfr .{r} (xreg_ne' (by decide)) (by decide) (by decide)]; exact hc.{f}")
out.append("")
out.append("set_option hygiene false in")
out.append("/-- unpack `Pins s.regs` (named `hc`) into the atomic facts `esimp` rewrites with -/")
out.append("macro \"pins\" : tactic => `(tactic| (obtain ⟨⟨p, hp, hel, hrw, hil⟩, " + ", ".join("h_"+f for f,_,_ in PINS) + "⟩ := id hc))")
print("\n".join(out))

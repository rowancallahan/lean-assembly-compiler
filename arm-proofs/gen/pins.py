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
]
import sys
out = []
out.append("/-- the pinned configuration registers (and the PSTATE fields) the full step relies on -/")
out.append("structure Pins (m : Regs) : Prop where")
out.append("  ps : ∃ p : ProcState, m.get? .PSTATE = some p ∧ p.EL = 3#2 ∧ p.nRW = 0#1")
for f, r, v in PINS:
  out.append(f"  {f} : m.get? .{r} = some {v}")
out.append("")
out.append("/-- registers outside `Pins` -/")
out.append("def NotPinned (r : Register) : Prop := r ≠ .PSTATE ∧ " + " ∧ ".join(f"r ≠ .{r}" for _, r, _ in PINS))
out.append("")
out.append("theorem pins_insert {m : Regs} {r : Register} (v : RegisterType r) (h : NotPinned r) :")
out.append("    Pins (m.insert r v) ↔ Pins m := by")
out.append("  obtain ⟨" + ", ".join(["h0"] + [f"h{i+1}" for i in range(len(PINS))]) + "⟩ := h")
out.append("  constructor <;> intro hc")
for d in range(2):
  out.append("  · refine ⟨?_, " + ", ".join(["?_"] * len(PINS)) + "⟩")
  out.append("    · obtain ⟨p, hp, h⟩ := hc.ps; exact ⟨p, by simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (r == Register.PSTATE) = true by simpa using h0)] using hp, h⟩")
  for i, (f, r, v) in enumerate(PINS):
    out.append(f"    · simpa only [Std.ExtDHashMap.get?_insert, dif_neg (show ¬ (r == Register.{r}) = true by simpa using h{i+1})] using hc.{f}")
print("\n".join(out))

# field getters of the pinned registers' types, for the `gsimp` macro in Arm/Hooks.lean
import re
txt = open('/home/user/armv9-lean/Armv9/V8Base.lean').read()
pre = ['TCR_EL3_Type','SCTLR_EL3_Type','SCR_EL3_Type','SCRType','SCTLRType','MDSCR_EL1_Type','MDCR_EL3_Type','MDCR_EL2_Type',
       'OSLSR_EL1_Type','EDSCR_Type','HCR_EL2_Type','PMCR_EL0_Type','CNTCR_Type','MPAM3_EL3_Type','TTBR0_EL3_Type',
       'PMBSR_EL1_Type','MAIRType','EDESR_Type','CNTP_CTL_EL0_Type','CNTHP_CTL_EL2_Type','CNTPS_CTL_EL1_Type',
       'CNTV_CTL_EL0_Type','BRBFCR_EL1_Type']
names = [n for n in re.findall(r'^def (_get_\w+) ', txt, re.M) if any(n.startswith('_get_' + p + '_') for p in pre)]
lines, cur = [], ' '
for n in names:
  if len(cur) + len(n) > 110: lines.append(cur); cur = ' '
  cur += ' ' + n + ','
lines.append(cur)
print('macro "gsimp" : tactic => `(tactic| ((try simp only [')
print("\n".join(lines).rstrip(',') + '] at *); esimp))')

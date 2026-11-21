#!/usr/bin/env python3
"""report.py OUTDIR: LEAN_DIFF.md from campaign.py logs (tally per compiler/class, one minimal repro per class, all NEW? entries)."""
import json, glob, sys, collections, os, datetime
O=sys.argv[1]; print(f"# LEAN_DIFF: standing differential campaign, nano vs real Lean 4.34.1 (branch lean-diff)\n\nGenerated {datetime.datetime.utcnow():%Y-%m-%d %H:%M}Z. Harness: `Testing/nano/v2self/fuzz/lean_diff/` (UNPROVEN glue). Oracle: `lean` 4.34.1 on `import Nano.Main.Prelude` + program + `#eval m input`; nano = B2.bin via nanorun (RV) and GA_arm.bin under qemu-aarch64 (sampled). Classes M1–M14: `LEAN_RULES.md` §0; `cls` is an auto-classification of the *minimized* program (heuristic; `NEW?` = needs manual triage).\n")
for t in sorted(glob.glob(O+"/*.tally")):
    print("## "+os.path.basename(t)[:-6]+"\n```\n"+open(t).read().strip()+"\n```")
    rs=[json.loads(l) for l in open(t[:-6]+".jsonl")] if os.path.exists(t[:-6]+".jsonl") else []
    c=collections.Counter(r["cls"] for r in rs); print("distinct minimized divergences by class: "+json.dumps(dict(c))+"\n")
    seen=set()
    for r in rs:
        if r["cls"] in seen and r["cls"] not in("NEW?","ARM","M10?"): continue
        seen.add(r["cls"]); print(f"* **{r['cls']}** ({r['kind']}): `{r['min'].strip()[:300]!r}` input `{r['inp']}` nano `{r['nano'][:40]}` lean `{r['lean'][:90]}`")
    print()

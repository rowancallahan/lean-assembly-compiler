#!/usr/bin/env python3
"""rssmon.py OUT: every second, record VmHWM (peak RSS) and elapsed time of each running `lean` process, keyed by
the .lean file it compiles; rewrite OUT as "peak_MB seconds file" lines. Run it beside a build; kill it after."""
import os, sys, time
out, seen = sys.argv[1], {}
while True:
    for p in os.listdir("/proc"):
        if not p.isdigit(): continue
        try:
            a = open(f"/proc/{p}/cmdline", "rb").read().split(b"\0")
            if not a[0].endswith(b"/lean"): continue
            f = next(x.decode() for x in a if x.endswith(b".lean"))
            hwm = next(int(l.split()[1]) for l in open(f"/proc/{p}/status") if l.startswith("VmHWM"))
        except (OSError, StopIteration):
            continue
        t0 = seen.get((p, f), (0, time.time()))[1]
        seen[(p, f)] = (max(hwm, seen.get((p, f), (0, 0))[0]), t0, time.time())
    with open(out + ".tmp", "w") as o:
        for (p, f), (h, t0, t1) in sorted(seen.items(), key=lambda kv: -kv[1][0]):
            o.write(f"{h // 1024} {t1 - t0:.0f} {f}\n")
    os.replace(out + ".tmp", out)
    time.sleep(1)

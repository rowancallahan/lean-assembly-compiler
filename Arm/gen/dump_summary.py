#!/usr/bin/env python3
"""dump_summary.py DUMP: short fingerprint of a dump_hashes.lean output, small enough to send as a message.
Prints the line count and sha256 of the whole file, then 256 buckets (rows grouped by md5(name)[:2]):
"bucket rows sha256[:16]". Two dumps are equal iff the summaries are equal (up to sha256 collisions); a differing
bucket names the 1/256 of the rows to exchange in full: dump_summary.py DUMP BUCKET prints that bucket's rows."""
import hashlib, sys
from collections import defaultdict
rows = open(sys.argv[1]).read().splitlines()
b = defaultdict(list)
for r in rows: b[hashlib.md5(r.split(" ", 1)[0].encode()).hexdigest()[:2]].append(r)
if len(sys.argv) > 2:
    print("\n".join(b[sys.argv[2]])); sys.exit()
print("rows", len(rows), "sha256", hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())
for k in sorted(b): print(k, len(b[k]), hashlib.sha256("\n".join(b[k]).encode()).hexdigest()[:16])

# integrator helper: resolve a merge conflict in expected-axioms.txt by keeping both sides, theirs first
import sys
p = 'Testing/scripts/expected-axioms.txt'
out, ours, theirs, mode = [], [], [], 0
for line in open(p):
    if line.startswith('<<<<<<<'): mode = 1
    elif line.startswith('=======') and mode == 1: mode = 2
    elif line.startswith('>>>>>>>') and mode == 2:
        seen = set(out)
        for l in theirs + ours:
            if l not in seen: out.append(l); seen.add(l)
        ours, theirs, mode = [], [], 0
    elif mode == 1: ours.append(line)
    elif mode == 2: theirs.append(line)
    else: out.append(line)
assert mode == 0
open(p, 'w').writelines(out)

#!/usr/bin/env python3
"""expand.py < E-output > S : S-compact → S. E writes the fixed phrases listed in gen_emitstr.ABBREV as the token
`!<id>`; this restores them (a token-level table lookup, unproven glue like the shim)."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
src = open(os.path.join(sys.path[0], 'gen_emitstr.py')).read().split('def words')[0]
g = {}; exec(src, g); P, A = g['P'], set(g['ABBREV'])
def sub(m):
    i = int(m.group(1)); assert i in A, i
    return P[i]
sys.stdout.write(re.sub(r' !(\d+)(?= |\n|$)', sub, sys.stdin.read()))

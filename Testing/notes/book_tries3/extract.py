# Extract top-level commands of fp-lean examples with file:line; build per-def contexts (dependency closure) -> decls.json
import re, os, glob, json, sys
R = sys.argv[1]            # fp-lean/examples
OUT = sys.argv[2]
files = sorted(f for f in glob.glob(R + '/**/*.lean', recursive=True)
               if '/.lake/' not in f and 'lakefile' not in f)
KEEP = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*'
                  r'(def|abbrev|instance|structure|inductive|class|theorem|namespace|end|section|open|variable|universe|'
                  r'set_option|deriving|attribute|export|mutual|macro|syntax|notation|infix\w*|local)\b')
DEFK = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*(def|abbrev|instance|structure|inductive|class|theorem)\b')
res = []
for f in files:
    rel = os.path.relpath(f, R)
    lines = open(f).read().split('\n')
    # command split: a new command starts at a non-indented, non-comment, non-continuation line
    cmds = []; cur = None; incom = False; discarding = False; steps = False
    for i, l in enumerate(lines):
        if incom:
            if '-/' in l: incom = False
            continue
        s = l.strip()
        if s == 'discarding': discarding = True; continue
        if s == 'stop discarding': discarding = False; continue
        if re.match(r'^(evaluation steps|equational steps)', s): steps = True; continue
        if re.match(r'^end (evaluation steps|equational steps)', s): steps = False; continue
        if discarding or steps: continue
        if s.startswith('/-') and not l[:1].isspace():
            # block / doc comment at column 0: skip entirely
            if '-/' not in s[2:]: incom = True
            continue
        if not l or l[0].isspace() or s.startswith('--') or s.startswith('|') or s.startswith('where') or s[0] in ')]}':
            if cur is not None and not s.startswith('--'): cur['lines'].append((i + 1, l))
            elif cur is not None: pass
            continue
        # new command
        if cur is not None: cmds.append(cur)
        cur = dict(file=rel, line=i + 1, lines=[(i + 1, l)])
    if cur is not None: cmds.append(cur)
    merged=[]; pend=None
    for c in cmds:
        first=c['lines'][0][1]
        if re.match(r'^(open|set_option|variable|universe|attribute)\b',first) and re.search(r'\bin\s*$',first.split('--')[0]) and len(c['lines'])==1:
            pend=(pend or [])+[c['lines'][0]]
            continue
        if pend:
            if re.match(r'^(namespace|section|end)\b',first): pend=None
            else:
                c['lines']=pend+c['lines']; c['line']=pend[0][0]; pend=None
        merged.append(c)
    cmds=merged
    ns = []; scopes = [dict(kind='top', name='', cmds=[])]
    for c in cmds:
        txt = '\n'.join(t for _, t in c['lines']).rstrip()
        c['end'] = [n for n,tt in c['lines'] if tt.strip()][-1]
        # trim trailing blank / comment
        tl_=txt.split('\n'); k_=0
        while k_<len(tl_)-1 and re.match(r'^(open|set_option|variable|universe|attribute)\b',tl_[k_]) and re.search(r'\bin\s*$',tl_[k_].split('--')[0]): k_+=1
        first = tl_[k_]
        c['src'] = txt
        del c['lines']
        c['ns'] = '.'.join(s['name'] for s in scopes if s['kind'] == 'namespace')
        m = re.match(r'^namespace\s+(\S+)', first)
        if m:
            scopes.append(dict(kind='namespace', name=m.group(1), cmds=[])); c['kind'] = 'namespace'; continue
        if re.match(r'^section\b', first):
            scopes.append(dict(kind='section', name='', cmds=[])); c['kind'] = 'section'; continue
        m = re.match(r'^end\b\s*(\S*)', first)
        if m:
            if len(scopes) > 1: scopes.pop()
            continue
        if re.match(r'^(open|variable|universe|set_option|attribute|export)\b', first):
            scopes[-1]['cmds'].append(c['src']); continue
        c['scope'] = [dict(kind=s['kind'], name=s['name'], cmds=list(s['cmds'])) for s in scopes]
        k = KEEP.match(first)
        if not k: continue
        c['kind'] = k.group(1)
        d = DEFK.match(first)
        c['name'] = ''
        if d:
            rest = first[d.end():].strip()
            nm = re.match(r"([^\s:({\[\]]+)", rest)
            c['name'] = nm.group(1) if nm else ''
            if c['kind'] == 'instance': c['name'] = ''
        res.append(c)
json.dump(res, open(OUT, 'w'))
from collections import Counter
print(len(res), Counter(r['kind'] for r in res))

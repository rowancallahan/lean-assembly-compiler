import re, sys, json
KW = ('def','abbrev','theorem','lemma','instance','structure','inductive','opaque','class','mutual','axiom')
MODS = ('protected','private','noncomputable','unsafe','partial','nonrec')

def parse(path):
    lines = open(path).read().split('\n')
    items = []; frames = []; glob = []; pending = []; cur = None; depth = 0
    def close():
        nonlocal cur
        cur = None
    def ctx():
        return [(f[0], f[1], list(f[2])) for f in frames]
    in_mut = [False]
    i = 0
    while i < len(lines):
        ln = lines[i]; i += 1
        if in_mut[0]:
            cur['body'].append(ln)
            if ln.rstrip() == 'end': in_mut[0] = False; close()
            continue
        if depth > 0 or ln.startswith('/-') and not ln.startswith('/--') and False:
            pass
        # block comments
        if depth == 0 and (ln.startswith('/-')):
            close(); pending = [ln]; depth = ln.count('/-') - ln.count('-/')
            while depth > 0 and i < len(lines):
                l2 = lines[i]; i += 1; pending.append(l2)
                depth += l2.count('/-') - l2.count('-/')
            if depth == 0 and pending and pending[-1].rstrip().endswith('-/') is False:
                pass
            continue
        if depth > 0:
            continue
        if ln.strip() == '':
            continue
        if ln.startswith('--'):
            m = re.match(r'-- frontx_ind (\S+) on', ln)
            if m:
                close(); items.append(dict(kind='target', name=m.group(1), frames=ctx(), line=i))
            continue
        if ln[0] in ' \t':
            if cur is not None: cur['body'].append(ln)
            continue
        # top-level command
        w = ln.split()
        head = w[0]
        if head == 'namespace':
            close(); frames.append(('namespace', w[1], [])); pending = []; continue
        if head == 'section':
            close(); frames.append(('section', '', [])); pending = []; continue
        if head == 'end':
            close(); frames.pop(); pending = []; continue
        if head in ('open', 'variable') and frames:
            close(); frames[-1][2].append(ln); pending = []; continue
        if head in ('open', 'variable', 'universe') and not frames:
            close(); glob.append(ln); continue
        if head == 'set_option' and ln.rstrip().endswith(' in'):
            close(); pending = [ln]; continue
        if head == 'set_option':
            close(); (frames[-1][2] if frames else glob).append(ln); continue
        if head.startswith('#'):
            close(); pending = []; continue
        attrs = []
        if head.startswith('@['):
            attrs.append(ln); k = i
        # strip attribute prefix
        s = ln
        if s.startswith('@['):
            s = s[s.index(']') + 1:].strip()
            if not s: # attribute alone on its line
                close(); pending.append(ln); continue
        toks = s.split()
        while toks and toks[0] in MODS: toks = toks[1:]
        if toks and toks[0] == 'mutual':
            close(); it = dict(kind='mutual', name=None, pre=list(pending), header=ln, body=[ln], frames=ctx())
            items.append(it); cur = it; pending = []; in_mut[0] = True; continue
        if toks and toks[0] in KW:
            close()
            name = toks[1] if len(toks) > 1 and toks[0] not in ('mutual', 'instance') else None
            if toks[0] == 'instance' and len(toks) > 1 and ':' in toks[1:][0:1]: name = None
            it = dict(kind=toks[0], name=name, pre=list(pending), header=ln, body=[ln], frames=ctx())
            items.append(it); cur = it; pending = []
            continue
        # other col-0 text: continuation of current item, or its own item
        if cur is not None:
            cur['body'].append(ln)
        else:
            it = dict(kind='other', name=None, pre=list(pending), header=ln, body=[ln], frames=ctx())
            items.append(it); cur = it; pending = []
    return items, glob

def fqn_of(it):
    ns = [f[1] for f in it['frames'] if f[0] == 'namespace']
    nm = it.get('name')
    if nm is None: return None
    return '.'.join(ns + [nm]) if ns else nm

def ns_str(it):
    return '.'.join(f[1] for f in it['frames'] if f[0] == 'namespace')

if __name__ == '__main__':
    items, glob = parse(sys.argv[1])
    from collections import Counter
    print(Counter(i['kind'] for i in items), len(items))

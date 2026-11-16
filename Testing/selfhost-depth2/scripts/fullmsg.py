import re
def full(path,fname):
    src=open(path).read().split('\n')
    out={}; cur=None; buf=[]
    pat=re.compile(r'[^:\s]*\.lean:(\d+):\d+: (error|warning|info)')
    for l in src:
        m=pat.search(l)
        if m:
            if cur is not None: out[cur]=' '.join(buf)
            cur=int(m.group(1)) if m.group(2)=='error' else None
            buf=[l[m.end():].lstrip(': ')] if cur is not None else []
        elif cur is not None and (l.startswith(' ') or l.strip()):
            buf.append(l.strip())
        elif cur is not None and not l.strip():
            pass
    if cur is not None: out[cur]=' '.join(buf)
    for k in list(out):
        out.setdefault(k,'')
    return out

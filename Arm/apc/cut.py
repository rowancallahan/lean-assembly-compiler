# stage helper: drop the paragraphs (blank-line separated) that hold a target-specific theorem
# (`theorem X_wf`, `theorem X_implements`) and `open LeanRV64D ...` lines; rewrite imports.  Usage:
#   python3 cut.py IN OUT 'old-import=>new-import' ...
import re, sys
src, out, *subs = sys.argv[1:]
text = open(src).read()
for s in subs:
    a, b = s.split('=>')
    text = text.replace('import ' + a + '\n', ('import ' + b + '\n') if b else '')
paras = text.split('\n\n')
keep = [p for p in paras if not re.search(r'^theorem \w+_(wf|implements) ', p, re.M)]
text = '\n\n'.join(keep)
text = '\n'.join(l for l in text.split('\n') if not l.startswith('open LeanRV64D'))
open(out, 'w').write(text if text.endswith('\n') else text + '\n')

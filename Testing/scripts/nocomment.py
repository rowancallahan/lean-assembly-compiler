"""Print `file:line: text` for forbidden words in Lean sources, ignoring comments and string literals."""
import re, sys
BAD = re.compile(r'\bsorry\b|native_decide|bv_decide|^\s*axiom\b|\bsorryAx\b')
for path in sys.argv[1:]:
    src = open(path).read(); out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(src[i]); i += 1
    for k, line in enumerate(''.join(out).split('\n'), 1):
        if BAD.search(line): print(f"{path}:{k}: {line.strip()}")

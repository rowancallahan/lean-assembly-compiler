# Rewrite every nested action `(← do S)` to `(← (do S))` in the given .lean files, in place.
# Lean 4.34 parses `do S` after `←` as a do-element; the legacy `do` elaborator accepts only a term there.
# Parenthesizing makes it the term `(do S)`, which elaborates exactly like `do S` did on 4.29.
# Prints the number of rewritten sites per file. Fails on anything it does not understand.
import sys

OPEN = "(← do"

def matching_close(s, i):
    """s[i] == '('; return the index of its matching ')', skipping strings, chars and comments."""
    assert s[i] == "("
    depth, j, n = 0, i, len(s)
    while j < n:
        c = s[j]
        if c == '"':
            j += 1
            while s[j] != '"':
                j += 2 if s[j] == "\\" else 1
        elif s.startswith("--", j):
            j = s.index("\n", j)
        elif s.startswith("/-", j):
            d = 0
            while True:
                if s.startswith("/-", j): d += 1; j += 2
                elif s.startswith("-/", j):
                    d -= 1; j += 2
                    if d == 0: break
                else: j += 1
            continue
        elif c == "'" and j + 2 < n and s[j + 2] == "'" and s[j + 1] != "\\":
            j += 2  # char literal like '('
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise AssertionError(f"unbalanced paren at {i}")

for path in sys.argv[1:]:
    s = open(path).read()
    assert "(← (do" not in s, f"{path}: already patched"
    sites, k = [], s.find(OPEN)
    while k != -1:
        # `do` must be a whole word
        assert not (s[k + len(OPEN)].isalnum() or s[k + len(OPEN)] in "_'"), (path, k)
        sites.append((k, matching_close(s, k)))
        k = s.find(OPEN, k + 1)
    ins = []  # (position, text)
    for (a, b) in sites:
        ins.append((a + len("(← "), "("))
        ins.append((b, ")"))
    out, prev = [], 0
    for pos, t in sorted(ins, key=lambda p: p[0]):
        out += [s[prev:pos], t]
        prev = pos
    s = "".join(out) + s[prev:]
    assert s.count("(← (do") == len(sites) and OPEN not in s
    open(path, "w").write(s)
    if sites:
        print(f"{path}\t{len(sites)}")

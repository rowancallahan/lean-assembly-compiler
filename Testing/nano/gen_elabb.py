"""Generates the two step macros of Nano/ElabB.lean from Testing/nano/elabb_step.tmpl (STEPN: a byte `c` with a next
byte `n` = @N) and Testing/nano/elabb_end.tmpl (STEPE: the last byte).  REC(st, sp, d, d0, w, ty) is the recursive
call on the rest (STEPN) or the end of the pass (STEPE)."""
import re, sys
TN = open(sys.argv[1]).read()
TE = open(sys.argv[2]).read()
def args(s, i):  # s[i] == '(' ; split top-level commas
    depth, cur, out = 0, '', []
    j = i
    while True:
        ch = s[j]
        if ch == '(':
            depth += 1
            if depth == 1: j += 1; continue
        elif ch == ')':
            depth -= 1
            if depth == 0: out.append(cur.strip()); return out, j + 1
        elif ch == ',' and depth == 1:
            out.append(cur.strip()); cur = ''; j += 1; continue
        cur += ch; j += 1
def expand(s, end):
    s = s.replace('@N', 'n')
    out, i = '', 0
    while True:
        k = s.find('REC(', i)
        if k < 0: return out + s[i:]
        a, j = args(s, k + 3)
        assert len(a) == 6, a
        def w(x): return x if re.fullmatch(r'[\w.]+', x) else '(' + x + ')' if not x.startswith('(') else x
        if end:
            ty = w(a[5])
            pre = s[max(0, k - 30):k]
            fin0 = f'(if {ty} == 0 then [0] else ({ty}).toUInt8 :: lx o o 1 0 0 0 0 0 {ty})'
            if pre.endswith('if m == 0 then '):   # pass 1 known: no second test of `m`
                r = fin0
            elif re.search(r'else [^()]*:: $', pre) or pre.endswith(':: '):  # pass 2 known
                r = '[]'
            else:
                r = f'(if m == 0 then {fin0} else [])'
        else:
            r = '(lx (n :: t) o m ' + ' '.join(w(x) for x in a) + ')'
        out += s[i:k] + r; i = j
for name, end in (('STEPN', False), ('STEPE', True)):
    print('set_option hygiene false in')
    print(f'macro "{name}" : term => `(')
    print(expand(TE if end else TN, end).rstrip() + ')')
    print()

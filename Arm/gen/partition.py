#!/usr/bin/env python3
"""Partition the generated ARM model into a core layer and the rest (ARM_FAST.md, option A1 + option 4).

usage: partition.py SRC OUT PROOFS [PART_LINES]
  SRC     generated model (lake project: lakefile.toml, Armv9.lean, Armv9/*.lean)
  OUT     new lake project to write (must not exist)
  PROOFS  Arm/proofs/Arm (model names used by the core proof files become roots)

Every declaration is moved as verbatim text; nothing is renamed and no namespace changes.
  * core: for every module M that imports Armv9.V8Base, the declarations of M reachable from ROOTS (closure stops at
    `__Decode*`), in original order, as module Armv9Core.M. Modules not above V8Base are shared unchanged.
  * rest: Armv9.M keeps M's other declarations in original order and imports Armv9Core.M.
  * a rest over SPLIT_MIN lines (V8Base, SysregsAutogen, Instrs*, DecodeEnd) is cut into Armv9.M.P<i> along its
    dependency graph; Armv9.M then only imports its parts, so every importer of Armv9.M is unchanged.
The full model is core ∪ rest: the same constants under the same names. check_hashes.lean compares it with an
unpartitioned build. Anything wrong in the cut is a compile error or a hash difference, never silent.
"""
import os, re, shutil, sys
from collections import defaultdict, deque

SRC, OUT, PROOFS = sys.argv[1], sys.argv[2], sys.argv[3]
PART_LINES = int(sys.argv[4]) if len(sys.argv) > 4 else 12000  # target lines per part
SPLIT_MIN = 20000  # split a module's rest when it has more lines than this
BIG = 500          # a declaration this long gets its own part
assert not os.path.exists(OUT), OUT

INSTRS = """movz_aarch64_instrs_integer_ins_ext_insert_movewide movk_aarch64_instrs_integer_ins_ext_insert_movewide
add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate
subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
and_log_shift_aarch64_instrs_integer_logical_shiftedreg orr_log_shift_aarch64_instrs_integer_logical_shiftedreg
eor_log_shift_aarch64_instrs_integer_logical_shiftedreg lslv_aarch64_instrs_integer_shift_variable
lsrv_aarch64_instrs_integer_shift_variable asrv_aarch64_instrs_integer_shift_variable
madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub csinc_aarch64_instrs_integer_conditional_select
csel_aarch64_instrs_integer_conditional_select b_uncond_aarch64_instrs_branch_unconditional_immediate
bl_aarch64_instrs_branch_unconditional_immediate b_cond_aarch64_instrs_branch_conditional_cond
cbz_aarch64_instrs_branch_conditional_compare cbnz_aarch64_instrs_branch_conditional_compare
br_aarch64_instrs_branch_unconditional_register blr_aarch64_instrs_branch_unconditional_register
ret_aarch64_instrs_branch_unconditional_register
ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal""".split()
assert len(INSTRS) == 39 == len(set(INSTRS))
ROOTS = ["decode_" + i for i in INSTRS] + ["__FetchInstr", "__CycleEnd"]
PROOF_FILES = "Base Exec Flags Hooks Fetch Mem Branch BrFull Ret".split()
START = re.compile(r"(/--|def |partial def )")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

def tokens(text):
    out = set()
    for t in IDENT.findall(text):
        ps = t.split(".")
        out.update(".".join(ps[i:j]) for i in range(len(ps)) for j in range(i + 1, len(ps) + 1))
    return out

def parse(path):
    """-> (import lines, other header lines, [(name, text)], footer lines). Every line lands in exactly one part."""
    lines = open(path).read().split("\n")
    assert lines[-1] == "", path
    lines = lines[:-1]
    i = 0
    while i < len(lines) and not START.match(lines[i]): i += 1
    head = lines[:i]
    imports = [l for l in head if l.startswith("import ")]
    other = [l for l in head if not l.startswith("import ")]
    assert head[:len(imports)] == imports, path
    j = len(lines)
    while j > i and (lines[j - 1].startswith("end ") or lines[j - 1] == ""): j -= 1
    foot = lines[j:]
    assert all(l == "" or l.startswith("end ") for l in foot)
    chunks, cur = [], None
    k = i
    while k < j:
        l = lines[k]
        if START.match(l):
            if cur: chunks.append(cur)
            cur = [None, []]
            if l.startswith("/--"):
                while "-/" not in lines[k]:
                    cur[1].append(lines[k]); k += 1
                cur[1].append(lines[k]); k += 1
                l = lines[k]
            m = re.match(r"(?:partial )?def ([^ (:]+)", l)
            assert m, (path, k, l)
            cur[0] = m.group(1)
        cur[1].append(l); k += 1
    if cur: chunks.append(cur)
    assert all(c[0] for c in chunks), path
    n = len(imports) + len(other) + sum(len(c[1]) for c in chunks) + len(foot)
    assert n == len(lines), (path, n, len(lines))
    return imports, other, [(c[0], "\n".join(c[1])) for c in chunks], foot

def modname(rel):  # "Armv9/V8Base.lean" -> "Armv9.V8Base"
    return rel[:-5].replace("/", ".")

files = ["Armv9.lean"] + sorted("Armv9/" + f for f in os.listdir(os.path.join(SRC, "Armv9")) if f.endswith(".lean"))
imp = {modname(f): [l.split()[1] for l in open(os.path.join(SRC, f)) if l.startswith("import ")] for f in files}

# A = modules at or above V8Base: these get split.
above = {"Armv9.V8Base"}
changed = True
while changed:
    changed = False
    for m in imp:
        if m not in above and any(i in above for i in imp[m]): above.add(m); changed = True
mods = {m: parse(os.path.join(SRC, m.replace(".", "/") + ".lean")) for m in above}
assert all(imp[m] == [l.split()[1] for l in mods[m][0]] for m in above)
anc = {}
def ancestors(m):
    if m not in anc:
        s = set()
        for i in imp[m]:
            if i in imp: s |= {i} | ancestors(i)
        anc[m] = s
    return anc[m]

where, text = {}, {}
for m in mods:
    for n, t in mods[m][2]:
        assert n not in where, ("duplicate", n)
        where[n], text[n] = m, t
names = {n for n in where if where[n] in above}
deps = {n: (tokens(text[n]) & names) - {n} for n in names}
rdeps = defaultdict(set)
for n, ds in deps.items():
    for d in ds: rdeps[d].add(n)

assert "partial def Reduce__1 " in "\n".join(text[n] for n in names if where[n] == "Armv9.V8Base"), "Reduce__1 not partial"
stops = {n for n in names if n.startswith("__Decode")}
assert "__DecodeA64" in stops
dec = set(stops); q = deque(stops)
while q:
    for r in rdeps[q.popleft()]:
        if r not in dec: dec.add(r); q.append(r)
proof_names = set()
for f in PROOF_FILES:
    proof_names |= tokens(open(os.path.join(PROOFS, f + ".lean")).read()) & names
for r in ROOTS: assert r in names and r not in dec, r
dropped = sorted(proof_names & dec)
roots = (set(ROOTS) | proof_names) - dec
core = set(roots); q = deque(roots)
while q:
    for d in deps[q.popleft()]:
        if d not in core: core.add(d); q.append(d)
assert not (core & dec) and "Reduce__1" not in core

def core_name(m): return "Armv9Core." + (m[len("Armv9."):] if m != "Armv9" else "Root")
def path_of(m): return os.path.join(OUT, m.replace(".", "/") + ".lean")
def write(m, imports, other, chunks, foot):
    os.makedirs(os.path.dirname(path_of(m)), exist_ok=True)
    body = ["import " + i for i in imports] + other + [t for _, t in chunks] + foot
    open(path_of(m), "w").write("\n".join(body) + "\n")

shutil.copytree(SRC, OUT, ignore=shutil.ignore_patterns(".lake", ".git"))
has_core = {m for m in above if any(n in core for n, _ in mods[m][2])}
stats = []
for m in sorted(above):
    imports, other, chunks, foot = mods[m]
    c = [x for x in chunks if x[0] in core]
    r = [x for x in chunks if x[0] not in core]
    if c:
        ci = [i for i in imp[m] if i not in above] + [core_name(a) for a in sorted(ancestors(m) & has_core)]
        write(core_name(m), ci, other, c, foot)
    ri = imp[m] + ([core_name(m)] if c else [])
    stats.append((m, len(c), sum(t.count("\n") + 1 for _, t in c), len(r), sum(t.count("\n") + 1 for _, t in r)))
    nl = lambda n: text[n].count("\n") + 1
    if sum(nl(n) for n, _ in r) <= SPLIT_MIN:
        write(m, ri, other, r, foot)
        continue
    # (b) split a large rest along its dependency graph: depth = longest dependency path inside the rest. Sorting by
    # (depth, original position) is a topological order; a declaration of BIG lines or more gets a part of its own.
    rest = [n for n, _ in r]
    rs = set(rest)
    depth = {}
    for n in rest:  # file order is topological (no forward references, no mutual blocks)
        assert all(d in depth for d in deps[n] & rs), ("forward reference", n)
        depth[n] = 1 + max((depth[d] for d in deps[n] & rs), default=-1)
    order = sorted(range(len(rest)), key=lambda i: (depth[rest[i]], i))
    parts, cur, size, big = [], [], 0, []  # big: solo parts waiting to be emitted after cur
    def flush():
        global cur, size, big
        if cur: parts.append(cur)
        parts.extend([b] for b in big)
        cur, size, big = [], 0, []
    for i in order:
        n = rest[i]
        if nl(n) >= BIG: big.append(n); continue
        if (cur and size + nl(n) > PART_LINES) or deps[n] & set(big): flush()
        cur.append(n); size += nl(n)
    flush()
    part_of = {n: p for p, ns in enumerate(parts) for n in ns}
    pnames = [f"{m}.P{p:02d}" for p in range(len(parts))]
    for p, ns in enumerate(parts):
        need = sorted({part_of[d] for n in ns for d in deps[n] & rs} - {p})
        assert all(x < p for x in need)
        write(pnames[p], ri + [pnames[x] for x in need], other, [(n, text[n]) for n in ns], foot)
        stats.append((pnames[p], 0, 0, len(ns), sum(nl(n) for n in ns), [pnames[x][-3:] for x in need]))
    write(m, ri + pnames, other, [], foot)

lf = os.path.join(OUT, "lakefile.toml")
s = open(lf).read()
assert s.count("[[lean_lib]]") == 1 and 'name = "Armv9"\n' in s
s = s.replace('defaultTargets = ["Armv9"]', 'defaultTargets = ["Armv9Core"]')
s = s.replace('[[lean_lib]]\nname = "Armv9"\n', '[[lean_lib]]\nname = "Armv9"\nglobs = ["Armv9", "Armv9.+"]\n')
s += '\n[[lean_lib]]\nname = "Armv9Core"\nglobs = ["Armv9Core.+"]\nleanOptions.weak.linter.style.nameCheck = false\nmoreLeancArgs= ["-fbracket-depth=500"]\n'
open(lf, "w").write(s)

# Verbatim check: re-read every written module; the declarations must be exactly the originals, each once.
back = {}
for d, _, fs in os.walk(OUT):
    for f in fs:
        if ".lake" in d or not f.endswith(".lean"): continue
        m = os.path.relpath(os.path.join(d, f), OUT)[:-5].replace("/", ".")
        if m in above or m.startswith("Armv9Core.") or re.fullmatch(r"Armv9\.\w+\.P\d+", m) is not None:
            for n, t in parse(os.path.join(d, f))[2]:
                assert n not in back, ("twice", n)
                back[n] = t
orig = {n: text[n] for n in names}
bad = [n for n in orig if (back.get(n) or "").rstrip("\n") != orig[n].rstrip("\n")]  # a chunk that ends a file loses its blank lines to the footer
assert set(back) == set(orig) and not bad, ("declaration text changed", bad[:5], len(bad))
hits = [os.path.join(d, f) for d, _, fs in os.walk(OUT) if ".lake" not in d for f in fs
        if f.endswith(".lean") and "partial def Reduce__1 " in open(os.path.join(d, f)).read()]
assert len(hits) == 1, ("partial def Reduce__1 must be in the output exactly once", hits)
print(f"roots {len(roots)} (proof names {len(proof_names)}, dropped as decoder-dependent: {' '.join(dropped)})")
print(f"core {len(core)} decls; above-V8Base decls {len(names)}")
for st in stats: print(*st)

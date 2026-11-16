"""Inputs for nanoElabB tests: corpus, boundary-fuzz mutations, prefixes/suffixes, random bytes, edge cases.
Usage: elabb_inputs.py N SEED -> prints one input per line as a Python bytes repr list (JSON array of ints)."""
import sys, os, re, json, random
D = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, D)
from nanolib import CORPUS
try:
    from nanolib import INT_CORPUS
except ImportError:
    INT_CORPUS = []
N = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
NAMES = ["id", "at", "fun", "if", "by", "end", "cast", "Type", "_", "x_", "xA", "max", "not", "and", "or", "abc4", "a_b",
         "sq_1", "do", "ite", "bif", "mt", "bne", "in", "let", "def", "for", "mut", "try", "x1", "zz9", "q_12", "Int64", "UInt64",
         "get", "abcd", "x__1", "x_1_2", "a1b", "UInt64x", "Int6", "deff", "lets", "rfl", "xor", "set", "min"]
INS = ["-", "--", "- -", "(", ")", "\t", "\r", "\r\n", " -5", "-5", "0x1", "1e3", "1_000", ";", ":=", "let", "UInt64",
       "Int64", "_", "+", "*", "-- c\n", " - 7", "(-3)", "--5", "x", "\n", "007", "18446744073709551616", "-0", ":", "=",
       ")(", ")x", "x(", "5(", "é", "\x00", "UInt64x"]
def tokens(s): return re.findall(r"\s+|\w+|:=|--|.", s)
def mutate(s):
    k = rng.randrange(6); t = tokens(s)
    if k == 0:
        ids = sorted({x for x in t if re.fullmatch(r"[a-z]\w*", x) and x not in ("def", "let")})
        if ids: return re.sub(rf"\b{rng.choice(ids)}\b", rng.choice(NAMES), s)
    if k in (1, 2):
        i = rng.randrange(len(t) + 1); return "".join(t[:i] + [rng.choice(INS)] + t[i:])
    if k == 3 and len(t) > 1:
        i = rng.randrange(len(t)); return "".join(t[:i] + t[i + 1:])
    if k == 4:
        occ = [m.start() for m in re.finditer(r"\bU?Int64\b", s)]
        if occ:
            o = rng.choice(occ); w = "Int64" if s[o] == "U" else "UInt64"; e = re.match(r"U?Int64", s[o:]).end()
            return s[:o] + w + s[o + e:]
    return s.replace(" ", rng.choice(["", "  ", "\t", "\r\n", "\n", "\n "]), 1)
EDGE = ["", " ", "abc", "ab", "a", "deff", "def", "UInt64", "(UInt64", "UInt64x", "x UInt64", "123", "12", "1", "(123",
        "( abc", "(ab1", "((x1", "Int64", "def f : UInt64 := 12", "def f : UInt64 := 1", "def f : UInt64 := xyz",
        "def f : Int64 := 5", "def f : UInt64 := ((1))", "def f (x : UInt64) : Int64 := x", "\r\n", "\r", "x\r",
        "def f : UInt64 := 1\r\n", "def f : UInt64 := 1 --", "-", ":", ":=", "a:=", "( :=", "(abcdefgh", "(abcdefg",
        "(UInt645", "(xyz9", "(x_", "(x_1", "+x1", "+12", "+1", "(1)2", "(a)b", "a(b", "1a", "1(", "1_0", ";def",
        "(12a", "(1a2", "\ndef", "\ndeff", "(\ndef", "def f : UInt64 := 1\ndef g : UInt64 := f", "def f : UInt64 := 1\nx",
        "def f : UInt64 := 1\n def g : UInt64 := f", "def f : UInt64 :=\n 1", "def f : UInt64 :=\n1", "\n\n def", "( x)(y",
        "x_1 y_2", "a__", "_a", "A1", "def f (x : UInt64) : UInt64 := x_1", "( 0123", "(00", "(UInt64)"]
outs = []
for s in CORPUS + INT_CORPUS: outs.append(s); outs.append(s + "\n")
outs += EDGE
for s in CORPUS[:12]:
    for k in range(1, len(s), 3): outs.append(s[:k])
while len(outs) < N:
    r = rng.random()
    if r < .6:
        m = rng.choice(CORPUS + INT_CORPUS)
        for _ in range(rng.choice([1, 1, 2, 3])): m = mutate(m)
        outs.append(m)
    elif r < .8:
        outs.append("".join(rng.choice("ab_1(): =+-*;\n\rUInt64deflx") for _ in range(rng.randrange(1, 12))))
    else:
        outs.append(bytes(rng.randrange(256) for _ in range(rng.randrange(0, 10))))
for o in outs[:N]:
    b = o if isinstance(o, bytes) else o.encode()
    print(" ".join(["L"] + [str(x) for x in b]))

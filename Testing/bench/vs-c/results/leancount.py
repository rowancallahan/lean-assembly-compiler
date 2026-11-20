import subprocess, re, sys, json
def ir(f, n):
    o = subprocess.run(f"valgrind --tool=callgrind --callgrind-out-file=/dev/null ./lb {f} {n}", shell=True, capture_output=True, text=True).stderr
    return int(re.search(r"Collected : (\d+)", o).group(1))
res = {}
for f, sizes in [("msort", [100, 1000, 100000]), ("insertion", [100, 1000, 10000]), ("sum", [100, 1000, 100000]), ("take", [100,1000,100000]), ("inc", [100,1000,100000]), ("gcd", [0]), ("loopsum", [100, 1000, 100000])]:
    for n in sizes:
        d = ir(f, n) - ir("none", n); res[f"{f}/{n}"] = d
        print(f, n, d, round(d / max(n, 1), 1), flush=True)
json.dump(res, open("lean_results.json", "w"))

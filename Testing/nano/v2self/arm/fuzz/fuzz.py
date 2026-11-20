# fuzz.py WORKDIR [FIRST_SEED] [COUNT]: differential fuzzer, RISC-V (nanorun) vs AArch64 (qemu shim_arm via rv2arm.sh).
# UNPROVEN test tool. Needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64-static, python3. Failures go to WORKDIR/fail/<seed>/.
# Per program: B2 compiles (nanorun); rv2arm.sh translates (checked against rv2arm.py); each input runs under nanorun
# and under qemu shim_arm; status and output bytes must agree. Negative statuses (−1, −2) compare status only.
import os, re, subprocess, sys, time, random, shutil, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gen
ARM = os.path.dirname(HERE); V2 = os.path.dirname(ARM)
B2 = os.path.join(V2, "B2.bin"); RV2ARM = os.path.join(ARM, "rv2arm.sh"); ORACLE = os.path.join(ARM, "rv2arm.py")
TRANS = os.path.join(ARM, "rv2arm_arm.bin")
W = os.path.abspath(sys.argv[1]); os.makedirs(W + "/fail", exist_ok=True)
FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 1
COUNT = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
NANORUN, SHIM, SHIM_RV = W + "/nanorun", W + "/shim_arm", W + "/shim_rv"
QEMU, QEMU_RV = "qemu-aarch64-static", "qemu-riscv64-static"
LOG = open(W + "/log.txt", "a")

def build():
    subprocess.run(["cc", "-O2", os.path.join(V2, "run/nanorun.c"), "-o", NANORUN], check=True)
    subprocess.run(["aarch64-linux-gnu-gcc", "-O2", "-static", os.path.join(V2, "run/shim/shim_arm.c"), "-o", SHIM], check=True)
    subprocess.run(["riscv64-linux-gnu-gcc", "-O2", "-static", os.path.join(V2, "run/shim/shim_rv.c"), "-o", SHIM_RV], check=True)

def run(args, timeout, env=None, stdin=None, stdout=None):
    t = time.time()
    try:
        p = subprocess.run(args, timeout=timeout, env=env, stdin=stdin, stdout=stdout, stderr=subprocess.PIPE)
        return p.returncode, p.stderr.decode(errors="replace"), time.time() - t
    except subprocess.TimeoutExpired:
        return "TIMEOUT", "", time.time() - t

def inputs(rng):
    yield "empty", b""
    yield "one", bytes([rng.randrange(256)])
    n = int(10 ** rng.uniform(1, 5.3))            # log-uniform up to ~200 KB
    yield "rand%d" % n, os.urandom(min(n, 200000))

def fail(seed, src, why, extra):
    d = os.path.join(W, "fail", str(seed)); os.makedirs(d, exist_ok=True)
    open(d + "/prog.src", "w").write(src)
    open(d + "/REPORT.txt", "w").write(why + "\n" + extra + "\n")
    for f in ("prog.rv", "prog.arm"):
        if os.path.exists(W + "/cur/" + f): shutil.copy(W + "/cur/" + f, d)
    for f in os.listdir(W + "/cur"):
        if f.startswith("in_"): shutil.copy(W + "/cur/" + f, d)
    print("FAIL seed %d: %s" % (seed, why), file=LOG, flush=True)

def run_shim(qemu, shim, code, ip, out):
    # run a code file under a shim (qemu) on input ip; returns (status or None, output bytes or None, why)
    with open(ip, "rb") as fi, open(out, "wb") as fo:
        rc, e, _ = run([qemu, shim, code], 60, stdin=fi, stdout=fo)
    if rc == "TIMEOUT": return None, None, "HANG"
    m = re.search(r"status (-?\d+)", e)
    if not m or rc not in (0, 1): return None, None, "rc=%s %s" % (rc, e.strip())
    return int(m.group(1)), open(out, "rb").read(), ""

def one(seed, stats):
    rng = random.Random(seed * 7919 + 1)
    src = gen.gen(seed)
    cur = W + "/cur"; os.makedirs(cur, exist_ok=True)
    for f in os.listdir(cur): os.remove(os.path.join(cur, f))
    open(cur + "/prog.src", "w").write(src)
    # reference compile: RISC-V shim under qemu (nanorun must give the same code)
    with open(cur + "/prog.src", "rb") as fi, open(cur + "/prog.rv", "wb") as fo:
        rc, err, _ = run([QEMU_RV, SHIM_RV, B2], 300, stdin=fi, stdout=fo)
    if rc != 0 or os.path.getsize(cur + "/prog.rv") == 0:
        stats["reject"] += 1
        return fail(seed, src, "B2 compile under qemu-riscv: rc=%s %s" % (rc, err.strip()), "empty code")
    rc, err, _ = run([NANORUN, B2, cur + "/prog.src", cur + "/nano.rv"], 120)
    if rc != 0 or open(cur + "/nano.rv", "rb").read() != open(cur + "/prog.rv", "rb").read():
        return fail(seed, src, "compile: nanorun code != qemu-riscv code", "")
    stats["programs"] += 1
    env = dict(os.environ, RUN="%s %s %s" % (QEMU, SHIM, TRANS))
    rc, err, _ = run([RV2ARM, cur + "/prog.rv"], 300, env=env, stdout=open(cur + "/prog.arm", "wb"))
    if rc != 0:
        return fail(seed, src, "rv2arm.sh rc=%s (translator refused valid compiler output)" % rc, err)
    rc, _, _ = run(["python3", ORACLE, cur + "/prog.rv"], 300, stdout=open(cur + "/oracle.arm", "wb"))
    if rc != 0 or open(cur + "/oracle.arm", "rb").read() != open(cur + "/prog.arm", "rb").read():
        return fail(seed, src, "translator != rv2arm.py oracle", "")
    for name, data in inputs(rng):
        ip = cur + "/in_" + name
        open(ip, "wb").write(data)
        s_rv, out_rv, why = run_shim(QEMU_RV, SHIM_RV, cur + "/prog.rv", ip, cur + "/o.rv")
        if why: return fail(seed, src, "RISC-V qemu shim on %s: %s" % (name, why), "")
        s_arm, out_arm, why = run_shim(QEMU, SHIM, cur + "/prog.arm", ip, cur + "/o.arm")
        if why: return fail(seed, src, "AArch64 qemu shim on %s: %s" % (name, why), "")
        rc, rerr, _ = run([NANORUN, cur + "/prog.rv", ip, cur + "/n.rv"], 60)
        if rc == "TIMEOUT": return fail(seed, src, "HANG nanorun (third opinion) on %s" % name, "")
        m1 = re.search(r"a0 = (-?\d+)", rerr)
        s_nano = int(m1.group(1)) if m1 else None
        out_nano = open(cur + "/n.rv", "rb").read() if s_nano in (0, 1) and os.path.exists(cur + "/n.rv") else b""
        if os.path.exists(cur + "/n.rv"): os.remove(cur + "/n.rv")
        stats["status_%d" % s_rv] += 1; stats["inputs"] += 1
        if s_rv != s_arm or out_rv != out_arm:
            return fail(seed, src, "MISMATCH rv(qemu) vs arm(qemu) on input %s: rv status %d (%d B), arm status %d (%d B)"
                        % (name, s_rv, len(out_rv), s_arm, len(out_arm)), "rv_out=%s\narm_out=%s"
                        % (out_rv[:64].hex(), out_arm[:64].hex()))
        if s_nano != s_rv or out_nano != out_rv:
            stats["nanorun_disagree"] += 1
            return fail(seed, src, "nanorun (third opinion) disagrees with qemu-riscv on %s: qemu %s/%dB, nanorun %s/%dB"
                        % (name, s_rv, len(out_rv), s_nano, len(out_nano)), "")
        print("ok seed %d %s len %d status %d out %d" % (seed, name, len(data), s_rv, len(out_rv)), file=LOG, flush=True)
        if s_rv not in (0, 1): break   # later inputs of a failed-capacity program add nothing new

if __name__ == "__main__":
    build()
    stats = collections.Counter(); t0 = last = time.time()
    for seed in range(FIRST, FIRST + COUNT):
        try:
            one(seed, stats)
        except Exception as e:
            fail(seed, gen.gen(seed), "driver exception: %r" % e, "")
        if time.time() - last > 1800:
            last = time.time()
            print("SUMMARY %s h: seed %d, programs %d, rejects %d, inputs %d, statuses %s" %
                  (round((time.time() - t0) / 3600, 2), seed, stats["programs"], stats["reject"], stats["inputs"],
                   {k: v for k, v in stats.items() if k.startswith("status_")}), file=LOG, flush=True)

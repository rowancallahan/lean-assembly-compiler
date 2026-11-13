#!/usr/bin/env python3
"""Writes Arm/Words.lean: for every word `Proven/CompilerArm.lean` (`Arm.gen` for depth < 11, plus `iRes`) emits,
  dec_<w>  : `__DecodeA64` dispatches it to the right decode function (SEE < 1),
  word_<w> : L1, decode+execute result with explicit register updates,
  step_<w> : L2, the model agrees with `armStep` (`Step`),
the list `emitted` of all these words and `armStep_ok`. Keep T and the encodings in sync with CompilerArm.lean.
usage: python3 gen/gen_words.py [maxk] > Arm/Words.lean"""
import sys
T = [9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7]; N = len(T)
MAXK = int(sys.argv[1]) if len(sys.argv) > 1 else N
rrr = lambda base, d, n, m: base | m << 16 | n << 5 | d
DEC = {  # family: (decode function, args template, SEE value)
    "add": ("decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg", "{d}#5 {n}#5 0#6 {m}#5 0#2 0#1 0#1 1#1", 14),
    "sub": ("decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg", "{d}#5 {n}#5 0#6 {m}#5 0#2 0#1 1#1 1#1", 16),
    "and": ("decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg", "{d}#5 {n}#5 0#6 {m}#5 0#1 0#2 0#2 1#1", 48),
    "orr": ("decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg", "{d}#5 {n}#5 0#6 {m}#5 0#1 0#2 1#2 1#1", 55),
    "eor": ("decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg", "{d}#5 {n}#5 0#6 {m}#5 0#1 0#2 2#2 1#1", 53),
    "lslv": ("decode_lslv_aarch64_instrs_integer_shift_variable", "{d}#5 {n}#5 0#2 {m}#5 1#1", 57),
    "lsrv": ("decode_lsrv_aarch64_instrs_integer_shift_variable", "{d}#5 {n}#5 1#2 {m}#5 1#1", 58),
    "asrv": ("decode_asrv_aarch64_instrs_integer_shift_variable", "{d}#5 {n}#5 2#2 {m}#5 1#1", 56),
    "cmp": ("decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg", "31#5 {n}#5 0#6 {m}#5 0#2 1#1 1#1 1#1", 17),
    "cset_lo": ("decode_csinc_aarch64_instrs_integer_conditional_select", "{d}#5 31#5 1#1 2#4 31#5 0#1 1#1", 188),
    "cset_lt": ("decode_csinc_aarch64_instrs_integer_conditional_select", "{d}#5 31#5 1#1 10#4 31#5 0#1 1#1", 188),
    "cset_eq": ("decode_csinc_aarch64_instrs_integer_conditional_select", "{d}#5 31#5 1#1 1#4 31#5 0#1 1#1", 188),
    "cmp0": ("decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate", "31#5 {n}#5 0#12 0#1 1#1 1#1 1#1", 21),
    "csel": ("decode_csel_aarch64_instrs_integer_conditional_select", "{d}#5 {n}#5 0#1 1#4 {m}#5 0#1 1#1", 187),
    "movz": ("decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide", "{d}#5 0#16 0#2 2#2 1#1", 698),
    "inc": ("decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate", "{d}#5 {n}#5 1#12 0#1 0#1 0#1 1#1", 18),
    "mov": ("decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg", "{d}#5 31#5 0#6 {m}#5 0#1 0#2 1#2 1#1", 55),
}
# exec lemma, value (for L1), which registers are read
EXEC = {"add": ("add_exec", "a + b"), "sub": ("sub_exec", "a - b"), "and": ("and_exec", "a &&& b"),
        "orr": ("orr_exec", "a ||| b"), "eor": ("eor_exec", "a ^^^ b"), "lslv": ("lslv_exec", "a <<< (b.toNat % 64)"),
        "lsrv": ("lsrv_exec", "a >>> (b.toNat % 64)"), "asrv": ("asrv_exec", "a.sshiftRight (b.toNat % 64)"),
        "mov": ("mov_exec", "b"), "movz": ("movz_exec", "0"), "inc": ("inc_exec", "a + 1")}
OPS = {"add": 0x8B000000, "sub": 0xCB000000, "and": 0x8A000000, "orr": 0xAA000000, "eor": 0xCA000000,
       "lslv": 0x9AC02000, "lsrv": 0x9AC02400, "asrv": 0x9AC02800}
words = []  # (tag, family, word, d, n, m)
for o, base in OPS.items():
    for k in range(min(N - 1, MAXK)): words.append((f"{o}_{k}", o, rrr(base, T[k], T[k], T[k + 1]), T[k], T[k], T[k + 1]))
for k in range(min(N - 1, MAXK)):
    words.append((f"cmp_{k}", "cmp", rrr(0xEB000000, 31, T[k], T[k + 1]), 31, T[k], T[k + 1]))
    for c, inv in [("lo", 2), ("lt", 10), ("eq", 1)]:
        words.append((f"cset_{c}_{k}", f"cset_{c}", rrr(0x9A800400 | inv << 12, T[k], 31, 31), T[k], 31, 31))
for k in range(min(N - 2, MAXK)):
    words.append((f"cmp0_{k}", "cmp0", 0xF100001F | T[k] << 5, 31, T[k], 0))
    words.append((f"csel_{k}", "csel", rrr(0x9A801000, T[k], T[k + 1], T[k + 2]), T[k], T[k + 1], T[k + 2]))
for k in range(min(N, MAXK)):
    for i in range(4): words.append((f"mov_{i}_{k}", "mov", rrr(0xAA000000, T[k], 31, i), T[k], 31, i))
    words.append((f"movz_{k}", "movz", 0xD2800000 | T[k], T[k], 0, 0))
    words.append((f"self_{k}", "add", rrr(0x8B000000, T[k], T[k], T[k]), T[k], T[k], T[k]))
    words.append((f"inc_{k}", "inc", 0x91000400 | T[k] << 5 | T[k], T[k], T[k], 0))
words.append(("res", "mov", rrr(0xAA000000, 0, 31, 9), 0, 31, 9))
assert len({w for _, _, w, *_ in words}) == len(words)

DSIMP = ("__DecodeA64, __DecodeA64_DataProcReg, __DecodeA64_DataProcImm, andM, ToBool.toBool, BitVec.slice, PreSail.readReg, "
         "PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, "
         "MonadStateOf.modifyGet, EStateM.modifyGet, h, hs, hk, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'")
out = ["""/- GENERATED by `python3 gen/gen_words.py > Arm/Words.lean`; do not edit.
Per-word lemmas for every word `Proven/CompilerArm.lean` emits (except `ret`): decode (dec_), decode+execute (word_, L1),
agreement with `armStep` (step_, L2). -/
import Arm.Small
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ArmProof
"""]
for tag, f, w, d, n, m in words:
    fn, args, see = DEC[f]
    call = f"{fn} {args.format(d=d, n=n, m=m)}"
    W = f"0x{w:08X}#32"
    out.append(f"""theorem dec_{tag} (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) :
    __DecodeA64 pc {W} s = {call} {{ s with regs := s.regs.insert .SEE ({see} : Int) }} := by
  have hk : ∀ k : Int, 1 ≤ k → see < k := fun k hk => by omega
  simp (config := {{decide := true}}) [{DSIMP}]
""")
    # L1
    reads = {"mov": [("b", m)], "movz": [], "inc": [("a", n)]}.get(f, [("a", n), ("b", m)])
    if f in EXEC:
        ex, val = EXEC[f]
        hyps = " ".join(f"({v} : BitVec 64) (h{r} : xget s.regs {r} = some {v})" for v, r in dict(reads).items() for _ in [0]) if False else \
               " ".join(f"{{{v} : BitVec 64}} (h{v} : xget s.regs {r} = some {v})" for v, r in reads)
        dargs = {"mov": f"(by decide) (by decide) ((xget_insert _ _ _ (by decide) {m}).trans hb)", "movz": "(by decide)",
                 "inc": f"(by decide) (by decide) ((xget_insert _ _ _ (by decide) {n}).trans ha)"}.get(
            f, f"(by decide) (by decide) (by decide) ((xget_insert _ _ _ (by decide) {n}).trans ha) ((xget_insert _ _ _ (by decide) {m}).trans hb)")
        out.append(f"""theorem word_{tag} (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {hyps} :
    __DecodeA64 pc {W} s = .ok () {{ s with regs := xset (s.regs.insert .SEE ({see} : Int)) {d} ({val}) }} := by
  rw [dec_{tag} s pc see hs h]; exact {ex} (d := {d}) {dargs}
""")
    # L2
    D = f"(fun s h => dec_{tag} s pc (-1) (by decide) h)"
    xr = lambda r: f"(h₀.x {r} (by decide))"
    if f in EXEC:
        ex, _ = EXEC[f]
        eargs = {"mov": f"(by decide) (by decide) {xr(m)}", "movz": "(by decide)", "inc": f"(by decide) (by decide) {xr(n)}"}.get(
            f, f"(by decide) (by decide) (by decide) {xr(n)} {xr(m)}")
        body = f"step_x (d := {d}) (by decide) {D} (fun s₀ h₀ _ => {ex} {eargs})"
    elif f == "cmp":
        body = f"step_cmp {D} (fun s₀ p h₀ hp => cmp_exec (by decide) (by decide) {xr(n)} {xr(m)} hp)"
    elif f == "cmp0":
        body = f"step_cmp {D} (fun s₀ p h₀ hp => cmp0_exec 0#12 (by decide) {xr(n)} hp)"
    elif f == "csel":
        body = f"step_csel (d := {d}) (n := {n}) (m := {m}) (by decide) (by decide) (by decide) {D}"
    else:
        body = f"step_{f} (d := {d}) (by decide) {D}"
    out.append(f"""theorem step_{tag} (pc : Int) (s : St) (a : AState) (hc : ArmCfg s) (ha : Abs s a) : Step pc {W} s a :=
  {body} (by simp [armStep, AState.rd]) hc ha
""")
out.append("/-- every word `Arm.gen e 0 ++ [Arm.iRes]` can contain when `e.depth < 11` -/")
out.append("def emitted : List (BitVec 32) := [" + ", ".join(f"0x{w:08X}#32" for _, _, w, *_ in words) + "]")
out.append(f"""
/-- **L2**: on every emitted word, the model's decode+execute (after `SEE := -1`) agrees with `armStep`. -/
theorem armStep_ok {{w : BitVec 32}} (hw : w ∈ emitted) (pc : Int) (s : St) (a : AState) (hc : ArmCfg s) (ha : Abs s a) :
    Step pc w s a := by
  simp only [emitted, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with {" | ".join(["rfl"] * len(words))}
{chr(10).join(f"  · exact step_{t} pc s a hc ha" for t, *_ in words)}
""")
out.append("end ArmProof")
print("\n".join(out))

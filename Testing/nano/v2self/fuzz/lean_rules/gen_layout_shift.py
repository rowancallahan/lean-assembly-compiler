"""cases4 (layout a1..a9) and the shift 3-leaf enumeration (486 trees); run with lean on PATH, LEAN_PATH with Nano.Main.Prelude. UNPROVEN glue."""
import itertools,subprocess,re,os
D=os.environ.get("CASES","/tmp/claude-0/lr/cases4"); os.makedirs(D,exist_ok=True)
IN="-- input (hex): 61 02 03\n"
c={}
c["a1_let_rhs_arg_le_let_col"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (\n  let a := rd x\n  0; a)\n"
c["a2_match_rhs_arg_eq_bar"]=IN+"def f (a b : UInt64) : UInt64 := a\ndef m (x : List UInt8) : List UInt8 := put [] (match rd x 0 with\n  | 97 => f 1\n  2\n  | _ => 3)\n"
c["a3_if_else_col0_in_let"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (\n  let a := 1;\n  if rd x 0 == 97 then a\nelse 2)\n"
c["a4_if_then_col0_top"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (if rd x 0 == 97\nthen 1\nelse 2)\n"
c["a8_let_bodyline_same_col"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (\n  let a := 1\n  a)\n"
c["a9_let_semi_next_col0"]=IN+"def m (x : List UInt8) : List UInt8 := put [] (let a := 1\na)\n"
for k,v in c.items(): open(f"{D}/{k}.lean","w",newline="").write(v)
leaves={"v":"rd x 0","n":"7","s":"(rd x 1 >>> 2)"}; ops=["+","*","|||"]
lines=["import Nano.Main.Prelude"]; ln={}
for a,b,cc in itertools.product(leaves,repeat=3):
  for o1,o2 in itertools.product(ops,repeat=2):
    for shape in (0,1):
      A,B,C=leaves[a],leaves[b],leaves[cc]
      e=f"(({A} {o1} {B}) {o2} {C})" if shape==0 else f"({A} {o1} ({B} {o2} {C}))"
      lines.append(f"def t{len(lines)} (x : List UInt8) : List UInt8 := put [] {e}"); ln[len(lines)]=f"{a}{b}{cc}{o1}{o2}{shape}"
open("/tmp/enum_shift.lean","w").write("\n".join(lines)+"\n")
out=subprocess.run(["lean","/tmp/enum_shift.lean"],capture_output=True,text=True).stdout
bad={ln[int(m.group(1))] for m in re.finditer(r"enum_shift.lean:(\d+):\d+: error",out)}
print(len(ln),"trees,",len(bad),"rejected by Lean; rejected patterns (leaf order):",sorted({k[:3] for k in bad}))

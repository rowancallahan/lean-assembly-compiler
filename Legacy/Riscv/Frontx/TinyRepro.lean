/- The self-hoster's blockers F1 and F3 (branch `tinyself2`, `Testing/notes/TINYSELF2.md`, reproducers
`Testing/asm/tiny2/repro/r1, r2, r3, r5`), now compiled with machine theorems (NOTES section 25): F1 (`r1`, an
arm budget over the reach of a branch: straight-line body), F3 (`r2`, `r3`, `r5`: built terms as call arguments). -/
import Legacy.Riscv.Frontx.IndCmd

-- repro/r1_arm_count.lean
namespace TinyR1
inductive Ex where
  | lit (n : UInt64)
  | var
  | add (a b : Ex)
  | sub (a b : Ex)

inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | ldx (rest : Ins)
  | add (rest : Ins)
  | sub (rest : Ins)

def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .ldx r, ys => .ldx (r.app ys)
  | .add r, ys => .add (r.app ys)
  | .sub r, ys => .sub (r.app ys)

def comp : Ex → Ins
  | .lit n => .push n .nil
  | .var => .ldx .nil
  | .add a b => (comp a).app ((comp b).app (.add .nil))
  | .sub a b => (comp a).app ((comp b).app (.sub .nil))

frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end TinyR1

-- repro/r2_literal_scalar_in_ext_arg.lean
namespace TinyR2
inductive Ex where
  | lit (n : UInt64)
  | set (a : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | op (k : UInt64) (rest : Ins)
def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .op k r, ys => .op k (r.app ys)
def comp : Ex → Ins
  | .lit n => .push n .nil
  | .set a => (comp a).app (.op 8 .nil)
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end TinyR2

-- repro/r3_ctor_around_call_in_ext_arg.lean
namespace TinyR3
inductive Ex where
  | lit (n : UInt64)
  | set (a b : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | op (k : UInt64) (rest : Ins)
  | pop (rest : Ins)
def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .op k r, ys => .op k (r.app ys)
  | .pop r, ys => .pop (r.app ys)
def comp : Ex → Ins
  | .lit n => .push n .nil
  | .set a b => (comp a).app (.pop (comp b))
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end TinyR3

-- repro/r5_literal_scalar_in_call_arg_and_entry_nil.lean
namespace TinyR5
inductive Ex where
  | lit (n : UInt64)
  | neg (a : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
def comp : Ex → Ins → Ins
  | .lit n, K => .push n K
  | .neg a, K => comp a (.push 0 K)
def compile (e : Ex) : Ins := comp e .nil
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind compile on ExT using InsT
end TinyR5

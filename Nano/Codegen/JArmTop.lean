/- Nano/Codegen/JArmTop: C with the J → ARM translator as its native back end (PROTOTYPE, UNPROVEN): Gen's word
buffer (as `g42`, before `g40`'s byte output) → `e64` (Nano/Codegen/JArm.lean) → bytes. -/
import Nano.Codegen.Gen
import Nano.Codegen.JArm
namespace C

/-- Gen's RISC-V words for the AST x (`g42` without the byte output), EMPTY on reject -/
def e70 (x : Buf) (u : UInt64) : Buf :=
  if 2147483647 < bsize x then bnew else
  if bget x 0 == 2 then
    let (x2, w) := g53 x;
    if w == 0 then bnew else
    let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) u;
    let (r1, o) := g39 16777216 x2 r (g34 bnew) bnew bnew bnew;
    if bget r1 4 == 1 then bnew else if 16777215 < bsize o then bnew else if 262143 < bsize o then bnew else o
  else bnew

/-- **C, native ARM by translation**: AST → A64 code bytes, or EMPTY -/
def e71 (c : List UInt8) (x : Buf) : List UInt8 :=
  let w := e64 (e70 x g_999);
  if bsize w == 0 then [] else e49 16777216 c w 0 []

end C

import Legacy.Riscv.Frontx.Translate

namespace Proven.Frontx.BookExtra
open Proven Proven.Frontx

-- fp-lean@0abeea5 examples/Examples/ProgramsProofs/TCO.lean:33-35 (verbatim)
namespace MoreClear
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar + 0
  | x :: xs => sumHelper (x + soFar) xs
end MoreClear

-- book text (TCO.lean:33-35, namespace MoreClear) with the directive: running-sum invariant as in Riscv/Frontx/ListExamples.lean:69-72
namespace Tail
def sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar + 0
  | x :: xs => sumHelper (x + soFar) xs
frontx_view sumHelper
frontx_compile sumHelper.view from sumHelper.view.eq measure (fun B i _ => B.size - i)
  with fun B i soFar => i ≤ B.size ∧ soFar + 255 * (B.size - i) < 2 ^ 64
end Tail

end Proven.Frontx.BookExtra

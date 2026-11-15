import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1860-1862
section
variable {α β : Type}
namespace MatchDef
variable {α : Type}
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
frontx_view MatchDef.length
frontx_compile MatchDef.length.view from MatchDef.length.view.eq measure fun B i => B.size - i
#check @MatchDef.length
end MatchDef
end

end Proven.Frontx.Run

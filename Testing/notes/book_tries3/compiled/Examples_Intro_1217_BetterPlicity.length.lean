import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1217-1220
section
namespace BetterPlicity
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
frontx_view BetterPlicity.length
frontx_compile BetterPlicity.length.view from BetterPlicity.length.view.eq measure fun B i => B.size - i
#check @BetterPlicity.length
end BetterPlicity
end

end Proven.Frontx.Run

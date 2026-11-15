import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1847-1850
section
variable {α β : Type}
namespace AutoImpl
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
frontx_view AutoImpl.length
frontx_compile AutoImpl.length.view from AutoImpl.length.view.eq measure fun B i => B.size - i
#check @AutoImpl.length
end AutoImpl
end

end Proven.Frontx.Run

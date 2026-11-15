import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1192-1195
section
namespace Oooops
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)
frontx_view Oooops.length
frontx_compile Oooops.length.view from Oooops.length.view.eq measure fun B i => B.size - i
#check @Oooops.length
end Oooops
end

end Proven.Frontx.Run

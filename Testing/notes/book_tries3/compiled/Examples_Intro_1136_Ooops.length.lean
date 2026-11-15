import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1136-1139
section
namespace Ooops
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
frontx_view Ooops.length
frontx_compile Ooops.length.view from Ooops.length.view.eq measure fun B i => B.size - i
#check @Ooops.length
end Ooops
end

end Proven.Frontx.Run

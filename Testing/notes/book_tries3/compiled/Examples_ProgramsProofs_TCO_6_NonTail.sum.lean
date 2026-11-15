import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/ProgramsProofs/TCO.lean:6-8
section
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
frontx_view NonTail.sum
frontx_compile NonTail.sum.view from NonTail.sum.view.eq measure fun B i => B.size - i
#check @NonTail.sum
end

end Proven.Frontx.Run

import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/ProgramsProofs/TCO.lean:157-159
section
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
frontx_view NonTail.length
frontx_compile NonTail.length.view from NonTail.length.view.eq measure fun B i => B.size - i
#check @NonTail.length
end

end Proven.Frontx.Run

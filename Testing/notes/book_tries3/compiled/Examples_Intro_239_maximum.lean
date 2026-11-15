import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:239-242
section
section
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
frontx_compile maximum
#check @maximum
end
end

end Proven.Frontx.Run

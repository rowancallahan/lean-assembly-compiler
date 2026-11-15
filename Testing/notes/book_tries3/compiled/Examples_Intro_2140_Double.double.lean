import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:2140-2142
section
variable {α β : Type}
namespace Double
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
frontx_compile Double.double
#check @Double.double
end Double
end

end Proven.Frontx.Run

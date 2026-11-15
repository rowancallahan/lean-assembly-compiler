import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Intro.lean:1248-1248
section
def x := Unit
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:2213-2213
section
variable {α β : Type}
namespace NewNamespace
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
frontx_compile NewNamespace.quadruple
#check @NewNamespace.quadruple
end NewNamespace
end

end Proven.Frontx.Run

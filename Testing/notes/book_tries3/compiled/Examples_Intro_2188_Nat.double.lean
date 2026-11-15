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

-- TARGET Examples/Intro.lean:2188-2188
section
variable {α β : Type}
def Nat.double (x : Nat) : Nat := x + x
frontx_compile Nat.double
#check @Nat.double
end

end Proven.Frontx.Run

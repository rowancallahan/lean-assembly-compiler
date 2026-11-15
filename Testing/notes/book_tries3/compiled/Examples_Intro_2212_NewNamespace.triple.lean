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

-- TARGET Examples/Intro.lean:2212-2212
section
variable {α β : Type}
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
frontx_compile NewNamespace.triple
#check @NewNamespace.triple
end NewNamespace
end

end Proven.Frontx.Run

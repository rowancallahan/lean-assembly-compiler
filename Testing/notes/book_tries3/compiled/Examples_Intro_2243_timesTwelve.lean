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

-- ctx Examples/Intro.lean:2212-2212
section
variable {α β : Type}
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
end NewNamespace
end

-- ctx Examples/Intro.lean:2213-2213
section
variable {α β : Type}
namespace NewNamespace
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:2243-2245
section
variable {α β : Type}
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
frontx_compile timesTwelve
#check @timesTwelve
end

end Proven.Frontx.Run

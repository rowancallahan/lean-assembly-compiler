import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:2051-2054
section
variable {α β : Type}
namespace Match
variable {α β : Type}
namespace Explicit
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
frontx_compile Match.Explicit.halve
#check @Match.Explicit.halve
end Explicit
end Match
end

end Proven.Frontx.Run

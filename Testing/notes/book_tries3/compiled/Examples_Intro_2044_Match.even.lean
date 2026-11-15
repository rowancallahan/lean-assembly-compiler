import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Intro.lean:887-892
section
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:2044-2046
section
variable {α β : Type}
namespace Match
variable {α β : Type}
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
frontx_compile Match.even
#check @Match.even
end Match
end

end Proven.Frontx.Run

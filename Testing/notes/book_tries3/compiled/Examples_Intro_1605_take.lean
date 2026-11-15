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

-- TARGET Examples/Intro.lean:1605-1609
section
def take (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | _, [] => []
  | Nat.zero, _ => []
  | Nat.succ n', x :: xs => x :: take n' xs
frontx_view take
frontx_compile take.view from take.view.eq measure fun B i _ => B.size - i
#check @take
end

end Proven.Frontx.Run

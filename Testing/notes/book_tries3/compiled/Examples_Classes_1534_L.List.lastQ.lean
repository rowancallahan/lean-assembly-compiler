import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1534-1537
section
open Plus (plus)
namespace L
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)
frontx_view L.List.last?
frontx_compile L.List.last?.view from L.List.last?.view.eq measure fun B i => B.size - i
#check @L.List.last?
end L
end

end Proven.Frontx.Run

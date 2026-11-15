import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1498-1502
section
namespace Floop
def List.final? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | y1 :: y2 :: ys => final? (y2::ys)
frontx_view Floop.List.final?
frontx_compile Floop.List.final?.view from Floop.List.final?.view.eq measure fun B i => B.size - i
#check @Floop.List.final?
end Floop
end

end Proven.Frontx.Run

import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1428-1431
section
namespace Floop
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
frontx_view Floop.List.head?
frontx_compile Floop.List.head?.view from Floop.List.head?.view.eq measure fun B i => B.size - i
#check @Floop.List.head?
end Floop
end

end Proven.Frontx.Run

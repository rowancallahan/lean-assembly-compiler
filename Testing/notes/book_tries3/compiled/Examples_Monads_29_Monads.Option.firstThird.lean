import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Monads.lean:23-24
section
namespace Monads.Option
variable {α : Type}
def first (xs : List α) : Option α :=
  xs[0]?
end Monads.Option
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Monads.lean:29-36
section
namespace Monads.Option
variable {α : Type}
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)
frontx_view Monads.Option.firstThird
frontx_compile Monads.Option.firstThird.view from Monads.Option.firstThird.view.eq measure fun B i => B.size - i
#check @Monads.Option.firstThird
end Monads.Option
end

end Proven.Frontx.Run

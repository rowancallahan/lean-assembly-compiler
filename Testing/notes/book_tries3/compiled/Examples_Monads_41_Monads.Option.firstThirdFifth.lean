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

-- TARGET Examples/Monads.lean:41-51
section
namespace Monads.Option
variable {α : Type}
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)
frontx_view Monads.Option.firstThirdFifth
frontx_compile Monads.Option.firstThirdFifth.view from Monads.Option.firstThirdFifth.view.eq measure fun B i => B.size - i
#check @Monads.Option.firstThirdFifth
end Monads.Option
end

end Proven.Frontx.Run

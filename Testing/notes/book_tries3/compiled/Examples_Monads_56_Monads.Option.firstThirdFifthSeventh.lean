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

-- TARGET Examples/Monads.lean:56-69
section
namespace Monads.Option
variable {α : Type}
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)
frontx_view Monads.Option.firstThirdFifthSeventh
frontx_compile Monads.Option.firstThirdFifthSeventh.view from Monads.Option.firstThirdFifthSeventh.view.eq measure fun B i => B.size - i
#check @Monads.Option.firstThirdFifthSeventh
end Monads.Option
end

end Proven.Frontx.Run

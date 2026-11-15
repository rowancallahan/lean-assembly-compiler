import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Monads.lean:167-170
section
namespace Monads.Err
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
end Monads.Err
end

-- ctx Examples/Monads.lean:197-198
section
namespace Monads.Err
def first (xs : List α) : Except String α :=
  get xs 0
end Monads.Err
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Monads.lean:230-243
section
namespace Monads.Err
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)
frontx_view Monads.Err.firstThirdFifthSeventh
frontx_compile Monads.Err.firstThirdFifthSeventh.view from Monads.Err.firstThirdFifthSeventh.view.eq measure fun B i => B.size - i
#check @Monads.Err.firstThirdFifthSeventh
end Monads.Err
end

end Proven.Frontx.Run

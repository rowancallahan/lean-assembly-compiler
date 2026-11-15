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

-- TARGET Examples/Monads.lean:203-210
section
namespace Monads.Err
def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)
frontx_view Monads.Err.firstThird
frontx_compile Monads.Err.firstThird.view from Monads.Err.firstThird.view.eq measure fun B i => B.size - i
#check @Monads.Err.firstThird
end Monads.Err
end

end Proven.Frontx.Run

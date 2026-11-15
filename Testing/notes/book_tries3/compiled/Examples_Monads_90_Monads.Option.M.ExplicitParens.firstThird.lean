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

-- ctx Examples/Monads.lean:29-36
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
end Monads.Option
end

-- ctx Examples/Monads.lean:74-77
section
namespace Monads.Option
variable {α : Type}
namespace M
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
end M
end Monads.Option
end

-- ctx Examples/Monads.lean:82-85
section
namespace Monads.Option
variable {α : Type}
namespace M
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
end M
end Monads.Option
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Monads.lean:90-93
section
namespace Monads.Option
variable {α : Type}
namespace M
namespace ExplicitParens
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
frontx_view Monads.Option.M.ExplicitParens.firstThird
frontx_compile Monads.Option.M.ExplicitParens.firstThird.view from Monads.Option.M.ExplicitParens.firstThird.view.eq measure fun B i => B.size - i
#check @Monads.Option.M.ExplicitParens.firstThird
end ExplicitParens
end M
end Monads.Option
end

end Proven.Frontx.Run

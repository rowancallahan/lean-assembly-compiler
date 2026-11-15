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

-- ctx Examples/Intro.lean:1813-1817
section
variable {α β : Type}
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Intro.lean:1837-1841
section
variable {α β : Type}
namespace Both
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
frontx_view Both.sameLength
frontx_compile Both.sameLength.view from Both.sameLength.view.eq measure fun B i _ => B.size - i
#check @Both.sameLength
end Both
end

end Proven.Frontx.Run

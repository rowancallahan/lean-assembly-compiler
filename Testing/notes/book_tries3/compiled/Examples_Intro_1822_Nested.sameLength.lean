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

-- TARGET Examples/Intro.lean:1822-1831
section
variable {α β : Type}
namespace Nested
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | x :: xs' =>
    match ys with
    | y :: ys' => sameLength xs' ys'
    | _ => false
frontx_view Nested.sameLength
frontx_compile Nested.sameLength.view from Nested.sameLength.view.eq measure fun B i _ => B.size - i
#check @Nested.sameLength
end Nested
end

end Proven.Frontx.Run

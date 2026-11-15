import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Monads/Many.lean:4-6
section
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Monads/Many.lean:16-18
section
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
frontx_ind_type TT761_0 := (Many Nat)
frontx_ind Many.union on TT761_0
#check @Many.union
end

end Proven.Frontx.Run

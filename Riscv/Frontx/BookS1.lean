/- Book survey 3, first third of the example files: rows that compile on current main (BOOK_S1.md). -/
import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000

namespace Proven.Frontx.BookS1.R320


-- ctx Examples/DependentTypes/Finite.lean:82-86
section
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:215-219
section
def Finite.isSingleton : Finite → Bool
  | .unit => true
  | .bool => false
  | .pair t1 t2 => not (isSingleton t1) || not (isSingleton t2)
  | .arr _ cod => not (isSingleton cod)
frontx_ind_type TT320_0 := Finite
frontx_ind Finite.isSingleton on TT320_0
#check @Finite.isSingleton
end

end Proven.Frontx.BookS1.R320

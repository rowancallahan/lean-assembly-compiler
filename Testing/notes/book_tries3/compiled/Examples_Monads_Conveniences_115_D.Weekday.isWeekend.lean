import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Monads/Conveniences.lean:71-78
section
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Monads/Conveniences.lean:115-117
section
namespace D
variable {α : Type}
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
frontx_ind_type TT743_0 := Weekday
frontx_ind D.Weekday.isWeekend on TT743_0
#check @D.Weekday.isWeekend
end D
end

end Proven.Frontx.Run

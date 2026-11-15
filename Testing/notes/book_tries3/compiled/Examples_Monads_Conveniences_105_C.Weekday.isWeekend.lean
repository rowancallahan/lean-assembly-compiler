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

-- TARGET Examples/Monads/Conveniences.lean:105-108
section
namespace C
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
frontx_ind_type TT742_0 := Weekday
frontx_ind C.Weekday.isWeekend on TT742_0
#check @C.Weekday.isWeekend
end C
end

end Proven.Frontx.Run

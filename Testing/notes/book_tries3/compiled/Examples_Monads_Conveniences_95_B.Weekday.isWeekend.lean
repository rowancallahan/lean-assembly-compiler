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

-- TARGET Examples/Monads/Conveniences.lean:95-99
section
namespace B
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
frontx_ind_type TT741_0 := Weekday
frontx_ind B.Weekday.isWeekend on TT741_0
#check @B.Weekday.isWeekend
end B
end

end Proven.Frontx.Run

import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Classes/Even.lean:4-6
section
namespace Even
inductive Even : Type where
  | zero : Even
  | plusTwo : Even → Even
end Even
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes/Even.lean:8-10
section
namespace Even
def Even.plus : Even → Even → Even
  | Even.zero, k => k
  | Even.plusTwo n, k => Even.plusTwo (n.plus k)
frontx_ind_type TT217_0 := Even.Even
frontx_ind Even.Even.plus on TT217_0
#check @Even.Even.plus
end Even
end

end Proven.Frontx.Run

import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/FunctorApplicativeMonad.lean:7-8
section
structure MythicalCreature where
  large : Bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:238-238
section
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
frontx_compile MythicalCreature.small
#check @MythicalCreature.small
end

end Proven.Frontx.Run

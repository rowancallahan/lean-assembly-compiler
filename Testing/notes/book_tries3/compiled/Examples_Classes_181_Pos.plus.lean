import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
namespace Proven.Frontx.Run


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
frontx_ind_type TT69_0 := Pos
frontx_ind Pos.plus on TT69_0
#check @Pos.plus
end

end Proven.Frontx.Run

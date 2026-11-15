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

-- ctx Examples/Classes.lean:1255-1257
section
open Plus (plus)
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
end

-- ctx Examples/Classes.lean:1259-1265
section
open Plus (plus)
def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false
end

-- ctx Examples/Classes.lean:1267-1268
section
open Plus (plus)
instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree
end

-- ctx Examples/Monads/Conveniences.lean:53-55
section
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/ProgramsProofs/TCO.lean:127-129
section
def Slow.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
frontx_ind_type TT852_0 := (BinTree Nat)
frontx_ind Slow.mirror on TT852_0
#check @Slow.mirror
end

end Proven.Frontx.Run

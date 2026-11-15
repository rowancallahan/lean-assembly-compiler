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

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:185-186
section
open Plus (plus)
instance : Plus Pos where
  plus := Pos.plus
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
frontx_ind_type TT79_0 := Pos
frontx_ind Pos.mul on TT79_0
#check @Pos.mul
end

end Proven.Frontx.Run

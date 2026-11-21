import Legacy.Riscv.Back.Opt
import Legacy.Riscv.Examples.GcdOpt
import Legacy.Compiler.Front.Reify
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def put (name : String) (r : Except String (List (BitVec 32))) : IO Unit :=
  match r with
  | .ok ws => do
    IO.FS.writeFile s!"Testing/asm/opt-words/{name}.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
    IO.println s!"{name}: {ws.length} words"
  | .error e => throw (IO.userError s!"{name}: {e}")
#eval do
  put "loopsum" (compileOptS sumProg)
  put "gcd-a" (compileOptS gcdProg)
  put "gcd" (.ok gcdCodeO)  -- `gcdProg2`, `Riscv/Examples/GcdOpt.lean`
  put "demo" (compileOpt demoE)
  put "demo2" (compileOpt demo2E)

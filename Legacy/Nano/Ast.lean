/- nano: AST and meaning.  Calls carry the callee's (already resolved) body; argument lists are `acons`/`anil`
   chains inside the same inductive.  Variables are de Bruijn indices, newest binding = 0; a function's
   parameters x1..xn are bound so that xn = 0. -/
namespace Nano

inductive Ex where
  | num (n : UInt64) | var (i : Nat)
  | add (a b : Ex) | sub (a b : Ex) | mul (a b : Ex)
  | let_ (v b : Ex)
  | call (body args : Ex)
  | anil | acons (e rest : Ex)
  deriving DecidableEq

/-- a program = the entry's arity and body -/
abbrev Prog := Nat × Ex

mutual
def den : Ex → List UInt64 → UInt64
  | .num n, _ => n
  | .var i, env => env.getD i 0
  | .add a b, env => den a env + den b env
  | .sub a b, env => den a env - den b env
  | .mul a b, env => den a env * den b env
  | .let_ v b, env => den b (den v env :: env)
  | .call b as, env => den b (denA as env).reverse
  | .anil, _ => 0
  | .acons _ _, _ => 0
def denA : Ex → List UInt64 → List UInt64
  | .acons e r, env => den e env :: denA r env
  | _, _ => []
end

/-- the meaning of a program on its argument words (`none` on wrong arity) -/
def Prog.eval (p : Prog) (args : List UInt64) : Option UInt64 :=
  if args.length = p.1 then some (den p.2 args.reverse) else none

end Nano

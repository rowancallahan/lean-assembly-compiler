import Lean
import Legacy.Nano.Elab
/- EXHAUSTIVE subset check: every body of 1..L tokens over a 15-token alphabet, as `def f (x y : UInt64) : UInt64 := <body>` after
   `def g (a b) := a - b; def h (a) := a * 3; def k := 7`.  nanoElab runs on all of them (fast); every text nano ACCEPTS is also run through
   Lean's real frontend, and the results on 4 input vectors must be equal.  usage:
   lake env lean --run Testing/nano/exhaust.lean L shard nshards [mode 0|1|2]   (prints a summary; exit 1 on any difference) -/
open Lean Elab

def toks : Array String := #["x", "y", "1", "-", "+", "*", "(", ")", "g", "h", "k", "let", "w", ":=", ";"]
def pre : String := "def g (a b : UInt64) : UInt64 := a - b\ndef h (a : UInt64) : UInt64 := a * 3\ndef k : UInt64 := 7\n"
def ins : List (List UInt64) := [[0, 0], [1, 2], [0xFFFFFFFFFFFFFFFF, 3], [12345678901234567, 0x8000000000000000]]

unsafe def real (env : Environment) (src : String) : IO (Option (List UInt64)) := do
  let run (s : String) : IO (Environment × Bool) := do
    let st ← IO.processCommands (Parser.mkInputContext s "<nano>") {} (Command.mkState env {} {})
    return (st.commandState.env, !st.commandState.messages.hasErrors)
  let (_, ok) ← run src
  if !ok then return none
  let (env2, ok2) ← run (src ++ "def __w (__v : List UInt64) : UInt64 := f (__v.getD 0 0) (__v.getD 1 0)\n")
  if !ok2 then return none
  match env2.evalConst (List UInt64 → UInt64) {} `__w with
  | .error _ => return none
  | .ok f => return some (ins.map f)

structure St where
  nano : Nat := 0
  bad : Nat := 0
  total : Nat := 0

def isW (c : Char) : Bool := c.isAlphanum || c == '_'
/-- `mode` 0: single spaces; 1: spaces only between word characters (`x-1`, `g(x)`, `(x)(y)`); 2: a newline before every token (column 0) -/
def joinToks (mode : Nat) (ts : List String) : String :=
  match mode with
  | 0 => " ".intercalate ts
  | 1 => (ts.foldl (fun (acc : String × String) t =>
      (acc.1 ++ (if acc.2 != "" && isW (acc.2.back) && isW (t.get 0) then " " else "") ++ t, t)) ("", "")).1
  | _ => "\n".intercalate ts

unsafe def check (env : Environment) (mode : Nat) (s : St) (ts : List String) : IO St := do
  let body := joinToks mode ts
  let src := pre ++ "def f (x y : UInt64) : UInt64 := " ++ body ++ "\n"
  let s := { s with total := s.total + 1 }
  match Nano.nanoElab src.toUTF8.toList with
  | none => return s
  | some p =>
    let nanoV := ins.map fun a => (p.eval a).getD 0
    let r ← real env src
    let s := { s with nano := s.nano + 1 }
    if r == some nanoV then return s
    IO.println s!"BUG {repr body} lean={repr r} nano={nanoV}"
    return { s with bad := s.bad + 1 }

unsafe def enum (env : Environment) (mode L : Nat) (first : Nat → Bool) : IO St := do
  -- iterative DFS over all token sequences of length 1..L; the first token's index filtered by `first`
  let mut st : St := {}
  let mut stack : Array (List Nat) := #[]
  for i in [0:toks.size] do if first i then stack := stack.push [i]
  while !stack.isEmpty do
    let cur := stack.back!
    stack := stack.pop
    st ← check env mode st (cur.reverse.map (toks[·]!))
    if cur.length < L then
      for i in [0:toks.size] do stack := stack.push (i :: cur)
  return st

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {} 0 (loadExts := true)
  let L := args[0]!.toNat!; let sh := args[1]!.toNat!; let n := args[2]!.toNat!
  let mode := (args.getD 3 "0").toNat!
  let st ← enum env mode L (fun i => i % n == sh)
  IO.println s!"mode {mode} L={L} shard {sh}/{n}: {st.total} bodies, nano accepts {st.nano}, differences {st.bad}"
  return (if st.bad == 0 then 0 else 1)

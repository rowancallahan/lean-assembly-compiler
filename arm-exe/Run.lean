-- Hand-written driver for the generated ARM model. All numbers hex.
--   armrun run FILE    line: `x0 x1 x2 x3 word...`. Words at address 0 (reset vector), x30 := stop, the model's
--                      `step_model` is called until PC = stop (so the trailing `ret` IS executed). Prints x0.
--   armrun step FILE   line: `pc nzcv x0 .. x30 word maddr mbytes` (mbytes: hex string, low address first).
--                      Puts `word` at pc and mbytes at maddr, calls `step_model` ONCE.
--                      Prints `pc nzcv x0 .. x30 mbytes` after the step, or `ERR <message>` if the model throws.
--   armrun stepA0 FILE same, with SCTLR_EL3.A (bit 1, alignment check) cleared after reset.
--   armrun stepdbg FILE same as step; the model's ESR_EL3, ELR_EL3, FAR_EL3 are inserted before mbytes.
--   armrun reset -     prints SCTLR_EL3 as left by reset.
-- The reset state (`sail_model_init`, `__InitSystem`) is computed once and reused for every line: the state is an
-- immutable value, each line starts from it with its own memory and registers.
import ArmRun.Model
open Sail Sail.ConcurrencyInterfaceV1 Armv9 Armv9.Functions

abbrev St := SequentialState RegisterType trivialChoiceSource
def stop : BitVec 64 := 0x100000
def maxSteps := 1000000

def setX (i : Nat) (v : BitVec 64) : SailM Unit :=
  match i with
  | 0 => writeReg Register.R0 v
  | 1 => writeReg Register.R1 v
  | 2 => writeReg Register.R2 v
  | 3 => writeReg Register.R3 v
  | 4 => writeReg Register.R4 v
  | 5 => writeReg Register.R5 v
  | 6 => writeReg Register.R6 v
  | 7 => writeReg Register.R7 v
  | 8 => writeReg Register.R8 v
  | 9 => writeReg Register.R9 v
  | 10 => writeReg Register.R10 v
  | 11 => writeReg Register.R11 v
  | 12 => writeReg Register.R12 v
  | 13 => writeReg Register.R13 v
  | 14 => writeReg Register.R14 v
  | 15 => writeReg Register.R15 v
  | 16 => writeReg Register.R16 v
  | 17 => writeReg Register.R17 v
  | 18 => writeReg Register.R18 v
  | 19 => writeReg Register.R19 v
  | 20 => writeReg Register.R20 v
  | 21 => writeReg Register.R21 v
  | 22 => writeReg Register.R22 v
  | 23 => writeReg Register.R23 v
  | 24 => writeReg Register.R24 v
  | 25 => writeReg Register.R25 v
  | 26 => writeReg Register.R26 v
  | 27 => writeReg Register.R27 v
  | 28 => writeReg Register.R28 v
  | 29 => writeReg Register.R29 v
  | 30 => writeReg Register.R30 v
  | _ => panic! "setX"
def getX (i : Nat) : SailM (BitVec 64) :=
  match i with
  | 0 => readReg Register.R0
  | 1 => readReg Register.R1
  | 2 => readReg Register.R2
  | 3 => readReg Register.R3
  | 4 => readReg Register.R4
  | 5 => readReg Register.R5
  | 6 => readReg Register.R6
  | 7 => readReg Register.R7
  | 8 => readReg Register.R8
  | 9 => readReg Register.R9
  | 10 => readReg Register.R10
  | 11 => readReg Register.R11
  | 12 => readReg Register.R12
  | 13 => readReg Register.R13
  | 14 => readReg Register.R14
  | 15 => readReg Register.R15
  | 16 => readReg Register.R16
  | 17 => readReg Register.R17
  | 18 => readReg Register.R18
  | 19 => readReg Register.R19
  | 20 => readReg Register.R20
  | 21 => readReg Register.R21
  | 22 => readReg Register.R22
  | 23 => readReg Register.R23
  | 24 => readReg Register.R24
  | 25 => readReg Register.R25
  | 26 => readReg Register.R26
  | 27 => readReg Register.R27
  | 28 => readReg Register.R28
  | 29 => readReg Register.R29
  | 30 => readReg Register.R30
  | _ => panic! "getX"

def run (xs : List Nat) : SailM (BitVec 64) := do
  for i in [0:4] do setX i (BitVec.ofNat 64 xs[i]!)
  setX 30 stop
  let mut n := 0
  while (← readReg Register._PC) != stop do
    assert! n < maxSteps
    step_model ()
    n := n + 1
  getX 0

def step (dbg : Bool) (v : Array Nat) : SailM (List Nat) := do
  writeReg Register._PC (BitVec.ofNat 64 v[0]!)
  let b := fun i => BitVec.ofNat 1 (v[1]! >>> i)
  writeReg Register.PSTATE { (← readReg Register.PSTATE) with N := b 3, Z := b 2, C := b 1, V := b 0 }
  for i in [0:31] do setX i (BitVec.ofNat 64 v[2 + i]!)
  step_model ()
  let p ← readReg Register.PSTATE
  let mut out := [(← readReg Register._PC).toNat, (p.N ++ p.Z ++ p.C ++ p.V).toNat]
  for i in [0:31] do out := out ++ [(← getX i).toNat]
  if dbg then out := out ++ [(← readReg Register.ESR_EL3).toNat, (← readReg Register.ELR_EL3).toNat, (← readReg Register.FAR_EL3).toNat]
  return out

def hex (s : String) : Nat := s.foldl (fun a c => 16 * a + "0123456789abcdef".toList.idxOf c) 0
def toHex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)
def le (addr w n : Nat) : List (Nat × BitVec 8) := (List.range n).map fun j => (addr + j, BitVec.ofNat 8 (w >>> (8 * j)))

def main (args : List String) : IO UInt32 := do
  let init : SailM (BitVec 64) := do
    sail_model_init (); __InitSystem ()
    let s ← readReg Register.SCTLR_EL3
    if args[0]! == "stepA0" then writeReg Register.SCTLR_EL3 (s &&& ~~~2#64)   -- clear SCTLR_EL3.A (alignment check)
    return s
  let .ok sctlr reset := init.run (default : St) | panic! "reset failed"
  assert! reset.mem.isEmpty
  if args[0]! == "reset" then IO.println s!"SCTLR_EL3 after reset = {toHex sctlr.toNat}"; return 0
  for l in (← IO.FS.lines args[1]!) do
    let tok := (l.splitOn " ").toArray
    if args[0]! == "run" then
      let v := tok.toList.map hex
      let bytes := (v.drop 4).zipIdx.flatMap fun (w, i) => le (4 * i) w 4
      match (run v).run { reset with mem := .ofList bytes } with
      | .ok x _ => IO.println (toHex x.toNat)
      | .error e _ => panic! s!"line `{l}`: {e.print}"
    else
      assert! (args[0]!.startsWith "step") && tok.size == 36
      let v := tok.map hex
      let n := tok[35]!.length / 2
      let mb := (List.range n).map fun j => (v[34]! + j, BitVec.ofNat 8 (hex (String.ofList ((tok[35]!.toList.drop (2 * j)).take 2))))
      match (step (args[0]! == "stepdbg") v).run { reset with mem := .ofList (le v[0]! v[33]! 4 ++ mb) } with
      | .ok out s =>
        let m := String.join ((List.range n).map fun j => let x := toHex (s.mem.get! (v[34]! + j)).toNat; if x.length == 1 then "0" ++ x else x)
        IO.println (" ".intercalate (out.map toHex ++ [m]))
      | .error e _ => IO.println s!"ERR {e.print}"
  return 0

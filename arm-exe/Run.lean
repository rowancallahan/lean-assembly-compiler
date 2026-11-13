-- Hand-written driver for the generated ARM model.
--   armrun FILE     each line of FILE: `x0 x1 x2 x3 word...` (hex). Prints x0 (hex) per line after running the words.
-- Words go at address 0 (reset vector, CFG_RVBAR = 0). x30 := `stop`; the model's `step_model` is called until
-- PC = stop, so the trailing `ret` IS executed. The reset state is computed once and reused for every line
-- (the state is an immutable value; each line gets that value with its own memory and x0..x3, x30).
import ArmRun.Model
open Sail Sail.ConcurrencyInterfaceV1 Armv9 Armv9.Functions

abbrev St := SequentialState RegisterType trivialChoiceSource
def stop : BitVec 64 := 0x100000
def maxSteps := 1000000

def run (xs : List (BitVec 64)) : SailM (BitVec 64) := do
  writeReg Register.R0 xs[0]!; writeReg Register.R1 xs[1]!; writeReg Register.R2 xs[2]!; writeReg Register.R3 xs[3]!
  writeReg Register.R30 stop
  let mut n := 0
  while (← readReg Register._PC) != stop do
    assert! n < maxSteps
    step_model ()
    n := n + 1
  readReg Register.R0

def hex (s : String) : Nat := s.foldl (fun a c => 16 * a + "0123456789abcdef".toList.idxOf c) 0

def main (args : List String) : IO UInt32 := do
  let .ok () reset := (do sail_model_init (); __InitSystem () : SailM Unit).run (default : St) | panic! "reset failed"
  assert! reset.mem.isEmpty
  for l in (← IO.FS.lines args[0]!) do
    let v := (l.splitOn " ").map hex
    let bytes := (v.drop 4).zipIdx.flatMap fun (w, i) => (List.range 4).map fun j => (4 * i + j, BitVec.ofNat 8 (w >>> (8 * j)))
    match (run ((v.take 4).map (BitVec.ofNat 64))).run { reset with mem := .ofList bytes } with
    | .ok x _ => IO.println (String.ofList (Nat.toDigits 16 x.toNat))
    | .error e _ => panic! s!"line `{l}`: {e.print}"
  return 0

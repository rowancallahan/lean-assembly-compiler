-- Hand-written driver. Runs AArch64 words on the generated model:
--   armrun <x0> <hexword>...   prints x0 after one step_model per word.
-- Words are placed at address 0 (the model's reset vector, CFG_RVBAR = 0).
import ArmRun.Model
open Sail Sail.ConcurrencyInterfaceV1 Armv9 Armv9.Functions

def run (x0 : BitVec 64) (n : Nat) : SailM (BitVec 64) := do
  sail_model_init ()
  __InitSystem ()
  writeReg Register.R0 x0
  for _ in [0:n] do step_model ()
  readReg Register.R0

def hex (s : String) : Nat := s.foldl (fun a c => 16 * a + "0123456789abcdef".toList.idxOf c) 0

def main (args : List String) : IO UInt32 := do
  let words := args.tail!.map hex
  let bytes := words.zipIdx.flatMap fun (w, i) => (List.range 4).map fun j => (4 * i + j, BitVec.ofNat 8 (w >>> (8 * j)))
  let s0 : SequentialState RegisterType trivialChoiceSource := { (default : SequentialState RegisterType trivialChoiceSource) with mem := .ofList bytes }
  match (run (BitVec.ofNat 64 args.head!.toNat!) words.length).run s0 with
  | .ok x s => s.sailOutput.forM IO.print; IO.println s!"x0 = {x.toNat}"; return 0
  | .error e s => s.sailOutput.forM IO.print; IO.eprintln s!"error: {e.print}"; return 1

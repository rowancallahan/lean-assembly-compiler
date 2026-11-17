import Nano.ElabBSplitE
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.Impl1
import Nano.CheckedSpill
/- stage 1b of the split lexer (`Nano.B.eB`, the emitter, Nano/ElabBSplit.lean) compiled by OUR compiler (front end
`frontx_compile`, list view), with a machine theorem `Nano.Self.eBE.implements1` -/
namespace Nano.Self
open Proven Proven.Frontx

frontx_view Nano.B.le
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
frontx_compile Nano.B.le.view from Nano.B.le.view.eq measure fun B i k m _ _ _ _ _ _ _ =>
  (if m == 7 then B.size - i + 1 else 0) + (B.size - i)

def eBE (xs : ByteArray) : List UInt8 := Nano.B.eB xs.data.toList
theorem eBE_eq (xs : ByteArray) : eBE xs = Nano.B.le.view xs 0 0 7 0 0 0 0 0 0 0 := rfl
frontx_entry eBE from eBE_eq
open Lean Proven.Mach Proven.Mach.Riscv in
/-- per colouring mode with every local spilled: does colourB succeed, does optB accept; with ms timings -/
def probeModes (N : Nat) (p : Proven.BStmt) : IO Unit := do
  let q := listProg p
  let spl := List.range N
  for mode in [0, 1, 2, 3, 4, 5, 6] do
    let t0 ← IO.monoMsNow
    let r := match colorB N [0, 3] [2] q spl mode with
      | some g => if (rvwF.optB scB (tblG (tabulate g 4096)) (fun j => spl.contains j) N [0, 3] [2] q).isSome then "optB ok" else "optB rejects"
      | none => "colorB none"
    IO.println s!"mode {mode}: {r} ({(← IO.monoMsNow) - t0} ms)"
#eval probeModes eBE.slots eBE.prog
end Nano.Self

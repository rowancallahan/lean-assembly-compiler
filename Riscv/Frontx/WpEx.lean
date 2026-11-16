/- Paged arrays (NOTES section 30), part 12: example programs with their `Implements1Pg` theorems. -/
import Riscv.Frontx.WpImpl

set_option linter.unusedVariables false

namespace Proven.WA.PgEx
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv

/-- bytes plus one, pushed one at a time -/
def copyGo (xs : ByteArray) (i : Nat) (out : ByteArray) : ByteArray :=
  if i < xs.size then copyGo xs (i + 1) (out.push (xs[i]! + 1)) else out
termination_by xs.size - i

def copyE (xs : ByteArray) : ByteArray := copyGo xs 0 ByteArray.empty

/-- the loop body over state `(out, i)`, then `xs` -/
def copyBody : T ([.ar .ba, .sc .nat] ++ [.ar .ba]) [.ar .ba, .sc .nat] (.ar .ba) :=
  .ite (.cmp .lt (.var (.tl .hd)) (.size (.tl (.tl .hd))))
    (.call (.cons (.push (.var .hd) (.bin .add (.getB (.tl (.tl .hd)) (.var (.tl .hd)) true) (.lit .u8 1)))
      (.cons (.bin .add (.var (.tl .hd)) (.lit .nat 1)) .nil)))
    (.ret (.var .hd))

def copyPg : Pg [.ar .ba] (.ar .ba) :=
  .loop [.ar .ba, .sc .nat] copyBody (.cons .empty (.cons (.lit .nat 0) .nil)) (.ret (.var .hd))


#eval (outBaseP copyPg, (copyPg.compP [inLocP] 9).2, (pgProgA copyPg).maxv, pgNA copyPg)

end Proven.WA.PgEx
namespace Proven.WA.PgEx
open Proven.WA Proven.WP
def stX := copyPg.compP [inLocP] 9
def initX : Inis [.ar .ba] [.ar .ba, .sc .nat] := (.cons .empty (.cons (.lit .nat 0) .nil))
#eval initX.wfP [inLocP]
#eval initX.locP [inLocP] 9
def stl := initX.locP [inLocP] 9
#eval (copyBody.rlP (stl ++ [inLocP]) (9 + 2 * 2 + 2))
#eval (wP [.ar .ba, .sc .nat] stl 13 14)
#eval copyBody.wfP stl ((copyBody.rlP (stl ++ [inLocP]) 15).getD default) (wP [.ar .ba, .sc .nat] stl 13 14) (stl ++ [inLocP]) 15
#eval decide (LoopC [.ar .ba, .sc .nat] stl [inLocP] 13 14 (.ar .ba) ((copyBody.rlP (stl ++ [inLocP]) 15).getD default) (wP [.ar .ba, .sc .nat] stl 13 14) 15)
end Proven.WA.PgEx
namespace Proven.WA.PgEx
open Proven.WA Proven.WP
def rlX := (copyBody.rlP (stl ++ [inLocP]) 15).getD default
def wX := wP [.ar .ba, .sc .nat] stl 13 14
#eval (vsOfP stl, workLocs [.ar .ba, .sc .nat] stl)
#eval decide (LayC stl 13 14 rlX wX 15)
#eval decide ((∀ l ∈ [inLocP], (l.v ∉ vsOfP stl ∧ l.v ≠ 13 ∧ l.v ≠ 14 ∧ NP l.v) ∧ (l.pt ∉ vsOfP stl ∧ l.pt ≠ 13 ∧ l.pt ≠ 14 ∧ NP l.pt)))
#eval decide ((workLocs [.ar .ba, .sc .nat] stl = [wX] ∨ workLocs [.ar .ba, .sc .nat] stl = []) ∧ (∀ l ∈ stl ++ [inLocP], l.v = wX.v → l = wX))
#eval decide (rlX.inp = false → rlX = wX ∧ workLocs [.ar .ba, .sc .nat] stl = [wX])
#eval decide (8 ∉ vsOfP stl ∧ 8 ≠ 13 ∧ 8 ≠ 14 ∧ ∀ l ∈ stl, l.pt ≠ 8)
#eval decide (NP (resLocP (.ar .ba) 13 rlX).v ∧ NP (resLocP (.ar .ba) 13 rlX).pt ∧ (resLocP (.ar .ba) 13 rlX).v ≠ 8 ∧ (resLocP (.ar .ba) 13 rlX).pt ≠ 8)
end Proven.WA.PgEx

/- A faster register choice for `frontx_implements_listC` (branch nano-closeA; the front end itself is unchanged):
`frontx_implements_listCS g` is `frontx_implements_listC g` with the (untrusted) choice `pickSpill`, which tries
"every local in its stack slot" (`spl = all`) with the seven colouring modes before falling back to `pickC`'s full
search.  `pickC` runs the code generator `optB` (interpreted) for many spill sets and modes; on the lexer stages this
search alone ran for more than an hour.  The theorem is produced by the same `implements1_listC` with the same
kernel check `(by decide +kernel)` that `optB` accepts the choice, so nothing trusted changes. -/
import Riscv.Frontx.Checked

namespace Proven.Frontx
open Lean Elab Command Term Proven Proven.Mach Proven.Mach.Riscv

/-- (untrusted) every local spilled, the first colouring mode `optB` accepts; else `pickC` -/
def pickSpill (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) (M : Nat := 4096) :
    Option (List (Nat × Reg) × List Nat) :=
  let spl := List.range N
  let r := [0, 1, 2, 3, 4, 5, 6].findSome? fun mode =>
    match colorB N bv wv p spl mode with
    | some g => let t := tabulate g M
      if (rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p).isSome then some (t, spl) else none
    | none => none
  match r with
  | some r => some r
  | none => pickC N bv wv p M

def pickListCS (N : Nat) (p : Proven.BStmt) : Option (List (Nat × Nat) × List Nat) :=
  (pickSpill N [0, 3] [2] (listProg p)).map fun (t, spl) => (t.map fun q => (q.1, q.2.val), spl)

/-- `frontx_implements_listC` with the choice `pickSpill` -/
elab "frontx_implements_listCS " g:ident : command => do
  let n := g.getId
  let prog := mkIdent (n ++ `prog); let slots := mkIdent (n ++ `slots)
  let exec := mkIdent (n ++ `exec); let code := mkIdent (n ++ `code)
  let tbl := mkIdent (n ++ `tbl); let spl := mkIdent (n ++ `spl)
  let thm := mkIdent (n ++ `implements1)
  let some (t, sp) ← liftTermElabM (evalChoice (← `(pickListCS $slots $prog)))
    | throwError "frontx_implements_listCS: no register choice passed optB"
  let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
  let ss : Array Term := sp.toArray.map fun j => quote j
  elabCommand (← `(def $tbl : List (Nat × Nat) := [$ts,*]))
  elabCommand (← `(def $spl : List Nat := [$ss,*]))
  elabCommand (← `(def $code : List (BitVec 32) := listCodeC $slots $tbl $spl $prog))
  elabCommand (← `(theorem $thm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) $code $g
        (fun _ => 8 * ($slots + 1) + 7) (retLen := true) :=
      implements1_listC $g $slots (by decide) $prog $tbl $spl (by decide +kernel) $exec))

end Proven.Frontx

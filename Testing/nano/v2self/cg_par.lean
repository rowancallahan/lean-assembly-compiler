import Nano.V2Self.C.Lex2
import Legacy.Nano.V2Self.Legacy.C.Par0
import Nano.V2Self.C.Gen
/- Main-shaped sources through the WHOLE chain C.s10 → C.y13 → C.g41 [] (no hand-written AST), expected output = the
same text as native Lean (the prelude's real definitions).  Writes Testing/asm/ir-words/cgp_K.{words,cases}; run each
with `BIG=16777216 NOSAIL=1 python3 Testing/nano/v2self/cg_test.py cgp_K`.  A rejection of a valid source is a FAILURE.
run: lean --run Testing/nano/v2self/cg_par.lean -/
namespace P
def m0 (x : List UInt8) : List UInt8 := put (put [] (rd x 0)) (len x)
def m1 (x : List UInt8) : List UInt8 := put [] (bget (bpush bnew 7) 0)
def m2 (x : List UInt8) : List UInt8 :=
  put (put (put [] (rd x 0 + rd x 1 * 3)) (if rd x 2 < 5 then len x else rd x 3 >>> 1)) (bget (bpush bnew 7) 0)
def m3 (x : List UInt8) : List UInt8 :=
  let b := bset (bpush (bpush bnew (rd x 1)) (rd x 0)) 0 (rd x 2 * 11); let c := bsize b;
  put (put (put [] (bget b 0)) (bget b 1 - c)) (if bget b 0 == rd x 3 then 1 else 2)
end P
def cases : List (String × (List UInt8 → List UInt8)) := [
  ("def m (x : List UInt8) : List UInt8 := put (put [] (rd x 0)) (len x)\n", P.m0),
  ("def m (x : List UInt8) : List UInt8 := put [] (bget (bpush bnew 7) 0)\n", P.m1),
  ("def m (x : List UInt8) : List UInt8 := put (put (put [] (rd x 0 + rd x 1 * 3)) (if rd x 2 < 5 then len x else rd x 3 >>> 1)) (bget (bpush bnew 7) 0)\n", P.m2),
  ("def m (x : List UInt8) : List UInt8 := let b := bset (bpush (bpush bnew (rd x 1)) (rd x 0)) 0 (rd x 2 * 11); let c := bsize b; put (put (put [] (bget b 0)) (bget b 1 - c)) (if bget b 0 == rd x 3 then 1 else 2)\n", P.m3)]
def hex (l : List UInt8) : String := if l.isEmpty then "-" else String.join (l.map fun b =>
  let s := (Nat.toDigits 16 b.toNat).asString; if s.length == 1 then "0" ++ s else s)
def inputs : List (List UInt8) := [[], [5], [1, 2, 3, 4], [255, 0, 2, 22], [9, 9, 200, 1, 7, 7]]
def main : IO Unit := do
  let mut k := 0
  for (src, f) in cases do
    let code := C.g41 [] (C.y13 (C.s10 src.toUTF8.toList))
    if code.isEmpty then throw (IO.userError s!"REJECTED valid source {src}")
    let wd := (List.range (code.length / 4)).map fun q =>
      (code.getD (4*q) 0).toNat + 256 * (code.getD (4*q+1) 0).toNat + 65536 * (code.getD (4*q+2) 0).toNat + 16777216 * (code.getD (4*q+3) 0).toNat
    let hx := wd.map fun w => let h := (Nat.toDigits 16 w).asString; String.ofList (List.replicate (8 - h.length) '0') ++ h
    IO.FS.writeFile s!"Testing/asm/ir-words/cgp_{k}.words" (s!"cgp {k}\n" ++ " ".intercalate hx ++ "\n")
    let cs := inputs.map fun x => let y := f x; hex x ++ (if y.isEmpty then " 1 -" else " 0 " ++ hex y)
    IO.FS.writeFile s!"Testing/asm/ir-words/cgp_{k}.cases" ("\n".intercalate cs ++ "\n")
    k := k + 1
  IO.println s!"valid sources accepted: {k}/{cases.length}"

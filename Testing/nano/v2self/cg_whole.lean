import Nano.V2Self.C.Gen
import Nano.V2Self.C.Main
/- g41 on the parser's AST of C's whole source (Testing/nano/v2self/c_source_ast.bin, 8-byte LE words).
Reports accept / code words, or the def id + cursor where Gen stopped.  The dumped source is the OLD chain
(`c_source_input.txt` = Lex/Parse/Inl/Expand/Asm/Main, main `C.m`), so on accept the code is written to
Testing/asm/ir-words/cgw.{words,cases} with expected outputs = native `C.m` (run: BIG=… NOSAIL=1 cg_test.py cgw).  run: lean --run Testing/nano/v2self/cg_whole.lean [BIN] -/
def rdw (b : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun a k => a ||| ((b.get! (8*i+k)).toUInt64 <<< (8*k).toUInt64)) 0
def main (args : List String) : IO Unit := do
  let b ← IO.FS.readBinFile (args.headD "Testing/nano/v2self/c_source_ast.bin")
  let x : List UInt64 := (List.range (b.size / 8)).map (rdw b)
  IO.println s!"ast words {x.length}, defs {(x.filter (· == 20)).length} (upper bound)"
  -- run the main loop directly to see where it stops
  let r := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0) 0) C.g_999
  let (r1, o) := C.g39 16777216 x r (C.g34 bnew) bnew bnew bnew
  IO.println s!"err {bget r1 4} done {bget r1 5} cursor {bget r1 0} code words {o.length}"
  if bget r1 4 == 1 then
    let i := (bget r1 0).toNat
    -- the last DEF header at or before the cursor
    let hs := (List.range (i+1)).filter fun j => x.getD j 0 == 20 && j + 6 ≤ x.length
    let h := hs.getLast?.getD 0
    IO.println s!"stopped at word {i} (tag {x.getD i 0}); last DEF-tag word {h}: {x.drop h |>.take 8}; next words {x.drop i |>.take 12}"
  else
    let code := C.g41 x
    if code.isEmpty then throw (IO.userError "g41 REJECTED although g39 finished")
    let wd := (List.range (code.length / 4)).map fun q =>
      (code.getD (4*q) 0).toNat + 256 * (code.getD (4*q+1) 0).toNat + 65536 * (code.getD (4*q+2) 0).toNat + 16777216 * (code.getD (4*q+3) 0).toNat
    let hx := wd.map fun w => let h := (Nat.toDigits 16 w).asString; String.ofList (List.replicate (8 - h.length) '0') ++ h
    IO.FS.writeFile "Testing/asm/ir-words/cgw.words" ("cgw\n" ++ " ".intercalate hx ++ "\n")
    let hex (l : List UInt8) : String := if l.isEmpty then "-" else String.join (l.map fun b =>
      let s := (Nat.toDigits 16 b.toNat).asString; if s.length == 1 then "0" ++ s else s)
    let ins := ["def f (a : UInt64) : UInt64 := a + 1\n", "def m (x : List UInt8) : List UInt8 := put [] (rd x 0 + 1)\n", "xyz"]
    let cs := ins.map fun s => let x := s.toUTF8.toList; let y := C.m x; hex x ++ (if y.isEmpty then " 1 -" else " 0 " ++ hex y)
    IO.FS.writeFile "Testing/asm/ir-words/cgw.cases" ("\n".intercalate cs ++ "\n")
    IO.println s!"accepted: {code.length / 4} code words; wrote cgw.words/cases ({ins.length} inputs)"

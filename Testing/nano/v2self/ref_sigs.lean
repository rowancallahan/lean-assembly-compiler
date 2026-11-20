import Legacy.Nano.V2.Front
/- reference signatures from Nano/V2/Front.lean (independent typing): per def (oldest first) `name hasInput kind(0 fn / 1 loop) nparams-words result-words`,
words: w/out/buf = 1, prod = sum.  run: lean --run ref_sigs.lean FILE > sigs.txt -/
open Nano.V2B
def Nano.V2B.FT.wd : FT → Nat | .w => 1 | .out => 1 | .buf => 1 | .prod a b => a.wd + b.wd
def main (a : List String) : IO UInt32 := do
  let txt := (← IO.FS.readFile a[0]!).toUTF8.toList
  match flex txt.length txt with
  | none => IO.println "LEX FAIL"; return 1
  | some ts =>
    match pDs (16 * (ts.length + 2)) [] ts with
    | none => IO.println "PARSE FAIL"; return 1
    | some ds =>
      for (nm, inp, ps, r, b) in ds.reverse do
        let k := match b with | .fn _ => 0 | .lp .. => 1
        IO.println s!"{String.fromUTF8! (ByteArray.mk nm.toArray)} {if inp then 1 else 0} {k} {(ps.map FT.wd).foldl (· + ·) 0} {r.wd}"
      return 0

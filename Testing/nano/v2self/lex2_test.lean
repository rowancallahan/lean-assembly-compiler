import Nano.V2Self.C.Lex2
/- reference lexer for S over `List Char` (independent of C.s*), differential test: S text files + random strings.
run: lean --run Testing/nano/v2self/lex2_test.lean FILE...  (prints mismatch count) -/
def isW (c : Char) : Bool := c.isAlphanum && c.toNat < 128 || c == '_' || c == '\''
def ops : List (String × Nat) := [("&&&", 26), ("|||", 27), ("<<<", 28), (">>>", 29), (":=", 9), ("=>", 19), ("==", 23),
  ("(", 6), (")", 7), (":", 8), ("+", 10), ("-", 11), ("*", 12), (";", 13), (",", 15), ("×", 16), ("→", 17), ("|", 18), ("<", 20), ("[", 30), ("]", 31)]
def kws : List (String × Nat) := [("def", 1), ("let", 2), ("UInt64", 3), ("if", 32), ("then", 33), ("else", 34), ("Nat", 35), ("Buf", 36), ("List", 37), ("UInt8", 38), ("len'", 39), ("rd", 40), ("len", 41), ("put", 42), ("bnew", 43), ("bsize", 44), ("bget", 45), ("bset", 46), ("bpush", 47)]
def le8 (v : Nat) : List UInt64 := (List.range 8).map fun i => ((v / 256 ^ i) % 256).toUInt64
partial def ref (cs : List Char) (o : List UInt64) : Option (List UInt64) :=
  match cs with
  | [] => some o
  | c :: r =>
    if c == ' ' || c == '\n' then ref r o else
    match ops.find? fun (s, _) => cs.take s.length == s.toList with
    | some (s, k) => ref (cs.drop s.length) (o ++ [k.toUInt64])
    | none =>
      if c.isDigit then
        let w := cs.takeWhile isW
        if w.all Char.isDigit then ref (cs.drop w.length) (o ++ [5] ++ le8 (w.foldl (fun a d => (a * 10 + (d.toNat - 48)) % 2 ^ 64) 0)) else none
      else if isW c then
        let w := cs.takeWhile isW
        match kws.find? fun (s, _) => s.toList == w with
        | some (_, k) => ref (cs.drop w.length) (o ++ [k.toUInt64])
        | none => ref (cs.drop w.length) (o ++ [14] ++ w.flatMap (fun d => [1, d.toNat.toUInt64]) ++ [0])
      else none
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def pieces : List String := ["def ", "let ", "if ", " then ", " else ", "Nat", "Buf", "List UInt8", "UInt64", "x", "x1", "y'", "12", "007", "99999999999999999999999", "1a", "(", ")", ",", " ", "\n", ":", ":=", "=>", "==", "=", "&", "&&", "&&&", "|", "||", "|||", "<", "<<", "<<<", ">", ">>", ">>>", "≤", "≠", "×", "→", "[", "]", "+", "-", "*", ";", "é", "Int64", "ifx", "rd", "len", "len'", "put", "bnew", "bsize", "bget", "bset", "bpush", "bpushx", "r"]
def gen : Nat → Nat → String → String × Nat
  | 0, s, acc => (acc, s)
  | n+1, s, acc => let s1 := lcg s; gen n s1 (acc ++ pieces[(s1 >>> 33) % pieces.length]!)
def chk (s : String) : Bool :=
  let got := (C.s10 s.toUTF8.toList)
  got == (ref s.toList []).getD []
def rnd : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, r => r
  | k+1, s, (bad, ne) =>
    let (str, s') := gen (k % 30) s ""
    rnd k s' (if chk str then bad else bad + 1, if (ref str.toList []).isSome then ne + 1 else ne)
def firstBad : Nat → Nat → Option String
  | 0, _ => none
  | k+1, s => let (str, s') := gen (k % 30) s ""; if chk str then firstBad k s' else some str
def main (a : List String) : IO Unit := do
  IO.println s!"first mismatch: {repr (firstBad 20000 5)}"
  for f in a do
    let t ← IO.FS.readFile f
    IO.println s!"{f}: tokens {(C.s10 t.toUTF8.toList).length} match {chk t} reject {(ref t.toList []).isNone}"
  IO.println s!"random (mismatches, valid): {rnd 20000 5 (0, 0)}"

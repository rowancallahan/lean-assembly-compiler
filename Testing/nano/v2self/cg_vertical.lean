import Nano.V2Self.C.Gen
/- The vertical example of Astra round 8 for the fused code generator `C.g41` (Nano/V2Self/C/Gen.lean): a fuel loop
copying the input into a buffer, a helper with its own loop returning a pair (sum, count), and the output.
The AST is written by hand in the NANO_V2_IR.md v2 format (tags as in Gen.lean).  Writes
Testing/asm/ir-words/cg_vertical.{words,cases} for Testing/nano/v2self/cg_test.py. -/
namespace V
-- the source (native Lean, the nano subset)
def f : Nat → List UInt8 → UInt64 → Buf → Buf
  | 0, _, _, b => b
  | n + 1, x, i, b => if i < len x then f n x (i + 1) (bpush b (rd x i)) else b
def h : Nat → Buf → UInt64 → UInt64 → UInt64 → UInt64 × UInt64
  | 0, _, _, s, c => (s, c)
  | n + 1, b, i, s, c => if i < bsize b then h n b (i + 1) (s + bget b i) (c + 1) else (s, c)
def m (x : List UInt8) : List UInt8 :=
  let b := f (len' x) x 0 bnew;
  let (s, c) := h (len' x) b 0 0 0;
  put (put [] s) c
end V

-- tags
def CONST : UInt64 := 1
def LOCAL : UInt64 := 2
def BIN : UInt64 := 3
def IF : UInt64 := 4
def LET : UInt64 := 5
def PAIR : UInt64 := 6
def CALL (t : Bool) : UInt64 := if t then 8 else 7
def PRIM (t : Bool) : UInt64 := if t then 9 else 8
def LOOP (t : Bool) : UInt64 := if t then 10 else 9
def CONT (t : Bool) : UInt64 := if t then 11 else 10
def DEF (t : Bool) : UInt64 := if t then 20 else 11
def END (t : Bool) : UInt64 := if t then 21 else 12
def ast (t : Bool) : List UInt64 := [2,
  -- f: fuel 0, i 1, b 2
  (DEF t), 0, 3, 3, 1, 1, (LOOP t),
    LOCAL, 2, 1,
    IF, 2, LOCAL, 1, 1, (PRIM t), 1,
      (CONT t), PAIR, 2, BIN, 1, LOCAL, 1, 1, CONST, 1, (PRIM t), 9, LOCAL, 2, 1, (PRIM t), 2, LOCAL, 1, 1,
      LOCAL, 2, 1,
  (END t),
  -- h: fuel 0, b 1, i 2, s 3, c 4
  (DEF t), 1, 5, 5, 1, 2, (LOOP t),
    PAIR, 2, LOCAL, 3, 1, LOCAL, 4, 1,
    IF, 2, LOCAL, 2, 1, (PRIM t), 6, LOCAL, 1, 1,
      (CONT t), PAIR, 4, LOCAL, 1, 1, BIN, 1, LOCAL, 2, 1, CONST, 1,
        BIN, 1, LOCAL, 3, 1, (PRIM t), 7, LOCAL, 1, 1, LOCAL, 2, 1, BIN, 1, LOCAL, 4, 1, CONST, 1,
      PAIR, 2, LOCAL, 3, 1, LOCAL, 4, 1,
  (END t),
  -- m: b 0, (s, c) 1-2
  (DEF t), 2, 0, 3, 0, 1,
    LET, 0, 1, (CALL t), 0, 3, (PRIM t), 1, CONST, 0, (PRIM t), 5,
    LET, 1, 2, (CALL t), 1, 5, (PRIM t), 1, LOCAL, 0, 1, CONST, 0, CONST, 0, CONST, 0,
    (PRIM t), 4, (PRIM t), 4, (PRIM t), 5, LOCAL, 1, 1, LOCAL, 2, 1,
  (END t)]

def hex (l : List UInt8) : String := if l.isEmpty then "-" else String.join (l.map fun b =>
  let s := (Nat.toDigits 16 b.toNat).asString; if s.length == 1 then "0" ++ s else s)
def main : IO Unit := do
  let code := C.g41 [] (ast true)
  if !(C.g41 [] (ast false)).isEmpty then throw (IO.userError "the old tag table must be rejected")
  -- out-of-frame / empty slot ranges reject: f's first `LOCAL 2 1` (words 8-10) → `LOCAL 3 1` (nslots 3), `LOCAL 250 1`
  if (ast true).getD 8 0 != LOCAL || (ast true).getD 9 0 != 2 then throw (IO.userError "layout of ast changed")
  if !(C.g41 [] ((ast true).set 9 3)).isEmpty then throw (IO.userError "LOCAL beyond nslots must be rejected")
  if !(C.g41 [] ((ast true).set 9 250)).isEmpty then throw (IO.userError "LOCAL slot 250 must be rejected")
  IO.println s!"code bytes: {code.length}"
  let ws := (List.range (code.length / 4)).map fun k =>
    (code.getD (4*k) 0).toUInt64 + 256 * (code.getD (4*k+1) 0).toUInt64 + 65536 * (code.getD (4*k+2) 0).toUInt64 + 16777216 * (code.getD (4*k+3) 0).toUInt64
  let hx := ws.map fun w => let s := (Nat.toDigits 16 w.toNat).asString; String.mk (List.replicate (8 - s.length) '0') ++ s
  IO.FS.writeFile "Testing/asm/ir-words/cg_vertical.words" ("cg vertical\n" ++ " ".intercalate hx ++ "\n")
  let ins : List (List UInt8) := [[], [1], [1, 2, 3], [200, 100, 7, 9], (List.range 40).map (·.toUInt8)]
  let cs := ins.map fun x => let y := V.m x; hex x ++ " " ++ (if y.isEmpty then "1 -" else "0 " ++ hex y)
  IO.FS.writeFile "Testing/asm/ir-words/cg_vertical.cases" ("\n".intercalate cs ++ "\n")
  IO.println (cs)

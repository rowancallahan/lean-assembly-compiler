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
def CALL : UInt64 := 8
def PRIM : UInt64 := 9
def LOOP : UInt64 := 10
def CONT : UInt64 := 11
def DEF : UInt64 := 20
def END : UInt64 := 21
def ast : List UInt64 := [2,
  -- f: fuel 0, i 1, b 2
  DEF, 0, 3, 3, 1, 1, LOOP,
    LOCAL, 2, 1,
    IF, 2, LOCAL, 1, 1, PRIM, 1,
      CONT, PAIR, 2, BIN, 1, LOCAL, 1, 1, CONST, 1, PRIM, 9, LOCAL, 2, 1, PRIM, 2, LOCAL, 1, 1,
      LOCAL, 2, 1,
  END,
  -- h: fuel 0, b 1, i 2, s 3, c 4
  DEF, 1, 5, 5, 1, 2, LOOP,
    PAIR, 2, LOCAL, 3, 1, LOCAL, 4, 1,
    IF, 2, LOCAL, 2, 1, PRIM, 6, LOCAL, 1, 1,
      CONT, PAIR, 4, LOCAL, 1, 1, BIN, 1, LOCAL, 2, 1, CONST, 1,
        BIN, 1, LOCAL, 3, 1, PRIM, 7, LOCAL, 1, 1, LOCAL, 2, 1, BIN, 1, LOCAL, 4, 1, CONST, 1,
      PAIR, 2, LOCAL, 3, 1, LOCAL, 4, 1,
  END,
  -- m: b 0, (s, c) 1-2
  DEF, 2, 0, 3, 0, 1,
    LET, 0, 1, CALL, 0, 3, PRIM, 1, CONST, 0, PRIM, 5,
    LET, 1, 2, CALL, 1, 5, PRIM, 1, LOCAL, 0, 1, CONST, 0, CONST, 0, CONST, 0,
    PRIM, 4, PRIM, 4, PRIM, 5, LOCAL, 1, 1, LOCAL, 2, 1,
  END]

def hex (l : List UInt8) : String := if l.isEmpty then "-" else String.join (l.map fun b =>
  let s := (Nat.toDigits 16 b.toNat).asString; if s.length == 1 then "0" ++ s else s)
def main : IO Unit := do
  let code := C.g41 ast
  IO.println s!"code bytes: {code.length}"
  let ws := (List.range (code.length / 4)).map fun k =>
    (code.getD (4*k) 0) + 256 * (code.getD (4*k+1) 0) + 65536 * (code.getD (4*k+2) 0) + 16777216 * (code.getD (4*k+3) 0)
  let hx := ws.map fun w => let s := (Nat.toDigits 16 w.toNat).asString; String.mk (List.replicate (8 - s.length) '0') ++ s
  IO.FS.writeFile "Testing/asm/ir-words/cg_vertical.words" ("cg vertical\n" ++ " ".intercalate hx ++ "\n")
  let ins : List (List UInt8) := [[], [1], [1, 2, 3], [200, 100, 7, 9], (List.range 40).map (·.toUInt8)]
  let cs := ins.map fun x => let y := V.m x; hex x ++ " " ++ (if y.isEmpty then "1 -" else "0 " ++ hex y)
  IO.FS.writeFile "Testing/asm/ir-words/cg_vertical.cases" ("\n".intercalate cs ++ "\n")
  IO.println (cs)

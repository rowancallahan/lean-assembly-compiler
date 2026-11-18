/- driver for running the S lexer + Par1 parser as a RISC-V program: output = every AST word as 8 little-endian bytes.
selfcompile.lean concatenates Base, Lex2, Par1, this file. -/
import Nano.V2Self.C.Par1
namespace C

def z0 (v : UInt64) (o : List UInt8) : List UInt8 :=
  put (put (put (put (put (put (put (put o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48)) (v >>> 56)

def z1 : Nat → Buf → UInt64 → List UInt8 → List UInt8
  | 0, b, i, o => o
  | n + 1, b, i, o =>
    if bsize b < i then o
    else if bsize b == i then o
    else
      let v := bget b i;
      z1 n b (i + 1) (z0 v o)

def m (x : List UInt8) : List UInt8 := z1 16777216 (y16 (s10 x)) 0 []

end C

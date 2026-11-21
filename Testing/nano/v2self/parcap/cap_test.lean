/- WIDTH CAP regression (parser stage, Lean evaluation of C's Par1): `src k` doubles a tuple through k lets, so the def needs
2^(k+1) − 1 slots.  Par1 must accept k = 19 (2^20 − 1 slots) and reject k = 20 and k = 63 (whose slot count would wrap mod 2^64).
Run: lake env lean Testing/nano/v2self/parcap/cap_test.lean (about 4 min, interpreted).  Full compilers: cap_regress.py. -/
import Nano.Parser.Par1
import Nano.Lexer.Lex2
open C

def capSrc (k : Nat) : List UInt8 :=
  let lets := String.join ((List.range k).map fun i => s!"let a{i+1} := (a{i}, a{i}); ")
  (s!"def f (a0 : UInt64) : UInt64 := {lets}a0\n\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0))\n").toUTF8.toList

#guard (y16 (s10 (capSrc 5))).getD 4 0 == 63
#guard (y16 (s10 (capSrc 19))).getD 4 0 == 1048575
#guard (y16 (s10 (capSrc 20))) == []
#guard (y16 (s10 (capSrc 63))) == []

/- Nano/V2Self/C: the DRIVER.  `m` = lex, parse, inline, expand, assemble, then copy the final `Buf` to the output. -/
import Legacy.Nano.V2Self.Legacy.C.Expand
import Legacy.Nano.V2Self.Legacy.C.Lex
import Legacy.Nano.V2Self.Legacy.C.Parse
namespace C

def m1 : Nat → Buf → UInt64 → List UInt8 → List UInt8
  | 0, b, i, o => o
  | n + 1, b, i, o =>
    let v308 := (if i < bsize b then k0 else k1); if v308 == k1 then o
    else
      let v := bget b i;
      m1 n b (i + 1) (put o v)

def m (x : List UInt8) : List UInt8 := m1 16777216 (a5 (e2 (j8 (r16 (l15 x))))) 0 []

end C

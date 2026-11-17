/- Nano/V2Self/C: the CHAINED stages.  Stage 1 reads the program input (`List UInt8`), every other stage reads the previous
stage's `Buf` (`bget`/`bsize`, borrowed) and all stages write a `Buf` (`q0` = `put`: the low 8 bits, as a word).  Fuel of
stages 2-5 is the numeral 16777216 (they stop on their own conditions).  Lean namespace `C` only to avoid clashes with the
list-based stages; the front-end acceptance script strips `namespace`/`end`. -/
import Nano.V2Self.Prelude
namespace C

def k255 : UInt64 := 255
def q0 (o : Buf) (v : UInt64) : Buf := bpush o (v &&& k255)

end C

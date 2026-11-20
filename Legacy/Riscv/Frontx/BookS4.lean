/- Book survey 4: blocked rows of the survey (BOOK_SURVEY3.md, `book_survey3.csv`) whose first error mentions `Int`,
retried on current `main` (BOOK_S4.md). Each definition is copied verbatim from fp-lean @0abeea5 (`file:line` in the
comment above it); only the `requires` range (the input range of `Int`, as in `IntExamples.lean`), the glue
entry points and the commands are ours. -/
import Legacy.Riscv.Frontx.IntExamples
import Legacy.Riscv.Frontx.Translate
import Legacy.Riscv.Frontx.RecCmd
import Legacy.Riscv.Frontx.IndCmd
import Legacy.Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000

namespace Proven.Frontx.BookS4
open Proven Proven.Frontx Proven.Frontx.IntEx

-- Examples/Monads.lean:316-317 (`namespace Monads.Writer`, fp-lean @0abeea5)
namespace Monads.Writer
def isEven (i : Int) : Bool :=
  i % 2 == 0
end Monads.Writer
frontx_compile Monads.Writer.isEven requires fun i => -2 ^ 63 ≤ i ∧ i < 2 ^ 63

def isEvenAt (xs : ByteArray) (i : Nat) : Bool := Monads.Writer.isEven (i64At xs (i + 0))
frontx_compile isEvenAt requires fun _ i => i + 32 < 2 ^ 64
def isEvenE (xs : ByteArray) : Bool := isEvenAt xs 0
frontx_entry isEvenE
frontx_implementsC isEvenE

end Proven.Frontx.BookS4

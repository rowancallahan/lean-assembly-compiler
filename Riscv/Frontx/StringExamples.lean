/- `String` arguments of calls (NOTES section 23): a call of a translated function passes its byte-array and
`String` parameters through when they are the caller's blocks in the same positions (a `String` is the block of
its UTF-8 bytes, `s.toUTF8`); the length variable of a block other than block 0 is passed like a scalar argument.

lean-svg @df8e663 `LeanSvg/Bytes.lean:55-60`, verbatim (`startsWith` is `ForExamples.startsWith`, lines 46-52). -/
import Riscv.Frontx.ForExamples

namespace Proven.Frontx.Ex

/-- Index of the first occurrence of ASCII `s` at or after `i`, or `bs.size`. -/
def findSeq (bs : ByteArray) (i : Nat) (s : String) : Nat := Id.run do
  let mut j := i
  for _ in [i:bs.size] do
    if startsWith bs j s then return j
    j := j + 1
  return bs.size

-- `requires`: `startsWith`'s precondition for every `j < bs.size`; `with`: the loop invariant (`j` ≤ the index)
frontx_compile findSeq requires fun bs _ s => bs.size + s.toUTF8.size < 2 ^ 64 with fun _ _ _ k _ j => j ≤ k

end Proven.Frontx.Ex

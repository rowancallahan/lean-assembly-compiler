/- Nano/Parser/ParRep: how Par1's tables represent ParSpec's context `Cx` (definitions; the lookup lemmas `v7_lookup` / `v8_lookup` are in ParInv).
Shape codes: 1 UInt64, 2 Buf, 3 List UInt8 (value), 4 Nat (fuel), s ≥ 5: row s - 5 of the shape table at `d7 + 8192 + 3 (s - 5)` = (left code, right code, width).
Binding i (table d9, 4 words): name token position, slot, shape code, input flag.
Def i (table d7, 8 words): +0 name token position, +1 npw (parameter words), +2 number of NON-input parameters (the CALL argument count), +3 result shape code,
+4 loop flag, +5 start of its parameter-code list (cells `d7 + 4096 + start + j`), +6 source arity (all parameters incl. the input and, for loops, the fuel). -/
import Nano.Parser.ParInv
namespace ParInv
open C BufL ParSpec

/-- the shape code `c` denotes the spec shape `s` in the shape table of `h` -/
inductive ShapeCode (h : Buf) : UInt64 → Sh → Prop
  | uw : ShapeCode h 1 .uw
  | bf : ShapeCode h 2 .bf
  | ls : ShapeCode h 3 .ls
  | nt : ShapeCode h 4 .nt
  | pr {c : UInt64} {l r : UInt64} {a b : Sh} :
      5 ≤ c.toNat → c.toNat < 5 + 8192 → bget h (d7 + 8192 + 3 * (c - 5)) = l → bget h (d7 + 8192 + 3 * (c - 5) + 1) = r →
      bget h (d7 + 8192 + 3 * (c - 5) + 2) = (a.width + b.width).toUInt64 →
      ShapeCode h l a → ShapeCode h r b → ShapeCode h c (.p a b)

end ParInv

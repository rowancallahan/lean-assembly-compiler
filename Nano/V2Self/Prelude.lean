/- Nano/V2Self: the nano compiler's stages written in the nano subset (Testing/notes/NANO_V2_CHECKPOINT.md).
The prelude: the primitives nano's own front end knows (`Nano.V2B.frontElab`), as real Lean definitions at the root
namespace (same text as Testing/nano/v2f/Prelude.lean.txt).  Stage sources use no `namespace`/`open`; names are
one letter + digits/`_` (locals b c d f g h i k n o p q s t u v w x y z; defs: a = asm, e = expand, j = inline,
l = lex, r = parse, k = constants, m = main). -/
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64
def len (xs : List UInt8) : UInt64 := xs.length.toUInt64
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
def len' (xs : List UInt8) : Nat := xs.length
abbrev Buf := List UInt64
def bnew : Buf := []
def bsize (b : Buf) : UInt64 := b.length.toUInt64
def bget (b : Buf) (i : UInt64) : UInt64 := b.getD i.toNat 0
def bset (b : Buf) (i v : UInt64) : Buf := b.set i.toNat v
def bpush (b : Buf) (v : UInt64) : Buf := b ++ [v]
def bpop (b : Buf) : Buf := b.dropLast

/- TRUSTED bootstrap prelude (the Lean compiler is trusted for B1): the nano prelude with Array-backed buffers so the native B1 is fast.
Same semantics as Nano/V2Self/Prelude.lean (List-backed): `List UInt8` of the S text is replaced by `Array UInt8` textually by build_B1.py;
rd/len/len'/put/bnew/bsize/bget/bset/bpush agree: out-of-range reads give 0, out-of-range `bset` is a no-op (List.set), put/bpush append. -/
def rd (xs : Array UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64
def len (xs : Array UInt8) : UInt64 := xs.size.toUInt64
def put (o : Array UInt8) (b : UInt64) : Array UInt8 := o.push b.toUInt8
def len' (xs : Array UInt8) : Nat := xs.size
abbrev Buf := Array UInt64
def bnew : Buf := #[]
def bsize (b : Buf) : UInt64 := b.size.toUInt64
def bget (b : Buf) (i : UInt64) : UInt64 := b.getD i.toNat 0
def bset (b : Buf) (i v : UInt64) : Buf := b.setIfInBounds i.toNat v
def bpush (b : Buf) (v : UInt64) : Buf := b.push v

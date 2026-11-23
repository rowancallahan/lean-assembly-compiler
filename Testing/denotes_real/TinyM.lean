-- DENOTES-3 nano tie: the tiny nano program `def m (x : List UInt8) : List UInt8 := put [] 1`
-- with nano's prelude `put` (Nano/Main/Prelude.lean) and the equations the bridge reads.
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
def m (x : List UInt8) : List UInt8 := put [] 1
theorem m_eq : ∀ x : List UInt8, m x = put [] 1 := fun _ => rfl
theorem put_one : put [] 1 = [UInt8.ofNat 1] := by decide
theorem br_litN : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n := fun _ => rfl

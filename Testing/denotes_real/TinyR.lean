-- DENOTES-3: an input-dependent nano program `def m (x : List UInt8) : List UInt8 := put [] (rd x 0 + 1)`
-- with nano's prelude `rd`, `put` (Nano/Main/Prelude.lean, same text) and the equations the bridge reads.
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]
def m (x : List UInt8) : List UInt8 := put [] (rd x 0 + 1)
theorem m_eq : ∀ x : List UInt8, m x = put [] (rd x 0 + 1) := fun _ => rfl
theorem r_nil : put [] (rd [] 0 + 1) = [UInt8.ofNat 1] := rfl
theorem r_cons : ∀ (b : Nat) (l : List UInt8), put [] (rd (UInt8.ofNat b :: l) 0 + 1) = [UInt8.ofNat (Nat.succ b)] := by
  intro b l
  simp only [put, rd, List.nil_append, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat]
theorem u8_wrap : UInt8.ofNat 256 = UInt8.ofNat 0 := rfl
theorem br_litN : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n := fun _ => rfl
theorem outParam_eq : outParam.{2} Type = Type := rfl

abbrev Mem := Nat → UInt64
def blockEnd (p c : Nat) := p + 16 + 8*c
def Foot (p c q : Nat) : Prop := p ≤ q ∧ q < blockEnd p c

structure BufferRep (xs : List UInt64) (p c : Nat) (m : Mem) : Prop where
  aligned : p % 8 = 0
  bound   : xs.length ≤ c
  capWord : c < 2^64
  lenHdr  : m p = UInt64.ofNat xs.length
  capHdr  : m (p+8) = UInt64.ofNat c
  data    : ∀ i (hi : i < xs.length), m (p+16+8*i) = xs[i]

structure LiveRep {k : Nat} (xs : Fin k → List UInt64)
    (ptr cap : Fin k → Nat) (top : Nat) (m : Mem) : Prop where
  rep   : ∀ i, BufferRep (xs i) (ptr i) (cap i) m
  below : ∀ i, blockEnd (ptr i) (cap i) ≤ top
  apart : ∀ i j, i ≠ j → ∀ q,
    Foot (ptr i) (cap i) q → ¬ Foot (ptr j) (cap j) q

def nextCap (c : Nat) := if c = 0 then 1 else 2*c

def GrowCorrect
    (runGrow : Nat → Nat → Nat → UInt64 → Mem →
      Option (Nat × Nat × Mem)) : Prop :=
  ∀ (xs : List UInt64) (p c top limit : Nat) (v : UInt64) (m : Mem),
    BufferRep xs p c m → xs.length = c → blockEnd p c ≤ top →
    top % 8 = 0 → limit < 2^64 → blockEnd top (nextCap c) ≤ limit →
    ∃ m', runGrow p top limit v m =
            some (top, blockEnd top (nextCap c), m') ∧
          BufferRep (xs ++ [v]) top (nextCap c) m' ∧
          ∀ q, ¬ Foot top (nextCap c) q → m' q = m q

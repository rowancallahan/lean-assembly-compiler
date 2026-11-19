/- Buf (= List UInt64) read/write lemmas for proofs about C's heap-machine stages (Par1, Gen).
`bget b i = b.getD i.toNat 0`, `bset b i v = b.set i.toNat v`, `bpush b v = b ++ [v]`. -/
import Nano.V2Self.Prelude

namespace BufL

@[simp] theorem bsize_bset (b : Buf) (i v : UInt64) : bsize (bset b i v) = bsize b := by simp [bsize, bset]

theorem bget_bset_same (b : Buf) (i v : UInt64) (h : i.toNat < b.length) : bget (bset b i v) i = v := by
  simp [bget, bset, List.getD, h]

theorem bget_bset_other (b : Buf) (i j v : UInt64) (h : i.toNat ≠ j.toNat) : bget (bset b i v) j = bget b j := by
  simp [bget, bset, List.getD, h]

/-- the one checked-write lemma: reading after a write -/
theorem bget_bset (b : Buf) (i j v : UInt64) :
    bget (bset b i v) j = if i.toNat = j.toNat ∧ i.toNat < b.length then v else bget b j := by
  by_cases h1 : i.toNat = j.toNat
  · by_cases h2 : i.toNat < b.length
    · have : i = j := UInt64.toNat_inj.mp h1
      subst this; simp [bget_bset_same _ _ _ h2, h2]
    · have h3 : ¬ j.toNat < b.length := by omega
      simp [bget, bset, List.getD, h1, h2, h3]
  · simp [bget_bset_other _ _ _ _ h1, h1]

theorem length_bset (b : Buf) (i v : UInt64) : (bset b i v).length = b.length := by simp [bset]

end BufL

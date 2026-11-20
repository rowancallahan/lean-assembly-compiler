/- The fixup lemma (Astra-11): Gen's jump emission and patching (`g19` / `g20`, Nano/V2Self/C/Gen.lean).
A patched placeholder (`g20 r o p`, no error) is the word C emits for J's `jal x0, (h − p)` — the jump from word p to
the current end h of the code — and every other word is unchanged; `g19` appends the same kind of word.  With
`SimW.encJ` this is the word `sim_stepW` runs. -/
import Nano.V2Self.Proof.Machine.RvEnc
import Nano.V2Self.Proof.Gen.BufL

namespace Fixup

/-- C's jump offset `(b − a) <<< 2` is the two's-complement `4·(b − a)` -/
theorem off_eq (a b : UInt64) : (b - a) <<< 2 = UInt64.ofInt (4 * ((b.toNat : Int) - a.toNat)) := by
  apply UInt64.toBitVec_inj.mp
  rw [SimW.ofInt_bv']
  apply BitVec.eq_of_toNat_eq
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp [UInt64.toBitVec_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ofInt, Nat.shiftLeft_eq]
  omega

end Fixup

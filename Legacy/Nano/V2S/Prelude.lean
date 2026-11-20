/- nano v2 source style (Testing/notes/NANO_V2_SRC.md): the primitives a restricted stage may use besides UInt64
arithmetic, comparisons, `if`, `let`, calls and fuel-bounded self-recursion (a `Nat` fuel argument matched as
`0` / `n + 1`).  The input is read only through `rd`/`len`, the output is extended only through `put`. -/
namespace Nano.V2S

/-- input byte `i` as a word (0 past the end) -/
def rd (xs : List UInt8) (i : UInt64) : UInt64 := (xs.getD i.toNat 0).toUInt64

/-- the input length as a word -/
def len (xs : List UInt8) : UInt64 := xs.length.toUInt64

/-- append one output byte (the low 8 bits of `b`) -/
def put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]

theorem rd_lt (xs : List UInt8) (i : UInt64) : rd xs i < 256 := by
  unfold rd; rw [UInt64.lt_iff_toNat_lt]; simpa using UInt8.toNat_lt _

theorem rd_drop (x : UInt8) (xs : List UInt8) (i : UInt64) (h : i.toNat < (x :: xs).length) :
    rd (x :: xs) i = if i = 0 then x.toUInt64 else rd xs (i - 1) := by
  unfold rd
  by_cases h0 : i = 0
  · subst h0; simp
  · have : i.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [if_neg h0, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    obtain ⟨n, hn⟩ : ∃ n, i.toNat = n + 1 := ⟨i.toNat - 1, by omega⟩
    simp [hn]

/-- reading at a word index is reading the list -/
theorem rd_get (xs : List UInt8) (i : Nat) (h : i < 2 ^ 64) : rd xs i.toUInt64 = (xs.getD i 0).toUInt64 := by
  unfold rd; congr; simp; omega

/-! word buffers (work stacks): a list of words, the newest at the end; reads past the end give 0 -/

def bget (b : List UInt64) (i : UInt64) : UInt64 := b.getD i.toNat 0
def bsize (b : List UInt64) : UInt64 := b.length.toUInt64
def bpush (b : List UInt64) (v : UInt64) : List UInt64 := b ++ [v]
def bpop (b : List UInt64) : List UInt64 := b.dropLast

end Nano.V2S

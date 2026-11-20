/- Nano/V2Self/Proof/Parser/ParInvFlatM: the FINISH / FLATTEN / CLOSE tasks of Par1 at cell level (parser lead).
Output words are appended with `bpush` at the end of the heap, everything else is below: `v1_append` lets every task be written as
"low-cell effect `++` appended words".
* `v144_eq` (task 83, def close): `[21]`, def count + 1, push task 60;
* `v143_eq` (task 82, flatten a sibling chain): no output; skip an input local, else push 81 (node) above 82 (rest);
* `v142_eq` (task 81, flatten one node): the header words `hdrW` (or none for a one-component CONTINUE tuple), push 82 for the children;
* `v141_eq` (task 80, FINISH a def): the checks, the 6 header words, push 81 (body) above 83. -/
import Nano.V2Self.Proof.Parser.ParInvVal
namespace ParInv
open C BufL

theorem bget_append_lt (h ws : Buf) (i : UInt64) (hi : i.toNat < h.length) : bget (h ++ ws) i = bget h i := by
  simp [bget, List.getD, List.getElem?_append_left hi]

theorem bset_append_lt (h ws : Buf) (i v : UInt64) (hi : i.toNat < h.length) : bset (h ++ ws) i v = bset h i v ++ ws := by
  simp [bset, List.set_append, hi]

theorem bpush_eq (h : Buf) (v : UInt64) : bpush h v = h ++ [v] := rfl
theorem k0v : k0 = 0 := rfl
theorem k1v : k1 = 1 := rfl

theorem taskIdx (g : UInt64) (hg : g < d12) :
    (d1 + 3 * g).toNat = 64 + 3 * g.toNat ∧ (d1 + 3 * g + 1).toNat = 65 + 3 * g.toNat ∧ (d1 + 3 * g + 2).toNat = 66 + 3 * g.toNat := by
  have e : (d12 : UInt64).toNat = 4096 := rfl
  have hg' := UInt64.lt_iff_toNat_lt.mp hg
  rw [e] at hg'
  have e0 : (d1 + 3 * g).toNat = 64 + 3 * g.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, d1v]; simp; omega
  refine ⟨e0, ?_, ?_⟩
  · rw [UInt64.toNat_add, e0]; simp; omega
  · rw [UInt64.toNat_add, e0]; simp; omega

/-- the task push writes only the task region and h[5] -/
theorem v1_append (h ws : Buf) (c a b : UInt64) (hl : 147520 ≤ h.length) : v1 (h ++ ws) c a b = v1 h c a b ++ ws := by
  have h5 : bget (h ++ ws) 5 = bget h 5 := bget_append_lt _ _ _ (by simp; omega)
  unfold v1
  rw [h5]
  split
  · rename_i hlt
    obtain ⟨e0, e1, e2⟩ := taskIdx _ hlt
    have hg := UInt64.lt_iff_toNat_lt.mp hlt
    have e12 : (d12 : UInt64).toNat = 4096 := rfl
    rw [e12] at hg
    simp only []
    rw [bset_append_lt _ _ _ _ (by rw [e0]; omega), bset_append_lt _ _ _ _ (by rw [length_bset, e1]; omega),
      bset_append_lt _ _ _ _ (by rw [length_bset, length_bset, e2]; omega)]
    rw [bget_append_lt _ _ _ (by simp [length_bset]; omega), bset_append_lt _ _ _ _ (by simp [length_bset]; omega)]
  · exact bset_append_lt _ _ _ _ (by simp; omega)

theorem v1_length (h : Buf) (c a b : UInt64) : (v1 h c a b).length = h.length := by
  unfold v1; split <;> simp [length_bset]

/-- **task 83** (`v144`, close the def): `21`, def count + 1, then the next def (task 60) -/
theorem v144_eq (h : Buf) (a b : UInt64) (hl : 147520 ≤ h.length) :
    v144 h a b = v1 (bset h 12 (bget h 12 + 1)) 60 0 0 ++ [21] := by
  unfold v144
  simp only [bpush_eq]
  rw [bget_append_lt _ _ _ (by simp; omega), bset_append_lt _ _ _ _ (by simp; omega), v1_append _ _ _ _ _ (by simp [length_bset]; omega)]

/-- **task 82** (`v143`, the sibling chain from `a`, `b` nodes left): an input local is skipped, any other node is flattened (task 81)
before the rest of the chain (task 82); no output -/
theorem v143_eq (h : Buf) (a b : UInt64) :
    v143 h a b = if b = 0 then h else
      if inpC h a = 1 then v1 h 82 (bget h ((d5 + 8*a) + 7)) (b - 1)
      else v1 (v1 h 82 (bget h ((d5 + 8*a) + 7)) (b - 1)) 81 a 0 := by
  unfold v143 inpC
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, if_false, beq_iff_eq]

/-- the header words of task 81 (`v142`): tag, then the count (PAIR) / payload 1 (tags < 10), then payload 2 (LOCAL, LET) or
`p2 − #input children` (CALL) -/
def hdrW (t x y n6 c8 : UInt64) : List UInt64 :=
  [t] ++ (if t == 6 then [n6] else if t < 10 then [x] else []) ++
    (if t == 2 then [y] else if t == 5 then [y] else if t == 8 then [y - c8] else [])

/-- the three conditional pushes of `v142` -/
theorem pushes_eq (h : Buf) (t x y n6 c8 : UInt64) :
    (let h1 := bpush h t
     let h2 := if t == 6 then bpush h1 n6 else if t < 10 then bpush h1 x else h1
     if t == 2 then bpush h2 y else if t == 5 then bpush h2 y else if t == 8 then bpush h2 (y - c8) else h2) = h ++ hdrW t x y n6 c8 := by
  simp only [bpush_eq, hdrW]
  by_cases h6 : t = 6
  · subst h6; simp
  by_cases h2 : t = 2
  · subst h2; simp
  by_cases h5 : t = 5
  · subst h5; simp
  by_cases h8 : t = 8
  · subst h8; simp
  simp [h6, h2, h5, h8]
  split <;> simp

/-- **task 81** (`v142`, flatten node `a`): `t x y z n` = tag, payloads, first child, child count; `c` = input-local children -/
theorem v142_eq (h : Buf) (a b : UInt64) (hl : 147520 ≤ h.length) (t x y z n c : UInt64)
    (ht : bget h ((d5 + 8*a) + 0) = t) (hx : bget h ((d5 + 8*a) + 1) = x) (hy : bget h ((d5 + 8*a) + 2) = y)
    (hz : bget h ((d5 + 8*a) + 5) = z) (hn : bget h ((d5 + 8*a) + 6) = n) (hc : v205 16777216 h z n 0 = c) :
    v142 h a b =
      if t = 6 ∧ n - c = 1 then v1 h 82 z n
      else
        v1 h 82 (if t = 9 ∧ x < 4 then bget h ((d5 + 8*z) + 7) else z) (if t = 9 ∧ x < 4 then n - 1 else n) ++
          hdrW t x y (n - c) c := by
  unfold v142
  simp only [ht, hx, hy, hz, hn, hc, k0v, k1v]
  rw [pushes_eq, v1_append _ _ _ _ _ hl]
  by_cases h6 : t = 6
  · subst h6
    by_cases e : n - c = 1
    · simp [e]
    · simp [e, hdrW]
  · simp only [h6, false_and, if_false, beq_iff_eq]
    have hw : hdrW t x y n (if t = 8 then c else 0) = hdrW t x y (n - c) c := by
      unfold hdrW
      by_cases h8 : t = 8
      · subst h8; simp
      · simp [h8, h6]
    by_cases h9 : t = 9 ∧ x < 4
    · obtain ⟨rfl, h4⟩ := h9
      simp [h4]; simpa using hw
    · by_cases h9' : t = 9
      · subst h9'
        have hx4 : ¬ x < 4 := fun e => h9 ⟨rfl, e⟩
        simp [hx4]; simpa using hw
      · simp [h9']; exact hw

/-- the width of a shape code (`v9`, written to the scratch cell 31) -/
def cwC (h : Buf) (c : UInt64) : UInt64 := if c < 5 then 1 else bget h ((d7 + 8192) + 3*(c - 5) + 2)

/-- **task 80** (`v141`, FINISH a def): exactly one operand `z` whose shape code is the def's result code and which is not the input
local; then the header `20, def id, npw, nslots, loop flag, result width` and the tasks 81 (body) above 83 (close) -/
theorem v141_eq (h : Buf) (a b : UInt64) (hl : 147520 ≤ h.length) :
    v141 h a b =
      let z := bget h (d3 + bget h 8 - 1)
      let f := d7 + 8 * bget h 12
      if bget h 8 = 1 ∧ bget h ((d5 + 8 * z) + 3) = bget h (f + 3) ∧ inpC h z ≠ 1 then
        v1 (v1 (bset h 31 (cwC h (bget h (f + 3)))) 83 0 0) 81 z 0 ++
          [20, bget h 12, bget h (f + 1), bget h 11, bget h (f + 4), cwC h (bget h (f + 3))]
      else bset h 0 0 := by
  unfold v141
  simp only [v9, bpush_eq, cwC]
  generalize hz : bget h (d3 + bget h 8 - 1) = z
  generalize hX : (if bget h (d7 + 8 * bget h 12 + 3) < 5 then (1 : UInt64)
    else bget h (d7 + 8192 + 3 * (bget h (d7 + 8 * bget h 12 + 3) - 5) + 2)) = X
  have L : 31 < h.length := by omega
  have g31 : bget (bset h 31 X) 31 = X := bget_bset_same _ _ _ L
  have g12 : bget (bset h 31 X ++ [20]) 12 = bget h 12 := by
    rw [bget_append_lt _ _ _ (by rw [length_bset]; show 12 < h.length; omega)]; exact bget_bset_other _ _ _ _ (by decide)
  rw [g12]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [g31]
  rw [v1_append _ _ _ _ _ (by rw [length_bset]; exact hl), v1_append _ _ _ _ _ (by rw [v1_length, length_bset]; exact hl)]
  unfold inpC
  by_cases h8 : bget h 8 = 1
  · simp only [h8, beq_self_eq_true, if_true, true_and, beq_iff_eq]
    by_cases hs : bget h (d5 + 8 * z + 3) = bget h (d7 + 8 * bget h 12 + 3)
    · simp only [hs, if_true, true_and]
      split <;> simp_all
    · simp [hs]
  · simp [h8]

end ParInv

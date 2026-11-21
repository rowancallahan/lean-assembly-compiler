/- Nano/Parser/ParInvNum: the numeral reader `v87` (box C): the machine's OR of the 8 shifted byte words is ParSpec's
`bytesVal` (byte words < 256 are part of `TokAt`), and the value is below 2^64. -/
import Nano.Parser.ParInvLetSemi
namespace ParInv
open C BufL ParSpec ParRun

theorem or_step (acc b : UInt64) (k : Nat) (sh : UInt64) (hsh : sh.toNat = 8 * k) (hk : k ≤ 7) (ha : acc.toNat < 2 ^ (8 * k))
    (hb : b.toNat < 256) : (acc ||| (b <<< sh)).toNat = acc.toNat + 2 ^ (8 * k) * b.toNat := by
  have e1 : (sh.toNat % 64) = 8 * k := by rw [hsh]; omega
  have p8 : 2 ^ (8 * k) * b.toNat < 2 ^ 64 := by
    have : 2 ^ (8 * k) * b.toNat < 2 ^ (8 * k) * 256 := Nat.mul_lt_mul_of_pos_left hb (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * k) * 256 = 2 ^ (8 * k + 8) := by rw [Nat.pow_add]
    have h3 : 2 ^ (8 * k + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, e1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact p8),
    Nat.or_comm, Nat.mul_comm b.toNat, ← Nat.two_pow_add_eq_or_of_lt ha]
  omega

theorem v87_word (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (h0 : b0.toNat < 256) (h1 : b1.toNat < 256) (h2 : b2.toNat < 256)
    (h3 : b3.toNat < 256) (h4 : b4.toNat < 256) (h5 : b5.toNat < 256) (h6 : b6.toNat < 256) (h7 : b7.toNat < 256) :
    (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)).toNat =
      bytesVal ([b0, b1, b2, b3, b4, b5, b6, b7].map UInt64.toNat) := by
  have s1 := or_step b0 b1 1 8 rfl (by decide) (by simpa using h0) h1
  have s2 := or_step (b0 ||| (b1 <<< 8)) b2 2 16 rfl (by decide) (by rw [s1]; omega) h2
  have s3 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16)) b3 3 24 rfl (by decide) (by rw [s2, s1]; omega) h3
  have s4 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)) b4 4 32 rfl (by decide) (by rw [s3, s2, s1]; omega) h4
  have s5 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32)) b5 5 40 rfl (by decide)
    (by rw [s4, s3, s2, s1]; omega) h5
  have s6 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40)) b6 6 48 rfl (by decide)
    (by rw [s5, s4, s3, s2, s1]; omega) h6
  have s7 := or_step (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48)) b7 7 56 rfl
    (by decide) (by rw [s6, s5, s4, s3, s2, s1]; omega) h7
  rw [s7, s6, s5, s4, s3, s2, s1]
  simp [bytesVal]; omega

theorem TokAt.num_inv {h : Buf} {p : UInt64} {v : Nat} {rest : List Tok} (r : TokAt h p (.num v :: rest)) :
    ∃ bs : List UInt64, p < bget h 7 ∧ bget h (d11 + p) = 5 ∧ bs.length = 8 ∧
      (∀ i, i < 8 → bget h (d11 + (p + 1 + i.toUInt64)) = bs.getD i 0) ∧ (∀ b ∈ bs, b.toNat < 256) ∧
      v = bytesVal (bs.map UInt64.toNat) ∧ TokAt h (p + 9) rest := by
  cases r with
  | num bs a b c d f x => exact ⟨bs, a, b, c, d, f, rfl, x⟩

/-- **numerals**: `v87` stores the token's value (< 2^64) in h[31] -/
theorem v87_tok {h : Buf} {p : UInt64} {v : Nat} {rest : List Tok} (r : TokAt h p (.num v :: rest)) (hn : (bget h 7).toNat < 2 ^ 32) :
    v87 h p = bset h 31 v.toUInt64 ∧ v < 2 ^ 64 ∧ TokAt h (p + 9) rest ∧ bget h (d11 + p) = 5 := by
  obtain ⟨bs, hp, h5, hl, hc, hb, hv, tr⟩ := r.num_inv
  have hp' := UInt64.lt_iff_toNat_lt.mp hp
  match bs, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have cell : ∀ (i : Nat) (k : UInt64), i < 8 → k.toNat = i + 1 → bget h (d11 + (p + k)) = [b0, b1, b2, b3, b4, b5, b6, b7].getD i 0 := by
      intro i k hi hk
      rw [← hc i hi]; congr 2
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hk]; simp; omega
    have w := v87_word b0 b1 b2 b3 b4 b5 b6 b7 (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
      (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp)) (hb _ (by simp))
    rw [← hv] at w
    have vl : v < 2 ^ 64 := by rw [← w]; exact UInt64.toNat_lt _
    refine ⟨?_, vl, tr, h5⟩
    simp only [v87]
    rw [cell 0 1 (by decide) rfl, cell 1 2 (by decide) rfl, cell 2 3 (by decide) rfl, cell 3 4 (by decide) rfl,
      cell 4 5 (by decide) rfl, cell 5 6 (by decide) rfl, cell 6 7 (by decide) rfl, cell 7 8 (by decide) rfl]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [w]; simp; omega

theorem mkNode_leaf0 (st : St) (t a b : Nat) (sh : Sh) : mkNode st t a b (some sh) false 0 = some (leaf st t a b sh) := by
  simp [mkNode, leaf]

/-- a numeral at the cursor becomes a CONST leaf (v87, cursor + 9, `v5 … 1 v 0 1 0 0`) -/
theorem rep_const {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hnf : fs.all (fun f => !f.isFlat))
    (hc : bget h (d11 + bget h 3) = 5)
    (hs : bget (v5 (bset (v87 h (bget h 3)) 3 (bget (v87 h (bget h 3)) 3 + 9)) 1 (bget (v87 h (bget h 3)) 31) 0 1 0 0) 0 ≠ 0) :
    ∃ v rest, st.toks = .num v :: rest ∧
      Rep (v5 (bset (v87 h (bget h 3)) 3 (bget (v87 h (bget h 3)) 3 + 9)) 1 (bget (v87 h (bget h 3)) 31) 0 1 0 0) ts
        (leaf { st with toks := rest } 1 v 0 .uw) fs := by
  rcases tok_cases r.2.2.2.1 r.1 with ⟨_, h0⟩ | ⟨v, rest, et, _⟩ | ⟨_, _, _, h14⟩ | ⟨t, _, _, ht, _, t5, _, _⟩
  · rw [hc] at h0; exact absurd h0 (by decide)
  · have p3 := r.2.2.2.1
    rw [et] at p3
    obtain ⟨hn7, hl, har⟩ := rep_bounds r
    obtain ⟨E87, vl, tr, _⟩ := v87_tok p3 hn7
    rw [E87] at hs ⊢
    have g31 : bget (bset h 31 v.toUInt64) 31 = v.toUInt64 := bget_bset_eq _ _ _ _ rfl (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)
    have g3 : bget (bset h 31 v.toUInt64) 3 = bget h 3 := bget_bset' _ _ _ _ (by decide)
    rw [g31, g3] at hs ⊢
    have R1 := rep_31 r v.toUInt64
    have tr' : TokAt (bset h 31 v.toUInt64) (bget h 3 + 9) rest :=
      tokAt_frame ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)⟩ hn7 tr
    have R2 := rep_set3 R1 tr'
    obtain ⟨st', em, R3⟩ := rep_v5g R2 hnf 0 1 v 0 (some .uw) false 1 .uw (by decide) (fun _ _ => ⟨vl, by decide⟩) (by decide)
      (by simpa [b01] using hs)
    rw [mkNode_leaf0] at em
    cases em
    exact ⟨v, rest, et, by simpa [b01] using R3⟩
  · rw [hc] at h14; exact absurd h14 (by decide)
  · rw [hc] at ht; exact absurd ht.symm t5

/-! ## task 49: `shiftNum op` (v102): the shift amount numeral, then the BIN node -/
theorem h_shiftNum {h ts : Buf} {st : St} {op : Nat} {fs : List Frame} (r : Rep h ts st (.shiftNum op :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.shiftNum op) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = v102 h1 a b := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v102, UInt64.add_zero] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c5 : bget h1 (d11 + bget h1 3) = 5
  · simp only [c5, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨v, rest, et, R2⟩ := rep_const R1 hnf c5 (pushOK hs)
    have R3 := rep_push (.mkBin op) a 0 R2 (by simp [inDefF, Frame.isDefs]) ea hs
    exact ⟨[.mkBin op], _, by simp [stepF, et], R3⟩
  · have n : (bget h1 (d11 + bget h1 3) == 5) = false := by simpa using c5
    simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv

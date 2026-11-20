/- Nano/V2Self/Proof/Parser/ParInvPrev: the token BEFORE the cursor (box C, for the parser lead's `hprev`, task 73).
No Rep change: `st.all` is constant and the token cells are fixed by `TokensAt h ts` (a Rep conjunct), so `TokAt h 0 st.all`
transfers along the run (`tokAgree_of_tokensAt` + `tokAt_frameN`).  Given `st.all = pre ++ st.toks` (Layer 2) and both TokAt facts,
the cursor is where `pre` ends (`tokAt_pos`), and the cell before it is the last keyword of `pre`, the name terminator 0 of a
last identifier, or a byte of a last number (`prev_cell`).  A number's last byte can be 35, so `hprev` also needs
"the token before the cursor is not a number" from Layer 2 (at task 73 it ends a type). -/
import Nano.V2Self.Proof.Parser.ParInvExpr
namespace ParInv
open C BufL ParSpec ParRun

/-- size in cells of a token -/
def tokSz : Tok → Nat
  | .k _ => 1
  | .num _ => 9
  | .id x => 2 + 2 * x.length

theorem TokAt.cons_pos {h : Buf} {p : UInt64} {t : Tok} {r : List Tok} (x : TokAt h p (t :: r)) (hn : (bget h 7).toNat < 2 ^ 32) :
    p.toNat + tokSz t ≤ (bget h 7).toNat ∧ TokAt h (p + (tokSz t).toUInt64) r := by
  cases x with
  | kw t' a _ _ _ _ tl =>
    have := tl.le; have hp := UInt64.lt_iff_toNat_lt.mp a
    exact ⟨by simp only [tokSz]; omega, by simpa [tokSz] using tl⟩
  | num bs a _ _ _ _ tl =>
    have := tl.le; have hp := UInt64.lt_iff_toNat_lt.mp a
    have e9 : (p + 9).toNat = p.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
    rw [e9] at this
    exact ⟨by simp only [tokSz]; omega, by simpa [tokSz] using tl⟩
  | id nm a tl =>
    have := tl.le; have hk := a.2.2
    have e : (p + 2 + 2 * nm.length.toUInt64).toNat = p.toNat + 2 + 2 * nm.length := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    have es : p + 2 + 2 * nm.length.toUInt64 = p + (tokSz (.id (nm.map UInt64.toNat))).toUInt64 := by
      apply UInt64.toNat_inj.mp; rw [e]; simp [tokSz]; omega
    rw [e] at this
    exact ⟨by simp only [tokSz, List.length_map]; omega, by rw [← es]; exact tl⟩

/-- the position of a token suffix is determined (it ends at h[7]) -/
theorem tokAt_pos {h : Buf} (hn : (bget h 7).toNat < 2 ^ 32) :
    ∀ {toks : List Tok} {p q : UInt64}, TokAt h p toks → TokAt h q toks → p = q
  | [], p, q, x, y => by cases x with | nil e => cases y with | nil e' => rw [e, e']
  | t :: r, p, q, x, y => by
    obtain ⟨xb, xt⟩ := x.cons_pos hn
    obtain ⟨yb, yt⟩ := y.cons_pos hn
    have e := tokAt_pos hn xt yt
    apply UInt64.toNat_inj.mp
    have ex : (p + (tokSz t).toUInt64).toNat = p.toNat + tokSz t := by rw [UInt64.toNat_add]; simp; omega
    have ey : (q + (tokSz t).toUInt64).toNat = q.toNat + tokSz t := by rw [UInt64.toNat_add]; simp; omega
    have := congrArg UInt64.toNat e; omega

/-- the terminator of a name sequence -/
theorem nameSeq_end {h : Buf} : ∀ (l : List UInt64) (a : UInt64), a.toNat + 2 * l.length < 2 ^ 40 → NameSeq h a l →
    bget h (d11 + (a + 2 * l.length.toUInt64)) = 0
  | [], a, _, x => by simpa [NameSeq] using x
  | c :: t, a, ha, x => by
    simp only [NameSeq] at x
    simp at ha
    have e := nameSeq_end t (a + 2) (by rw [UInt64.toNat_add]; simp; omega) x.2.2
    have q : a + 2 + 2 * t.length.toUInt64 = a + 2 * (c :: t).length.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    rw [← q]; exact e

/-- **the cell before the cursor**: with `TokAt h 0 (pre ++ toks)` and the cursor at `toks`, the cell just before it is the last
keyword of `pre`, or 0 (a last identifier's terminator), or `pre` ends with a number -/
theorem prev_cell {h : Buf} (hn : (bget h 7).toNat < 2 ^ 32) :
    ∀ {pre toks : List Tok} {p0 q : UInt64}, TokAt h p0 (pre ++ toks) → TokAt h q toks → pre ≠ [] →
      (∃ t, pre.getLast? = some (.k t) ∧ bget h (d11 + (q - 1)) = t.toUInt64) ∨
      (∃ x, pre.getLast? = some (.id x) ∧ bget h (d11 + (q - 1)) = 0) ∨ (∃ v, pre.getLast? = some (.num v))
  | [], _, _, _, _, _, hne => absurd rfl hne
  | t :: r, toks, p0, q, x, y, _ => by
    simp only [List.cons_append] at x
    obtain ⟨xb, xt⟩ := x.cons_pos hn
    match r with
    | [] =>
      simp only [List.nil_append] at xt
      have eq := tokAt_pos hn xt y
      subst eq
      simp only [List.getLast?_singleton, Option.some.injEq]
      cases x with
      | kw t' a b _ _ _ =>
        left; refine ⟨t'.toNat, rfl, ?_⟩
        have e : p0 + (tokSz (.k t'.toNat)).toUInt64 - 1 = p0 := by simp [tokSz]
        rw [e, b]; simp
      | num bs _ _ _ _ _ _ => right; right; exact ⟨_, rfl⟩
      | id nm a _ =>
        right; left; refine ⟨_, rfl, ?_⟩
        have hk := a.2.2
        have e : p0 + (tokSz (.id (nm.map UInt64.toNat))).toUInt64 - 1 = p0 + 1 + 2 * nm.length.toUInt64 := by
          apply UInt64.toNat_inj.mp
          have e1 : (p0 + (tokSz (.id (nm.map UInt64.toNat))).toUInt64).toNat = p0.toNat + 2 + 2 * nm.length := by
            rw [UInt64.toNat_add]; simp [tokSz]; omega
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e1]; simp; omega)), e1]
          rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
        rw [e]
        exact nameSeq_end nm (p0 + 1) (by rw [UInt64.toNat_add]; simp; omega) a.2.1
    | s :: r' =>
      have ih := prev_cell hn (pre := s :: r') xt y (by simp)
      simpa [List.getLast?_cons_cons] using ih

end ParInv

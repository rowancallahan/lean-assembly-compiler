/- T11: the def epilogue `epi p q` (`GenArm` item 12 + `a23`) as an A64 run on `NMid`:
`ldp x15, x14, [x8]`; for j < q: `ldr x5, [x11, #8(q-1-j)]` and a store of x5 to `x8 + d_j`, `d_j = 8p + 16 - 8(j+1)`
(`str`, `stur`, or `sub x16, x8, #-d_j; str x5, [x16]`); `add/sub x11, x8, #|n|` (`n = 8p + 16 - 8q`);
`add x8, x15, #0`; `br x14`. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-! ## for ArmNat: `sub x16, xn, #i` -/

theorem n_subi16 (S : A64SemN M X W) (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {q n i : Nat} (hA : A[q]? = some (ArmEnc.subi 16 (armReg n) i)) (hn : mapped n = true)
    (hn0 : n ≠ 0) (hi : i < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (q + 1) s' ∧ (M.observe s').register 16 = st.x n - UInt64.ofNat i := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.subi s 16 _ i hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by decide) (armReg_lt hn hn0) hi (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  obtain ⟨s', r, N, o⟩ := nmid_scr hM (Or.inl rfl) this
  exact ⟨s', r, N, by rw [o]; simp [setReg]⟩

/-! ## definitions -/

/-- `d_j = 8p + 16 - 8(j+1)` -/
def dj (p j : Nat) : Int := 8 * (p : Int) + 16 - 8 * ((j : Int) + 1)
/-- words of the store of copy `j`: 1 (`str` / `stur`) or 2 (`sub x16; str [x16]`) -/
def stLen (d : Int) : Nat := if -256 ≤ d then 1 else 2
/-- word index after `j` copies, starting at word `h` -/
def epiPos (p h : Nat) : Nat → Nat
  | 0 => h
  | j + 1 => epiPos p h j + 1 + stLen (dj p j)
/-- the three store shapes, at word `i`, offset `d` from x8 -/
def StW (A : List Nat) (i : Nat) (d : Int) : Prop :=
  (0 ≤ d ∧ d % 8 = 0 ∧ d < 32768 ∧ A[i]? = some (ArmEnc.str (armReg 5) (armReg 8) d.toNat)) ∨
  (-256 ≤ d ∧ d < 0 ∧ A[i]? = some (ArmEnc.stur (armReg 5) (armReg 8) d)) ∨
  (-4096 < d ∧ d < -256 ∧ A[i]? = some (ArmEnc.subi 16 (armReg 8) (-d).toNat) ∧
    A[i + 1]? = some (ArmEnc.str (armReg 5) 16 0))
/-- the view after `j` copies (loads read the current memory) -/
def epiSt (p q : Nat) (st : CallProbe.St) : Nat → CallProbe.St
  | 0 => st
  | j + 1 =>
    let s := epiSt p q st j
    let s1 := CallProbe.wr s 5 (s.m ((s.x 31).toNat + 8 * (q - 1 - j)))
    { s1 with m := CallProbe.upd s1.m (((s.x 8).toNat : Int) + dj p j).toNat (s1.x 5) }
/-- `x + n` for an Int `n` (`add` / `sub` immediate) -/
def addI (x : UInt64) (n : Int) : UInt64 := if 0 ≤ n then x + UInt64.ofNat n.toNat else x - UInt64.ofNat (-n).toNat
/-- the final frame-pointer displacement `8p + 16 - 8q` -/
def nI (p q : Nat) : Int := 8 * (p : Int) + 16 - 8 * (q : Int)

theorem epiSt_x (p q : Nat) (st : CallProbe.St) (r : Nat) (hr : r ≠ 5) : ∀ j, (epiSt p q st j).x r = st.x r := by
  intro j; induction j with
  | zero => rfl
  | succ j ih => simp [epiSt, CallProbe.wr, CallProbe.upd, hr, ih]

theorem toNat_lt64 (x : UInt64) : x.toNat < 2 ^ 64 := by
  first | exact x.toNat_lt | exact x.toNat_lt_size | simpa using x.toNat_lt_size

/-! ## one copy: load + store -/

theorem n_epiPair (S : A64SemN M X W) {h f : Nat} {d : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h]? = some (ArmEnc.ldr (armReg 5) (armReg 31) f)) (hf8 : f % 8 = 0) (hf : f < 32768)
    (a1 : StW A (h + 1) d) (hnn : 0 ≤ ((st.x 8).toNat : Int) + d)
    (hl : wok K ((st.x 31).toNat + f)) (hs : wok K (((st.x 8).toNat : Int) + d).toNat) :
    let st1 := CallProbe.wr st 5 (st.m ((st.x 31).toNat + f))
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 { st1 with m := CallProbe.upd st1.m (((st.x 8).toNat : Int) + d).toNat (st1.x 5) }
        (h + 1 + stLen d) s' := by
  intro st1
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 31).toNat + f) S hM hB a0 (by decide) (by decide) (by decide)
    (hM.x 31 (by omega) (by omega)) hf8 hf rfl hl
  have e8 : (CallProbe.wr st 5 (st.m ((st.x 31).toNat + f))).x 8 = st.x 8 := by
    simp [CallProbe.wr, CallProbe.upd]
  rcases a1 with ⟨h0, h8, h32, a1⟩ | ⟨h0, h1, a1⟩ | ⟨h0, h1, a1, a2⟩
  · obtain ⟨s2, r2, N2⟩ := n_str (a := (((st.x 8).toNat : Int) + d).toNat) S N1 hB a1 (by decide)
      (N1.x 5 (by omega) (by omega)) (by decide) (N1.x 8 (by omega) (by omega)) (by omega) (by omega)
      (by rw [e8]; omega) hs
    rw [show stLen d = 1 from if_pos (by omega)]
    exact ⟨s2, Runs.trans r1 r2, N2⟩
  · obtain ⟨s2, r2, N2⟩ := n_stur (a := (((st.x 8).toNat : Int) + d).toNat) S N1 hB a1 (by decide)
      (N1.x 5 (by omega) (by omega)) (by decide) (N1.x 8 (by omega) (by omega)) h0 (by omega)
      (by rw [e8]; omega) hs
    rw [show stLen d = 1 from if_pos (by omega)]
    exact ⟨s2, Runs.trans r1 r2, N2⟩
  · have b8 := toNat_lt64 (st.x 8)
    obtain ⟨s2, r2, N2, R2⟩ := n_subi16 S N1 hB a1 (by decide) (by decide) (i := (-d).toNat) (by omega)
    have hi : (st.x 8 - UInt64.ofNat (-d).toNat).toNat = (st.x 8).toNat - (-d).toNat := by
      rw [UInt64.toNat_sub, toNat_ofNat_lt (by omega)]
      rw [e8] at *
      omega
    obtain ⟨s3, r3, N3⟩ := n_str (a := (((st.x 8).toNat : Int) + d).toNat) S N2 hB a2 (by decide)
      (N2.x 5 (by omega) (by omega)) (by decide) (bv := st.x 8 - UInt64.ofNat (-d).toNat) (by
        rw [R2]; simp [CallProbe.wr, CallProbe.upd]) (by decide) (by decide) (by rw [hi]; omega) hs
    rw [show stLen d = 2 from if_neg (by omega)]
    exact ⟨s3, Runs.trans r1 (Runs.trans r2 r3), N3⟩

/-! ## the copy loop -/

theorem n_epiCopy (S : A64SemN M X W) {h p q : Nat} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hq : q < 4096)
    (hcp : ∀ j, j < q → A[epiPos p h j]? = some (ArmEnc.ldr (armReg 5) (armReg 31) (8 * (q - 1 - j))) ∧
      StW A (epiPos p h j + 1) (dj p j))
    (hwk : ∀ j, j < q → wok K ((st.x 31).toNat + 8 * (q - 1 - j)) ∧ 0 ≤ ((st.x 8).toNat : Int) + dj p j ∧
      wok K (((st.x 8).toNat : Int) + dj p j).toNat) :
    ∀ j, j ≤ q → ∃ s', Runs M s s' ∧ NMid X W K A s0 (epiSt p q st j) (epiPos p h j) s' := by
  intro j
  induction j with
  | zero => intro _; exact ⟨s, .stop, hM⟩
  | succ j ih =>
    intro hj
    obtain ⟨s1, r1, N1⟩ := ih (by omega)
    obtain ⟨hl, hnn, hs⟩ := hwk j (by omega)
    obtain ⟨c0, c1⟩ := hcp j (by omega)
    have x31 := epiSt_x p q st 31 (by decide) j
    have x8 := epiSt_x p q st 8 (by decide) j
    obtain ⟨s2, r2, N2⟩ := n_epiPair (f := 8 * (q - 1 - j)) S N1 hB c0 (by omega) (by omega) c1
      (by rw [x8]; exact hnn) (by rw [x31]; exact hl) (by rw [x8]; exact hs)
    rw [x8, x31] at N2
    exact ⟨s2, Runs.trans r1 r2, N2⟩

/-! ## tail: `add/sub x11, x8, #|n|; add x8, x15, #0; br x14` -/

theorem n_epiTail (S : A64SemN M X W) {e r : Nat} {n : Int} (hM : NMid X W K A s0 st e s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a1 : A[e]? = some (if 0 ≤ n then ArmEnc.addi (armReg 31) (armReg 8) n.toNat
      else ArmEnc.subi (armReg 31) (armReg 8) (-n).toNat))
    (a2 : A[e + 1]? = some (ArmEnc.addi (armReg 8) (armReg 15) 0))
    (a3 : A[e + 2]? = some (ArmEnc.brR (armReg 14))) (hn : -4096 < n ∧ n < 4096)
    (hret : st.x 14 = UInt64.ofNat (K.base + 4 * r)) :
    let st3 := CallProbe.wr st 31 (addI (st.x 8) n)
    let st4 := CallProbe.wr st3 8 (st3.x 15 + UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st4 r s' := by
  intro st3 st4
  have e3 : ∀ {s1 : M.State}, NMid X W K A s0 st3 (e + 1) s1 → ∃ s', Runs M s1 s' ∧ NMid X W K A s0 st4 r s' := by
    intro s1 N1
    obtain ⟨s2, r2, N2⟩ := n_addi S N1 hB a2 (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s3, r3, N3⟩ := n_br S (n := 14) N2 hB a3 (by decide) (by decide)
      (by simp [CallProbe.wr, CallProbe.upd, st3, hret])
    exact ⟨s3, Runs.trans r2 r3, N3⟩
  by_cases hp : 0 ≤ n
  · rw [if_pos hp] at a1
    obtain ⟨s1, r1, N1⟩ := n_addi S hM hB a1 (by decide) (by decide) (by decide) (by decide) (by omega)
    obtain ⟨s', r', N'⟩ := e3 (s1 := s1) (by simpa [st3, addI, hp] using N1)
    exact ⟨s', Runs.trans r1 r', N'⟩
  · rw [if_neg hp] at a1
    obtain ⟨s1, r1, N1⟩ := n_subi S hM hB a1 (by decide) (by decide) (by decide) (by decide) (by omega)
    obtain ⟨s', r', N'⟩ := e3 (s1 := s1) (by simpa [st3, addI, hp] using N1)
    exact ⟨s', Runs.trans r1 r', N'⟩

/-! ## the epilogue -/

/-- **epi p q** (`item 12`, `a23`): `ldp x15, x14, [x8]`; the q copies; `x11 := x8 ± |8p + 16 - 8q|`; `x8 := x15`;
`br x14` to word `r` (the saved return address `[x8 + 8]` is the byte address of word `r`) -/
theorem n_epi (S : A64SemN M X W) {h p q r : Nat} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hq : q < 4096)
    (a0 : A[h]? = some (ArmEnc.ldp (armReg 15) (armReg 14) (armReg 8)))
    (hcp : ∀ j, j < q → A[epiPos p (h + 1) j]? = some (ArmEnc.ldr (armReg 5) (armReg 31) (8 * (q - 1 - j))) ∧
      StW A (epiPos p (h + 1) j + 1) (dj p j))
    (a1 : A[epiPos p (h + 1) q]? = some (if 0 ≤ nI p q then ArmEnc.addi (armReg 31) (armReg 8) (nI p q).toNat
      else ArmEnc.subi (armReg 31) (armReg 8) (-nI p q).toNat))
    (a2 : A[epiPos p (h + 1) q + 1]? = some (ArmEnc.addi (armReg 8) (armReg 15) 0))
    (a3 : A[epiPos p (h + 1) q + 2]? = some (ArmEnc.brR (armReg 14))) (hn : -4096 < nI p q ∧ nI p q < 4096)
    (hw : wok K (st.x 8).toNat) (hw8 : wok K ((st.x 8).toNat + 8))
    (hwk : ∀ j, j < q → wok K ((st.x 31).toNat + 8 * (q - 1 - j)) ∧ 0 ≤ ((st.x 8).toNat : Int) + dj p j ∧
      wok K (((st.x 8).toNat : Int) + dj p j).toNat)
    (hret : st.m ((st.x 8).toNat + 8) = UInt64.ofNat (K.base + 4 * r)) :
    let st1 := CallProbe.wr (CallProbe.wr st 15 (st.m (st.x 8).toNat)) 14 (st.m ((st.x 8).toNat + 8))
    let st2 := epiSt p q st1 q
    let st3 := CallProbe.wr st2 31 (addI (st2.x 8) (nI p q))
    let st4 := CallProbe.wr st3 8 (st3.x 15 + UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st4 r s' := by
  intro st1 st2 st3 st4
  obtain ⟨s1, r1, N1⟩ := n_ldp S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (hM.x 8 (by omega) (by omega)) hw hw8
  have y31 : st1.x 31 = st.x 31 := by simp [st1, CallProbe.wr, CallProbe.upd]
  have y8 : st1.x 8 = st.x 8 := by simp [st1, CallProbe.wr, CallProbe.upd]
  obtain ⟨s2, r2, N2⟩ := n_epiCopy S N1 hB hq hcp (by
    intro j hj; rw [y31, y8]; exact hwk j hj) q le_rfl
  obtain ⟨s3, r3, N3⟩ := n_epiTail (r := r) S N2 hB a1 a2 a3 hn (by
    rw [epiSt_x p q st1 14 (by decide) q]; simp [st1, CallProbe.wr, CallProbe.upd, hret])
  exact ⟨s3, Runs.trans r1 (Runs.trans r2 r3), N3⟩

end JT

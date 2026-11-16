/- The correctness of the inductive path's lowering to RTL, part 4: the decoder `dec` (`decF`) reads the byte format
`C.enc sh` of a well-formed value from the input and returns the value in memory and the cursor after it (strings
as length + bytes into chains of cells, `decStr`). -/
import Compiler.Ir.IndLowT
import Compiler.IndStrOk

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

variable {P : Prog VReg}

theorem ex_seqs_cons {a : SC} {as : List SC} {g g₁ g₂ : VReg → Val} {m m₁ m₂ : Mem} (ha : SC.Ex P a g m g₁ m₁)
    (hs : SC.Ex P (SC.seqs as) g₁ m₁ g₂ m₂) : SC.Ex P (SC.seqs (a :: as)) g m g₂ m₂ := by
  cases as with
  | nil => cases hs; exact ha
  | cons b bs => exact .seq ha hs

/-- a byte of the input -/
theorem ex_ldb {g : VReg → Val} {m : Mem} {d p : VReg} {i : Arg VReg} {k : Nat} {b : UInt8} (hp : g p = .p 0 0)
    (hi : i.word g = some (BitVec.ofNat 64 k)) (hk : k < 2 ^ 64) (hb : m.inp[k]? = some b) :
    SC.Ex P (.i (.ldb d p i)) g m (upd g d (.w (BitVec.ofNat 64 b.toNat))) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by
    simp only [Inst.exec, hi, hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, hb, zb])

theorem word_r {g : VReg → Val} {x : VReg} {w : BitVec 64} (h : g x = .w w) : (Arg.r x).word g = some w := by
  simp [Arg.word, Arg.eval, h]

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem unle_take_succ : ∀ (L : List UInt8) (k : Nat) (hk : k < L.length),
    unle (L.take (k + 1)) = unle (L.take k) + L[k].toNat * 256 ^ k
  | [], _, hk => absurd hk (by simp)
  | b :: L, 0, _ => by simp [unle]
  | b :: L, k + 1, hk => by
    have hk' : k < L.length := by simp at hk; omega
    simp only [List.take_succ_cons, unle, List.getElem_cons_succ]
    rw [unle_take_succ L k hk', Nat.pow_succ]
    simp only [Nat.mul_add]
    rw [show 256 * (L[k].toNat * (256 ^ k)) = L[k].toNat * (256 ^ k * 256) by
      rw [Nat.mul_comm 256, Nat.mul_assoc, Nat.mul_comm (256 ^ k)]]
    omega

/-- one byte of `rd8`: `d := d * 256 + byte` -/
def rdStep (inp cur d t1 t2 : VReg) (j : Nat) : SC :=
  .seqs [addK t1 cur (BitVec.ofNat 64 j), .i (.ldb t2 inp (.r t1)), .i (.let_ d (.op .shl (.r d) (.i 8))), bin .add d d t2]

theorem rd8_eq (inp cur d t1 t2 : VReg) : rd8 inp cur d t1 t2 =
    .seq (setK d 0) (.seqs ((List.range 8).reverse.map (rdStep inp cur d t1 t2))) := rfl

theorem pow_lt (k : Nat) (hk : k ≤ 8) : 256 ^ k ≤ 2 ^ 64 := by
  have : 256 ^ k ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hk
  exact Nat.le_trans this (by decide)

/-- the bytes `L[0 .. k)` read from the last to the first onto `u` -/
theorem rd_loop {inp cur d t1 t2 : VReg} (hd1 : d ≠ t1) (hd2 : d ≠ t2) (h12 : t1 ≠ t2) (hi1 : inp ≠ t1)
    (hi2 : inp ≠ t2) (hc1 : cur ≠ t1) (hc2 : cur ≠ t2) (hid : inp ≠ d) (hcd : cur ≠ d)
    {m : Mem} {c : Nat} (L : List UInt8) (hL : L.length = 8) (hin : ∀ i (hi : i < 8), m.inp[c + i]? = some L[i])
    (hc : c + 8 < 2 ^ 64) :
    ∀ k (hk : k ≤ 8) (g : VReg → Val) (u : Nat), g inp = .p 0 0 → g cur = .w (BitVec.ofNat 64 c) →
      g d = .w (BitVec.ofNat 64 u) → u < 256 ^ (8 - k) →
      ∃ g', SC.Ex P (.seqs ((List.range k).reverse.map (rdStep inp cur d t1 t2))) g m g' m ∧
        g' d = .w (BitVec.ofNat 64 (u * 256 ^ k + unle (L.take k))) ∧ ∀ q : Nat, q ≠ d → q ≠ t1 → q ≠ t2 → g' q = g q
  | 0, _, g, u, _, _, hd, _ => ⟨g, .nop, by simpa [unle] using hd, fun _ _ _ _ => rfl⟩
  | k + 1, hk, g, u, hp, hcu, hd, hu => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    have hk8 : k < 8 := by omega
    have hb := hin k hk8
    -- the step for byte `k`
    generalize hg1 : upd g t1 (.w (BitVec.ofNat 64 c + BitVec.ofNat 64 k)) = g1
    have x1 : SC.Ex P (addK t1 cur (BitVec.ofNat 64 k)) g m g1 m := hg1 ▸ ex_addK m t1 cur _ hcu
    have h1 : g1 t1 = .w (BitVec.ofNat 64 (c + k)) := by rw [← hg1, upd_same, ofNat_add]
    have x2 := ex_ldb (P := P) (d := t2) (g := g1) (m := m) (b := L[k]) (by rw [← hg1, upd_ne _ _ hi1]; exact hp)
      (word_r h1) (by omega) hb
    generalize hg2 : upd g1 t2 (.w (BitVec.ofNat 64 L[k].toNat)) = g2 at x2
    have hd2' : g2 d = .w (BitVec.ofNat 64 u) := by rw [← hg2, upd_ne _ _ hd2, ← hg1, upd_ne _ _ hd1]; exact hd
    have x3 : SC.Ex P (.i (.let_ d (.op .shl (.r d) (.i 8)))) g2 m
        (upd g2 d (.w (Op.eval .shl (BitVec.ofNat 64 u) (BitVec.ofNat 64 8)))) m :=
      .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, Rhs.eval, Arg.word, Arg.eval, hd2'])
    have x4 := ex_bin (P := P) m .add d d t2 (g := upd g2 d (.w (Op.eval .shl (BitVec.ofNat 64 u) (BitVec.ofNat 64 8))))
      (upd_same _ _ _) (by rw [upd_ne _ _ (Ne.symm hd2), ← hg2, upd_same])
    have hu56 : u < 2 ^ 56 := by
      have : 256 ^ (8 - (k + 1)) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
      omega
    have hor := horner u L[k].toNat hu56 L[k].toNat_lt
    simp only [Op.eval] at x4 hor
    rw [hor] at x4
    generalize hg3 : upd (upd g2 d (.w (Op.eval .shl (BitVec.ofNat 64 u) (BitVec.ofNat 64 8)))) d
      (.w (BitVec.ofNat 64 (L[k].toNat + 256 * u))) = g3 at x4
    have e3 : ∀ q : Nat, q ≠ d → q ≠ t1 → q ≠ t2 → g3 q = g q := fun q a b c => by
      rw [← hg3, upd_ne _ _ a, upd_ne _ _ a, ← hg2, upd_ne _ _ c, ← hg1, upd_ne _ _ b]
    have hu' : L[k].toNat + 256 * u < 256 ^ (8 - k) := by
      have := L[k].toNat_lt
      have e : 256 ^ (8 - k) = 256 * 256 ^ (8 - (k + 1)) := by
        rw [show 8 - k = (8 - (k + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      have : u + 1 ≤ 256 ^ (8 - (k + 1)) := hu
      have := Nat.mul_le_mul_left 256 this
      omega
    obtain ⟨g', x', hd', fr⟩ := rd_loop hd1 hd2 h12 hi1 hi2 hc1 hc2 hid hcd L hL hin hc k (by omega) g3 (L[k].toNat + 256 * u)
      (by rw [e3 _ hid hi1 hi2]; exact hp) (by rw [e3 _ hcd hc1 hc2]; exact hcu) (by rw [← hg3, upd_same]) hu'
    refine ⟨g', ex_seqs_cons (by simp only [rdStep, SC.seqs]; exact .seq x1 (.seq x2 (.seq x3 (hg3 ▸ x4)))) x', ?_,
      fun q a b c => by rw [fr q a b c, e3 q a b c]⟩
    rw [hd', unle_take_succ L k (by omega)]
    congr 2
    have e : (L[k].toNat + 256 * u) * 256 ^ k = L[k].toNat * 256 ^ k + u * 256 ^ (k + 1) := by
      rw [Nat.add_mul, Nat.mul_comm 256 u, Nat.mul_assoc, Nat.pow_succ, Nat.mul_comm 256 (256 ^ k)]
    rw [e]; omega

/-- **`rd8`**: the 8 bytes at the cursor, little-endian -/
theorem rd8_ok {inp cur d t1 t2 : VReg} (hd1 : d ≠ t1) (hd2 : d ≠ t2) (h12 : t1 ≠ t2) (hi1 : inp ≠ t1)
    (hi2 : inp ≠ t2) (hc1 : cur ≠ t1) (hc2 : cur ≠ t2) (hid : inp ≠ d) (hcd : cur ≠ d)
    {m : Mem} {c : Nat} (L : List UInt8) (hL : L.length = 8) (hin : ∀ i (hi : i < 8), m.inp[c + i]? = some L[i])
    (hc : c + 8 < 2 ^ 64) {g : VReg → Val} (hp : g inp = .p 0 0) (hcu : g cur = .w (BitVec.ofNat 64 c)) :
    ∃ g', SC.Ex P (rd8 inp cur d t1 t2) g m g' m ∧ g' d = .w (BitVec.ofNat 64 (unle L)) ∧
      ∀ q : Nat, q ≠ d → q ≠ t1 → q ≠ t2 → g' q = g q := by
  obtain ⟨g', x, hd, fr⟩ := rd_loop (P := P) hd1 hd2 h12 hi1 hi2 hc1 hc2 hid hcd L hL hin hc 8 (Nat.le_refl _)
    (upd g d (.w 0)) 0 (by rw [upd_ne _ _ hid]; exact hp) (by rw [upd_ne _ _ hcd]; exact hcu) (by rw [upd_same]; rfl)
    (by decide)
  refine ⟨g', by rw [rd8_eq]; exact .seq (ex_setK g m d 0) x, ?_, fun q a b c => by rw [fr q a b c, upd_ne _ _ a]⟩
  rw [hd, ← hL, List.take_length]; simp

/-! ## strings -/

theorem ofNat_sub1 (a : Nat) (h : a + 1 < 2 ^ 64) :
    Op.eval .sub (BitVec.ofNat 64 (a + 1)) 1 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Op.eval, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (a := a + 1) (by omega),
    Nat.mod_eq_of_lt (a := a) (by omega)]
  omega

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact h this

/-- the loop of `decStr` -/
def strBody (st : Nat) : SC :=
  .seqs [.i (.let_ 9 (.op .sub (.r 9) (.i 1))), .i (.ldb 7 0 (.r 9)),
    mkCell 11 (.i (BitVec.ofNat 64 (st + 1))) (.r 7) (.r 10) (.i 0), mov 10 11]

theorem str_loop (st : Nat) (hst : st + 1 < 256) (L : List UInt8) (c : Nat) (hc : c + 8 + L.length < 2 ^ 64)
    (inp : List UInt8) (hin : ∀ i (hi : i < L.length), inp[c + 8 + i]? = some L[i]) :
    ∀ j (hj : j ≤ L.length) (g : VReg → Val) (m : Mem), m.inp = inp → g 0 = .p 0 0 →
      g 1 = .w (BitVec.ofNat 64 (c + 8)) → g 9 = .w (BitVec.ofNat 64 (c + 8 + j)) → Rv m (g 10) (C.str st (L.drop j)) →
      ∃ g' m', SC.Ex P (.loop ⟨.ne, .r 9, .r 1⟩ (strBody st)) g m g' m' ∧ MLe m m' ∧ m'.out = m.out ∧
        Rv m' (g' 10) (C.str st L) ∧ ∀ q : Nat, q ≠ 7 → q ≠ 9 → q ≠ 10 → q ≠ 11 → g' q = g q
  | 0, _, g, m, hm, h0, h1, h9, h10 =>
    ⟨g, m, .loopF (by simp [Tst.eval, Arg.eval, h9, h1, Cond.eval]), MLe.refl m, rfl, by simpa using h10,
      fun _ _ _ _ _ => rfl⟩
  | j + 1, hj, g, m, hm, h0, h1, h9, h10 => by
    have hjl : j < L.length := by omega
    have ht : (⟨.ne, .r 9, .r 1⟩ : Tst VReg).eval g = some true := by
      simp only [Tst.eval, Arg.eval, h9, h1, Cond.eval]
      rw [decide_eq_false (ofNat_ne (by omega) (by omega) (by omega))]; rfl
    -- the body
    have x1 : SC.Ex P (.i (.let_ 9 (.op .sub (.r 9) (.i 1)))) g m (upd g 9 (.w (BitVec.ofNat 64 (c + 8 + j)))) m :=
      .i (e := []) (fun _ _ _ h => nomatch h) (by
        simp only [Inst.exec, Rhs.eval, Arg.word, Arg.eval, h9, show c + 8 + (j + 1) = (c + 8 + j) + 1 by omega]
        rw [ofNat_sub1 _ (by omega)])
    generalize hg1 : upd g 9 (.w (BitVec.ofNat 64 (c + 8 + j))) = g1 at x1
    have x2 := ex_ldb (P := P) (d := 7) (p := 0) (i := .r 9) (g := g1) (m := m) (k := c + 8 + j) (b := L[j])
      (by rw [← hg1, upd_ne _ _ (by decide)]; exact h0) (word_r (x := 9) (w := BitVec.ofNat 64 (c + 8 + j)) (by rw [← hg1, upd_same])) (by omega)
      (by rw [hm]; exact hin j hjl)
    generalize hg2 : upd g1 7 (.w (BitVec.ofNat 64 L[j].toNat)) = g2 at x2
    have g2_10 : g2 10 = g 10 := by rw [← hg2, upd_ne _ _ (by decide), ← hg1, upd_ne _ _ (by decide)]
    have g2_7 : g2 7 = .w (BitVec.ofNat 64 L[j].toNat) := by rw [← hg2, upd_same]
    have x3 := ex_mkCell' (P := P) (g := g2) (m := m) (d := 11) (t := .i (BitVec.ofNat 64 (st + 1))) (x := .r 7)
      (l := .r 10) (r := .i 0) rfl (by simp only [Arg.eval]; rw [upd_ne _ _ (by decide), g2_7])
      (by simp only [Arg.eval]; rw [upd_ne _ _ (by decide), g2_10]) rfl
    obtain ⟨hle, hrv⟩ := mkCell_rv (m := m) (t := st + 1) (x := BitVec.ofNat 64 L[j].toNat) hst h10 Rv.z
    have x4 := ex_mov (P := P) (upd g2 11 (.p (m.blks.length + 2) 0)) (m.push4 (.w (BitVec.ofNat 64 (st + 1)))
      (.w (BitVec.ofNat 64 L[j].toNat)) (g 10) (.w 0)) 10 11
    generalize hg4 : upd (upd g2 11 (.p (m.blks.length + 2) 0)) 10 (upd g2 11 (.p (m.blks.length + 2) 0) 11) = g4 at x4
    have e4 : ∀ q : Nat, q ≠ 7 → q ≠ 9 → q ≠ 10 → q ≠ 11 → g4 q = g q := fun q a b c d => by
      rw [← hg4, upd_ne _ _ c, upd_ne _ _ d, ← hg2, upd_ne _ _ a, ← hg1, upd_ne _ _ b]
    have h10' : Rv (m.push4 (.w (BitVec.ofNat 64 (st + 1))) (.w (BitVec.ofNat 64 L[j].toNat)) (g 10) (.w 0)) (g4 10)
        (C.str st (L.drop j)) := by
      rw [← hg4, upd_same, upd_same, List.drop_eq_getElem_cons hjl]; exact hrv
    obtain ⟨g', m', xl, ml, ho, hr, fr⟩ := str_loop st hst L c hc inp hin j (by omega) g4 _ (by rw [← hm]; rfl)
      (by rw [e4 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
      (by rw [e4 1 (by decide) (by decide) (by decide) (by decide)]; exact h1)
      (by rw [← hg4, upd_ne _ _ (by decide), upd_ne _ _ (by decide), ← hg2, upd_ne _ _ (by decide), ← hg1, upd_same])
      h10'
    refine ⟨g', m', .loopT ht (by simp only [strBody, SC.seqs]; exact .seq x1 (.seq x2 (.seq x3 x4))) xl,
      hle.trans ml, by rw [ho]; rfl, hr, fun q a b c d => by rw [fr q a b c d, e4 q a b c d]⟩

-- DECSTR
theorem unle_leN8 (n : Nat) (hn : n < 2 ^ 64) : unle (leN 8 n) = n := by
  rw [unle_leN]; exact Nat.mod_eq_of_lt (by simpa using hn)

theorem in_app {inp L₁ L₂ : List UInt8} {c : Nat}
    (h : ∀ i (hi : i < (L₁ ++ L₂).length), inp[c + i]? = some (L₁ ++ L₂)[i]) :
    (∀ i (hi : i < L₁.length), inp[c + i]? = some L₁[i]) ∧
      ∀ i (hi : i < L₂.length), inp[c + L₁.length + i]? = some L₂[i] := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by simp; omega); rw [List.getElem_append_left hi] at this; exact this
  · have := h (L₁.length + i) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [Nat.add_assoc]; exact this

/-- **`decStr`**: a string (its length, then its bytes) into a chain of cells -/
theorem decStr_ok (st : Nat) (hst : st + 1 < 256) (d : Nat) (hd1 : d ≠ 0) (hd2 : d ≠ 1) (hd3 : d < 6)
    (L : List UInt8) (c : Nat) (hc : c + 8 + L.length < 2 ^ 60) {g : VReg → Val} {m : Mem} (h0 : g 0 = .p 0 0)
    (h1 : g 1 = .w (BitVec.ofNat 64 c))
    (hin : ∀ i (hi : i < (leN 8 L.length ++ L).length), m.inp[c + i]? = some (leN 8 L.length ++ L)[i]) :
    ∃ g' m', SC.Ex P (decStr st d) g m g' m' ∧ MLe m m' ∧ m'.out = m.out ∧ Rv m' (g' d) (C.str st L) ∧
      g' 1 = .w (BitVec.ofNat 64 (c + (leN 8 L.length ++ L).length)) ∧
      ∀ q : Nat, q ≠ d → q ≠ 1 → (q < 6 ∨ 11 < q) → g' q = g q := by
  obtain ⟨hA, hB⟩ := in_app hin
  rw [leN_length] at hB
  obtain ⟨g₁, x₁, e8, f₁⟩ := rd8_ok (P := P) (inp := 0) (cur := 1) (d := 8) (t1 := 6) (t2 := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (leN 8 L.length) (leN_length _ _)
    (fun i hi => hA i (by rw [leN_length]; exact hi)) (by omega) h0 h1
  rw [unle_leN8 _ (by omega)] at e8
  have g10 : g₁ 0 = .p 0 0 := by rw [f₁ 0 (by decide) (by decide) (by decide)]; exact h0
  have g11 : g₁ 1 = .w (BitVec.ofNat 64 c) := by rw [f₁ 1 (by decide) (by decide) (by decide)]; exact h1
  have x₂ := ex_addK (P := P) m 1 1 8 g11
  rw [show (BitVec.ofNat 64 c + 8 : BitVec 64) = BitVec.ofNat 64 (c + 8) from ofNat_add c 8] at x₂
  generalize hg₂ : upd g₁ 1 (.w (BitVec.ofNat 64 (c + 8))) = g₂ at x₂
  have x₃ := ex_mkCell' (P := P) (g := g₂) (m := m) (d := 10) (t := .i (BitVec.ofNat 64 st)) (x := .i 0) (l := .i 0)
    (r := .i 0) (vt := .w (BitVec.ofNat 64 st)) (vx := .w 0) (vl := .w 0) (vr := .w 0) rfl rfl rfl rfl
  obtain ⟨hle₃, hrv₃⟩ := mkCell_rv (m := m) (t := st) (x := 0) (by omega) Rv.z Rv.z
  generalize hg₃ : upd g₂ 10 (.p (m.blks.length + 2) 0) = g₃ at x₃
  generalize hm₃ : m.push4 (.w (BitVec.ofNat 64 st)) (.w 0) (.w 0) (.w 0) = m₃ at x₃ hle₃ hrv₃
  have g31 : g₃ 1 = .w (BitVec.ofNat 64 (c + 8)) := by rw [← hg₃, upd_ne _ _ (by decide), ← hg₂, upd_same]
  have g38 : g₃ 8 = .w (BitVec.ofNat 64 L.length) := by
    rw [← hg₃, upd_ne _ _ (by decide), ← hg₂, upd_ne _ _ (by decide)]; exact e8
  have x₄ := ex_bin (P := P) m₃ .add 9 1 8 g31 g38
  simp only [Op.eval, ofNat_add] at x₄
  generalize hg₄ : upd g₃ 9 (.w (BitVec.ofNat 64 (c + 8 + L.length))) = g₄ at x₄
  have e4 : ∀ q : Nat, q ≠ 1 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 10 → g₄ q = g q := fun q a b c d e f => by
    rw [← hg₄, upd_ne _ _ e, ← hg₃, upd_ne _ _ f, ← hg₂, upd_ne _ _ a, f₁ q d b c]
  obtain ⟨g₅, m₅, x₅, ml₅, o₅, r₅, f₅⟩ := str_loop (P := P) st hst L c (by omega) m.inp
    (fun i hi => by have := hB i hi; rwa [Nat.add_assoc c 8 i] at this ⊢) L.length (Nat.le_refl _) g₄ m₃
    (by rw [← hm₃]; rfl) (by rw [e4 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h0)
    (by rw [← hg₄, upd_ne _ _ (by decide), g31]) (by rw [← hg₄, upd_same])
    (by rw [← hg₄, upd_ne _ _ (by decide), ← hg₃, upd_same, List.drop_length]; exact hrv₃)
  have g51 : g₅ 1 = .w (BitVec.ofNat 64 (c + 8)) := by
    rw [f₅ 1 (by decide) (by decide) (by decide) (by decide), ← hg₄, upd_ne _ _ (by decide), g31]
  have g58 : g₅ 8 = .w (BitVec.ofNat 64 L.length) := by
    rw [f₅ 8 (by decide) (by decide) (by decide) (by decide), ← hg₄, upd_ne _ _ (by decide), g38]
  have x₆ := ex_bin (P := P) m₅ .add 1 1 8 g51 g58
  simp only [Op.eval, ofNat_add] at x₆
  have x₇ := ex_mov (P := P) (upd g₅ 1 (.w (BitVec.ofNat 64 (c + 8 + L.length)))) m₅ d 10
  refine ⟨_, m₅, by
      simp only [decStr, SC.seqs]
      exact .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ x₇))))),
    hle₃.trans ml₅, by rw [o₅, ← hm₃]; rfl, ?_, ?_, ?_⟩
  · rw [upd_same, upd_ne _ _ (by decide)]; exact r₅
  · rw [upd_ne _ _ (Ne.symm hd2), upd_same, List.length_append, leN_length, Nat.add_assoc]
  · intro q a b cq
    rw [upd_ne _ _ a, upd_ne _ _ b]
    rw [f₅ q (by omega) (by omega) (by omega) (by omega)]
    exact e4 q b (by omega) (by omega) (by omega) (by omega) (by omega)

end Proven.Ir.IndLow

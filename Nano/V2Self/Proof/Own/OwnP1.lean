/- Nano/V2Self/Proof/Own/OwnP1: the representation of the walk state of `C.o41` (Nano/V2Self/C/Own.lean) and the access
lemmas for its registers and frames.  Abstract state `AS`: cursor, frames (bottom first), dead flags, value entries,
IF snapshots, phase; per-def context `WCx`: AST, def table, callee param / result kinds, slot kinds, npw.
`RS` = registers + frames in `s`; `RF` = kinds | flags | snapshots in `f`; `RV` = entries in `v`; `RT` = def table. -/
import Nano.V2Self.Proof.Own.OwnP0
import Nano.V2Self.Proof.Own.OwnSpec
namespace OwnP
open C

/-- a frame: tag, children, done, destination source, value base, current child's base, aux a, aux b -/
structure Fr where
  g : Nat
  n : Nat
  c : Nat
  d : Nat
  vb : Nat
  vc : Nat
  a : Nat
  b : Nat
  deriving Inhabited, DecidableEq

def Fr.fld (r : Fr) : Nat → Nat
  | 0 => r.g | 1 => r.n | 2 => r.c | 3 => r.d | 4 => r.vb | 5 => r.vc | 6 => r.a | 7 => r.b | _ => 0

def Fr.small (r : Fr) : Prop := ∀ k < 8, r.fld k < 2 ^ 60

def Fr.set (r : Fr) : Nat → Nat → Fr
  | 0, x => { r with g := x } | 1, x => { r with n := x } | 2, x => { r with c := x } | 3, x => { r with d := x }
  | 4, x => { r with vb := x } | 5, x => { r with vc := x } | 6, x => { r with a := x } | 7, x => { r with b := x }
  | _, _ => r

theorem Fr.fld_set (r : Fr) {k j : Nat} (hk : k < 8) (x : Nat) : (r.set k x).fld j = if j = k then x else r.fld j := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;>
  subst h <;> (rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [Fr.set, Fr.fld])

/-- per-def walk context -/
structure WCx where
  x : Buf
  t : Buf
  ps : List (List Nat)
  rs : List (List Nat)
  K : List Nat
  npw : Nat

def WCx.oc (W : WCx) : OwnSpec.Cx := ⟨W.ps, W.rs, W.K, W.npw⟩
abbrev WCx.ns (W : WCx) : Nat := W.K.length

/-- abstract walk state -/
structure AS where
  i : Nat
  Φ : List Fr
  F : List Bool
  es : List Nat
  sn : List (List Bool)
  ph : Nat

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- the registers 0..15 (none = unconstrained: 3 nres, 9 changed, 12 body start, 14, 15) -/
def regL (W : WCx) (A : AS) : List (Option UInt64) :=
  [some (u A.i), some 0, some (u W.npw), none, some (u A.Φ.length), some 0, some (u W.ns), some (u A.es.length),
   some 0, none, some (u A.sn.length), some (u A.ph), none, some (u W.ps.length), none, none]

/-- registers and frames -/
def RS (W : WCx) (s : Buf) (A : AS) : Prop :=
  16 + 8 * A.Φ.length ≤ s.length ∧ s.length < 2 ^ 62 ∧
  (∀ k x, (regL W A)[k]? = some (some x) → s.getD k 0 = x) ∧
  ∀ j < A.Φ.length, ∀ k < 8, s.getD (16 + 8 * j + k) 0 = u ((A.Φ.getD j default).fld k)

/-- kinds, dead flags, IF snapshots -/
def RF (W : WCx) (f : Buf) (A : AS) : Prop :=
  A.F.length = W.ns ∧ (∀ l ∈ A.sn, l.length = W.ns) ∧ 2 * W.ns + W.ns * A.sn.length ≤ f.length ∧ f.length < 2 ^ 62 ∧
  (∀ q < W.ns, f.getD q 0 = u (W.K.getD q 0)) ∧
  (∀ q < W.ns, f.getD (W.ns + q) 0 = u (b2n (A.F.getD q false))) ∧
  ∀ j < A.sn.length, ∀ q < W.ns, f.getD (2 * W.ns + W.ns * j + q) 0 = u (b2n ((A.sn.getD j []).getD q false))

/-- value entries -/
def RV (v : Buf) (A : AS) : Prop :=
  A.es.length ≤ v.length ∧ v.length < 2 ^ 62 ∧ ∀ j < A.es.length, v.getD j 0 = u (A.es.getD j 0)

/-- the def table: `t[c]` = offset `a` of `[npw, nres, unused flags, P, R]` -/
def RT (W : WCx) : Prop :=
  W.ps.length = W.rs.length ∧ W.ps.length < 4096 ∧ W.t.length < 2 ^ 40 ∧
  ∀ c < W.ps.length, ∃ a, W.t.getD c 0 = u a ∧ a + 2 + 2 * (W.ps.getD c []).length + (W.rs.getD c []).length ≤ W.t.length ∧
    (W.ps.getD c []).length < 2 ^ 20 ∧ (W.rs.getD c []).length < 2 ^ 20 ∧
    W.t.getD a 0 = u (W.ps.getD c []).length ∧ W.t.getD (a + 1) 0 = u (W.rs.getD c []).length ∧
    (∀ j < (W.ps.getD c []).length, W.t.getD (a + 2 + (W.ps.getD c []).length + j) 0 = u ((W.ps.getD c []).getD j 0)) ∧
    (∀ j < (W.rs.getD c []).length, W.t.getD (a + 2 + 2 * (W.ps.getD c []).length + j) 0 = u ((W.rs.getD c []).getD j 0)) ∧
    (∀ k ∈ W.ps.getD c [], k ≤ 2) ∧ (∀ k ∈ W.rs.getD c [], k ≤ 1)

/-- bounds -/
def Bnd (W : WCx) (A : AS) : Prop :=
  W.ns < 2 ^ 20 ∧ W.npw ≤ W.ns ∧ (∀ k ∈ W.K, k ≤ 2) ∧ W.x.length < 2 ^ 40 ∧ A.i < 2 ^ 40 ∧
  A.Φ.length ≤ 2 ^ 30 ∧ A.sn.length ≤ 2 ^ 30 ∧ A.es.length ≤ 2 ^ 24 ∧ (∀ e ∈ A.es, e < 2 ^ 30) ∧
  (∀ r ∈ A.Φ, r.small) ∧ A.ph < 3

/-- the whole state -/
def St (W : WCx) (s f v : Buf) (A : AS) : Prop := RS W s A ∧ RF W f A ∧ RV v A ∧ RT W ∧ Bnd W A

/-! ## registers -/
theorem regL_len (W : WCx) (A : AS) : (regL W A).length = 16 := rfl

theorem rs_get {W : WCx} {s : Buf} {A : AS} (h : RS W s A) {k : Nat} {x : UInt64} (hk : (regL W A)[k]? = some (some x)) :
    bget s (u k) = x := by
  have hk16 : k < 16 := by
    have := (List.getElem?_eq_some_iff.mp hk).1; simpa [regL_len] using this
  rw [bget_u s (by omega)]; exact h.2.2.1 k x hk

theorem rs_set {W : WCx} {s : Buf} {A A' : AS} (h : RS W s A) {r : Nat} (hr : r < 16) (x : UInt64)
    (hreg : regL W A' = (regL W A).set r (some x)) (hΦ : A'.Φ = A.Φ) : RS W (bset s (u r) x) A' := by
  obtain ⟨hl, hl2, hrg, hfr⟩ := h
  rw [bset_u s (by omega)]
  refine ⟨by rw [List.length_set, hΦ]; exact hl, by rw [List.length_set]; exact hl2, ?_, ?_⟩
  · intro k y hk
    rw [hreg, List.getElem?_set] at hk
    rw [getD_set]
    by_cases hkr : r = k
    · subst hkr
      have : r < (regL W A).length := by rw [regL_len]; exact hr
      simp only [if_true, this] at hk
      have : r < s.length := by omega
      simp only [true_and, this, if_true]; simpa using hk
    · simp only [hkr, if_false] at hk
      simp only [hkr, false_and, if_false]; exact hrg k y hk
  · intro j hj k hk
    rw [getD_set, if_neg (by omega), hΦ]; exact hfr j (hΦ ▸ hj) k hk

/-- the register facts with literal indices -/
theorem regs {W : WCx} {s : Buf} {A : AS} (h : RS W s A) :
    bget s 0 = u A.i ∧ bget s 1 = 0 ∧ bget s 2 = u W.npw ∧ bget s 4 = u A.Φ.length ∧ bget s 5 = 0 ∧
    bget s 6 = u W.ns ∧ bget s 7 = u A.es.length ∧ bget s 8 = 0 ∧ bget s 10 = u A.sn.length ∧
    bget s 11 = u A.ph ∧ bget s 13 = u W.ps.length :=
  ⟨rs_get h (k := 0) rfl, rs_get h (k := 1) rfl, rs_get h (k := 2) rfl, rs_get h (k := 4) rfl, rs_get h (k := 5) rfl,
   rs_get h (k := 6) rfl, rs_get h (k := 7) rfl, rs_get h (k := 8) rfl, rs_get h (k := 10) rfl, rs_get h (k := 11) rfl,
   rs_get h (k := 13) rfl⟩

/-! ## frames -/
theorem frame_idx {m k : Nat} (hm : m < 2 ^ 30) (hk : k < 8) :
    16 + 8 * (u (m + 1) - 1) + u k = u (16 + 8 * m + k) := by
  rw [show (1 : UInt64) = u 1 from rfl, u_sub (by omega) (by omega), show m + 1 - 1 = m by omega, show (16 : UInt64) = u 16 from rfl,
    show (8 : UInt64) = u 8 from rfl, u_mul, u_add, u_add]

theorem o1_eq {W : WCx} {s : Buf} {A : AS} (h : RS W s A) {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r])
    (hb : A.Φ.length ≤ 2 ^ 30) {k : Nat} (hk : k < 8) : o1 s (u k) = u (r.fld k) := by
  have h4 := (regs h).2.2.2.1
  have hl : A.Φ.length = Φ0.length + 1 := by rw [hΦ]; simp
  unfold o1; rw [h4, hl, frame_idx (by omega) hk, bget_u s (by omega), h.2.2.2 Φ0.length (by omega) k hk, hΦ]
  simp [List.getD_eq_getElem?_getD]

theorem o2_eq {W : WCx} {s : Buf} {A : AS} (h : RS W s A) {Φ0 : List Fr} {r : Fr} (hΦ : A.Φ = Φ0 ++ [r])
    (hb : A.Φ.length ≤ 2 ^ 30) {k : Nat} (hk : k < 8) (x : Nat) :
    RS W (o2 s (u k) (u x)) { A with Φ := Φ0 ++ [r.set k x] } := by
  have h4 := (regs h).2.2.2.1
  have hl : A.Φ.length = Φ0.length + 1 := by rw [hΦ]; simp
  obtain ⟨hl1, hl2, hrg, hfr⟩ := h
  unfold o2; rw [h4, hl, frame_idx (by omega) hk, bset_u s (by omega)]
  refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
  · intro k' y hk'
    have hk16 : k' < 16 := by
      have := (List.getElem?_eq_some_iff.mp hk').1; simpa [regL_len] using this
    rw [getD_set, if_neg (by omega)]
    apply hrg k' y
    simpa [regL, hl] using hk'
  · intro j hj k2 hk2
    rw [getD_set]
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjm : j = Φ0.length
    · subst hjm
      by_cases hkk : k2 = k
      · subst hkk; simp [List.getD_eq_getElem?_getD, Fr.fld_set _ hk, show 16 + 8 * Φ0.length + k2 < s.length by omega]
      · rw [if_neg (by omega), hfr _ (by rw [hl]; omega) k2 hk2, hΦ]
        simp [List.getD_eq_getElem?_getD, Fr.fld_set _ hk, hkk]
    · rw [if_neg (by omega), hfr j (by rw [hl]; omega) k2 hk2, hΦ]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < Φ0.length by omega)]

/-- one `o0` write at `j ≤ length` -/
theorem o0_step {b : Buf} {j : Nat} (hj : j ≤ b.length) (hb : b.length < 2 ^ 62) (w : UInt64) :
    (o0 b (u j) w).length = max b.length (j + 1) ∧ ∀ k, (o0 b (u j) w).getD k 0 = if k = j then w else b.getD k 0 := by
  rw [o0_u b (by omega) (by omega)]; exact ⟨wr_length hj w, wr_getD hj w⟩

theorem o3_eq {W : WCx} {s : Buf} {A : AS} (h : RS W s A) (hb : A.Φ.length < 2 ^ 30)
    (g n d a b : Nat) (hg : g < 2 ^ 60) (hn : n < 2 ^ 60) (hd : d < 2 ^ 60) (ha : a < 2 ^ 60) (hb' : b < 2 ^ 60) :
    RS W (o3 s (u g) (u n) (u d) (u a) (u b)) { A with Φ := A.Φ ++ [⟨g, n, 0, d, A.es.length, A.es.length, a, b⟩] } := by
  have h4 := (regs h).2.2.2.1
  have h7 := (regs h).2.2.2.2.2.2.1
  obtain ⟨hl1, hl2, hrg, hfr⟩ := h
  have hq : u A.Φ.length < 1073741824 := by
    rw [show (1073741824 : UInt64) = u 1073741824 from rfl, u_lt (by omega) (by omega)]; omega
  unfold o3; simp only [h4, h7, hq, if_true]
  generalize hm : A.Φ.length = m at *
  generalize he : A.es.length = e at *
  rw [show (16 : UInt64) + 8 * u m = u (16 + 8 * m) by
      rw [show (16 : UInt64) = u 16 from rfl, show (8 : UInt64) = u 8 from rfl, u_mul, u_add]]
  rw [show u (16 + 8 * m) + 1 = u (16 + 8 * m + 1) from u_add _ 1, show u (16 + 8 * m) + 2 = u (16 + 8 * m + 2) from u_add _ 2,
    show u (16 + 8 * m) + 3 = u (16 + 8 * m + 3) from u_add _ 3, show u (16 + 8 * m) + 4 = u (16 + 8 * m + 4) from u_add _ 4,
    show u (16 + 8 * m) + 5 = u (16 + 8 * m + 5) from u_add _ 5, show u (16 + 8 * m) + 6 = u (16 + 8 * m + 6) from u_add _ 6,
    show u (16 + 8 * m) + 7 = u (16 + 8 * m + 7) from u_add _ 7]
  rw [show 16 + 8 * m = 16 + 8 * m + 0 from rfl]
  have s0 := o0_step (b := s) (j := 16 + 8 * m + 0) (by omega) hl2 (u g)
  generalize o0 s (u (16 + 8 * m + 0)) (u g) = b1 at s0 ⊢
  have s1 := o0_step (b := b1) (j := 16 + 8 * m + 1) (by omega) (by omega) (u n)
  generalize o0 b1 (u (16 + 8 * m + 1)) (u n) = b2 at s1 ⊢
  have s2 := o0_step (b := b2) (j := 16 + 8 * m + 2) (by omega) (by omega) 0
  generalize o0 b2 (u (16 + 8 * m + 2)) 0 = b3 at s2 ⊢
  have s3 := o0_step (b := b3) (j := 16 + 8 * m + 3) (by omega) (by omega) (u d)
  generalize o0 b3 (u (16 + 8 * m + 3)) (u d) = b4 at s3 ⊢
  have s4 := o0_step (b := b4) (j := 16 + 8 * m + 4) (by omega) (by omega) (u e)
  generalize o0 b4 (u (16 + 8 * m + 4)) (u e) = b5 at s4 ⊢
  have s5 := o0_step (b := b5) (j := 16 + 8 * m + 5) (by omega) (by omega) (u e)
  generalize o0 b5 (u (16 + 8 * m + 5)) (u e) = b6 at s5 ⊢
  have s6 := o0_step (b := b6) (j := 16 + 8 * m + 6) (by omega) (by omega) (u a)
  generalize o0 b6 (u (16 + 8 * m + 6)) (u a) = b7 at s6 ⊢
  have s7 := o0_step (b := b7) (j := 16 + 8 * m + 7) (by omega) (by omega) (u b)
  generalize o0 b7 (u (16 + 8 * m + 7)) (u b) = b8 at s7 ⊢
  have hlen : b8.length = max s.length (16 + 8 * m + 8) := by omega
  have hget : ∀ k, b8.getD k 0 = if k = 16 + 8 * m + 7 then u b else if k = 16 + 8 * m + 6 then u a
      else if k = 16 + 8 * m + 5 then u e else if k = 16 + 8 * m + 4 then u e else if k = 16 + 8 * m + 3 then u d
      else if k = 16 + 8 * m + 2 then 0 else if k = 16 + 8 * m + 1 then u n else if k = 16 + 8 * m + 0 then u g
      else s.getD k 0 := by
    intro k; rw [s7.2, s6.2, s5.2, s4.2, s3.2, s2.2, s1.2, s0.2]
  rw [show (4 : UInt64) = u 4 from rfl, show u m + 1 = u (m + 1) from u_add m 1, bset_u b8 (by omega)]
  refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
  · intro k y hk
    have hk16 : k < 16 := by
      have := (List.getElem?_eq_some_iff.mp hk).1; simpa [regL_len] using this
    rw [getD_set]
    by_cases k4 : 4 = k
    · subst k4; simp only [true_and, show 4 < b8.length by omega, if_true]
      simp [regL] at hk; rw [← hk]; simp [hm]
    · rw [if_neg (by omega), hget]
      simp (disch := omega) only [if_neg]
      apply hrg k y
      have hR : regL W { A with Φ := A.Φ ++ [⟨g, n, 0, d, e, e, a, b⟩] } = (regL W A).set 4 (some (u (m + 1))) := by
        simp [regL, hm]
      rw [hR, List.getElem?_set, if_neg k4] at hk; exact hk
  · intro j hj k hk
    rw [getD_set, if_neg (by omega), hget]
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjm : j = m
    · subst hjm
      have hfl : (A.Φ ++ [(⟨g, n, 0, d, e, e, a, b⟩ : Fr)]).getD j default = ⟨g, n, 0, d, e, e, a, b⟩ := by
        simp [List.getD_eq_getElem?_getD, ← hm]
      simp only [hfl]
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;>
        subst h <;> simp (disch := omega) only [if_neg, if_pos] <;> simp [Fr.fld] <;> rfl
    · simp (disch := omega) only [if_neg]
      rw [hfr j (by omega) k hk]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < A.Φ.length by omega)]

end OwnP

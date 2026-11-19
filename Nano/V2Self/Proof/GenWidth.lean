/- Gen's width pre-pass (g53) on success: every def body satisfies the width relation `W` (each node's stack width,
CONTINUE = npw − 1, CALL arity = callee npw, IF arms equal, LET value = slot width, LOOP arms = nres, PRIM / BIN
operands 1, def body = nres).  State: s[0] cursor, [1] error, [2] npw, [3] nres, [4] frame count, [5] done; frames
of 4 words (tag, children left, width so far, aux) from word 8; d = (npw, nres) per def seen. -/
import Nano.V2Self.Proof.GenRef
namespace GenRef
open C CallProbe

/-! ## the reference relation -/

/- nodes (top = the parent is the def root: a LOOP is allowed only there) and operand sequences -/
mutual
inductive W (X : Buf) (D : List (UInt64 × UInt64)) (p q : UInt64) : Bool → Nat → UInt64 → Nat → Prop
  | const {top i} : tg X i = 1 → W X D p q top i 1 (i + 2)
  | local {top i} : tg X i = 2 → W X D p q top i (tg X (i + 2)) (i + 3)
  | bin {top i i1 i2} : tg X i = 3 → W X D p q false (i + 2) 1 i1 → W X D p q false i1 1 i2 → W X D p q top i 1 i2
  | ite {top i i1 i2 i3 i4 w} : tg X i = 4 → W X D p q false (i + 2) 1 i1 → W X D p q false i1 1 i2 →
      W X D p q false i2 w i3 → W X D p q false i3 w i4 → W X D p q top i w i4
  | lett {top i i1 i2 w} : tg X i = 5 → W X D p q false (i + 3) (tg X (i + 2)) i1 → W X D p q false i1 w i2 →
      W X D p q top i w i2
  | pair {top i i' ws} : tg X i = 6 → Ws X D p q (i + 2) ws i' → ws.length = (tg X (i + 1)).toNat →
      W X D p q top i (ws.foldl (· + ·) 0) i'
  | call {top i i' ws} : tg X i = 8 → (tg X (i + 1)).toNat < D.length → Ws X D p q (i + 3) ws i' →
      ws.length = (tg X (i + 2)).toNat → ws.foldl (· + ·) 0 = (D.getD (tg X (i + 1)).toNat (0, 0)).1 →
      W X D p q top i (D.getD (tg X (i + 1)).toNat (0, 0)).2 i'
  | prim {top i i' ws} : tg X i = 9 → Ws X D p q (i + 2) ws i' → ws.length = (g33 (tg X (i + 1))).toNat →
      (∀ c ∈ ws, c = 1) → W X D p q top i 1 i'
  | loop {i i1 i2} : tg X i = 10 → W X D p q false (i + 1) q i1 → W X D p q false i1 q i2 → W X D p q true i q i2
  | cont {top i i1 w} : tg X i = 11 → W X D p q false (i + 1) w i1 → w + 1 = p → W X D p q top i q i1
inductive Ws (X : Buf) (D : List (UInt64 × UInt64)) (p q : UInt64) : Nat → List UInt64 → Nat → Prop
  | nil {i} : Ws X D p q i [] i
  | cons {i i1 i2 c cs} : W X D p q false i c i1 → Ws X D p q i1 cs i2 → Ws X D p q i (c :: cs) i2
end

/-! ## the frame stack -/

abbrev Fr := UInt64 × UInt64 × UInt64 × UInt64

def fk (f : Fr) : Nat → UInt64
  | 0 => f.1
  | 1 => f.2.1
  | 2 => f.2.2.1
  | _ => f.2.2.2

def FS (s : Buf) (FL : List Fr) : Prop :=
  8 + 4 * FL.length ≤ s.length ∧ ∀ j < FL.length, ∀ k < 4, s.getD (8 + 4 * j + k) 0 = fk (FL.getD j (0, 0, 0, 0)) k

/-- the width pass's state in def (npw p, nres q), defs D seen, frames FL -/
structure WI (D : List (UInt64 × UInt64)) (p q : UInt64) (d s : Buf) (FL : List Fr) : Prop where
  dl : d.length = 2 * D.length
  dv : ∀ j < D.length, d.getD (2 * j) 0 = (D.getD j (0, 0)).1 ∧ d.getD (2 * j + 1) 0 = (D.getD j (0, 0)).2
  e1 : bget s 1 ≠ 1
  r2 : bget s 2 = p
  r3 : bget s 3 = q
  r4 : bget s 4 = FL.length.toUInt64
  r5 : bget s 5 ≠ 1
  fs : FS s FL
  sl : s.length < 2 ^ 40
  Dl : D.length < 2 ^ 30

theorem bget_n (s : Buf) (n : Nat) (h : n < 2 ^ 64) : bget s n.toUInt64 = s.getD n 0 := by
  simp [bget, u_toNat n h]

/-- s' agrees with s on the frame words and the registers except those in `J` -/
theorem FS_mono {s s' : Buf} {FL : List Fr} (h : FS s FL) (hl : s.length ≤ s'.length)
    (ha : ∀ m, 8 ≤ m → m < 8 + 4 * FL.length → s'.getD m 0 = s.getD m 0) : FS s' FL :=
  ⟨by have := h.1; omega, fun j hj k hk => by rw [ha _ (by omega) (by omega)]; exact h.2 j hj k hk⟩

theorem getD_bset (s : Buf) (j : UInt64) (v : UInt64) (m : Nat) :
    (bset s j v).getD m 0 = if j.toNat = m ∧ j.toNat < s.length then v else s.getD m 0 := by
  have := BufL.bget_bset s j m.toUInt64 v
  simp only [bget, bset] at this ⊢
  rw [getD_set]

theorem bget_eq_getD (s : Buf) (j : UInt64) : bget s j = s.getD j.toNat 0 := rfl

theorem fidx (n j : Nat) (hn : n < 2 ^ 40) (hj : j < 4) :
    (8 + 4 * ((n + 1).toUInt64 - 1) + j.toUInt64 : UInt64).toNat = 8 + 4 * n + j := by
  simp [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le]
  omega

/-- the top frame's words -/
theorem g44_top {D p q d s FL f} (hI : WI D p q d s (FL ++ [f])) (j : Nat) (hj : j < 4) :
    g44 s j.toUInt64 = fk f j := by
  have hl : FL.length < 2 ^ 40 := by have := hI.fs.1; have := hI.sl; simp at *; omega
  unfold g44
  rw [hI.r4, show (FL ++ [f]).length = FL.length + 1 by simp, bget_eq_getD, fidx _ _ hl hj]
  rw [hI.fs.2 FL.length (by simp) j hj]
  simp [List.getD_eq_getElem?_getD]

theorem g44_0 {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) : g44 s 0 = t := g44_top hI 0 (by decide)
theorem g44_1 {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) : g44 s 1 = r := g44_top hI 1 (by decide)
theorem g44_2 {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) : g44 s 2 = a := g44_top hI 2 (by decide)
theorem g44_3 {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) : g44 s 3 = e := g44_top hI 3 (by decide)

/-- a write below the frames to a register other than 1..5 -/
theorem WI_set {D p q d s FL} (hI : WI D p q d s FL) (j : UInt64) (v : UInt64) (hj : j.toNat < 8) (h1 : j ≠ 1) (h2 : j ≠ 2)
    (h3 : j ≠ 3) (h4 : j ≠ 4) (h5 : j ≠ 5) : WI D p q d (bset s j v) FL := by
  have hs8 : 8 ≤ s.length := by have := hI.fs.1; omega
  have hb : ∀ i : UInt64, i ≠ j → bget (bset s j v) i = bget s i := fun i hi => by
    rw [BufL.bget_bset, if_neg]; intro ⟨e, _⟩; exact hi (UInt64.toNat.inj e).symm
  exact { dl := hI.dl, dv := hI.dv
          e1 := by rw [hb 1 (Ne.symm h1)]; exact hI.e1
          r2 := by rw [hb 2 (Ne.symm h2)]; exact hI.r2
          r3 := by rw [hb 3 (Ne.symm h3)]; exact hI.r3
          r4 := by rw [hb 4 (Ne.symm h4)]; exact hI.r4
          r5 := by rw [hb 5 (Ne.symm h5)]; exact hI.r5
          fs := FS_mono hI.fs (by simp [bset]) (fun m hm _ => by rw [getD_bset, if_neg (by omega)])
          sl := by simp [bset]; exact hI.sl
          Dl := hI.Dl }

theorem cur_set {D p q d s FL} (hI : WI D p q d s FL) (v : UInt64) : bget (bset s 0 v) 0 = v := by
  have hs8 : 8 ≤ s.length := by have := hI.fs.1; omega
  rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]

theorem WI_cur {D p q d s FL} (hI : WI D p q d s FL) (v : UInt64) : WI D p q d (bset s 0 v) FL :=
  WI_set hI 0 v (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem g17_4 (s : Buf) (y : Nat) (a b c e : UInt64) (hy : y ≤ s.length) (hs : s.length + 4 < 2 ^ 64) (hy' : y + 4 < 2 ^ 64) :
    let s4 := g17 (g17 (g17 (g17 s y.toUInt64 a) (y.toUInt64 + 1) b) (y.toUInt64 + 2) c) (y.toUInt64 + 3) e
    s4.length = max s.length (y + 4) ∧ ∀ m, s4.getD m 0 =
      if m = y + 3 then e else if m = y + 2 then c else if m = y + 1 then b else if m = y then a else s.getD m 0 := by
  intro s4
  have u0 : (y.toUInt64).toNat = y := u_toNat _ (by omega)
  have u1 : (y.toUInt64 + 1).toNat = y + 1 := by rw [show y.toUInt64 + 1 = (y + 1).toUInt64 by simp [Nat.toUInt64]]; exact u_toNat _ (by omega)
  have u2 : (y.toUInt64 + 2).toNat = y + 2 := by rw [show y.toUInt64 + 2 = (y + 2).toUInt64 by simp [Nat.toUInt64]]; exact u_toNat _ (by omega)
  have u3 : (y.toUInt64 + 3).toNat = y + 3 := by rw [show y.toUInt64 + 3 = (y + 3).toUInt64 by simp [Nat.toUInt64]]; exact u_toNat _ (by omega)
  have l1 := g17_len s y.toUInt64 a (by omega) (by omega)
  rw [u0] at l1
  have l2 := g17_len (g17 s y.toUInt64 a) (y.toUInt64 + 1) b (by rw [u1, l1]; omega) (by rw [l1]; omega)
  rw [u1, l1] at l2
  have l3 := g17_len _ (y.toUInt64 + 2) c (by rw [u2, l2]; omega) (by rw [l2]; omega)
  rw [u2, l2] at l3
  have l4 := g17_len _ (y.toUInt64 + 3) e (by rw [u3, l3]; omega) (by rw [l3]; omega)
  rw [u3, l3] at l4
  refine ⟨by rw [l4]; omega, fun m => ?_⟩
  simp only [s4]
  rw [g17_get _ _ _ (by rw [u3, l3]; omega) (by rw [l3]; omega), g17_get _ _ _ (by rw [u2, l2]; omega) (by rw [l2]; omega),
    g17_get _ _ _ (by rw [u1, l1]; omega) (by rw [l1]; omega), g17_get _ _ _ (by omega) (by omega), u0, u1, u2, u3]

/-- push a frame (g47) -/
theorem WI_push {D p q d s FL} (hI : WI D p q d s FL) (hF : FL.length < 2 ^ 32) (a b c e : UInt64) :
    WI D p q d (g47 s a b c e) (FL ++ [(a, b, c, e)]) ∧ bget (g47 s a b c e) 0 = bget s 0 := by
  have hf := hI.fs.1
  have hsl := hI.sl
  have hn : (8 + 4 * bget s 4 : UInt64) = (8 + 4 * FL.length).toUInt64 := by
    rw [hI.r4]; simp [Nat.toUInt64]
  obtain ⟨hl, hg⟩ := g17_4 s (8 + 4 * FL.length) a b c e (by omega) (by omega) (by omega)
  unfold g47
  simp only []
  rw [hn]
  generalize hs4 : g17 (g17 (g17 (g17 s (8 + 4 * FL.length).toUInt64 a) ((8 + 4 * FL.length).toUInt64 + 1) b)
    ((8 + 4 * FL.length).toUInt64 + 2) c) ((8 + 4 * FL.length).toUInt64 + 3) e = s4 at hl hg
  have h4 : 4 < s4.length := by rw [hl]; omega
  have hb : ∀ i : UInt64, i.toNat < 8 → i ≠ 4 → bget (bset s4 4 (bget s 4 + 1)) i = bget s i := fun i hi h4' => by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => h4' (UInt64.toNat.inj e).symm), bget_eq_getD, bget_eq_getD, hg,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨{ dl := hI.dl, dv := hI.dv
            e1 := by rw [hb 1 (by decide) (by decide)]; exact hI.e1
            r2 := by rw [hb 2 (by decide) (by decide)]; exact hI.r2
            r3 := by rw [hb 3 (by decide) (by decide)]; exact hI.r3
            r4 := by
              rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩, hI.r4]; simp [Nat.toUInt64]
            r5 := by rw [hb 5 (by decide) (by decide)]; exact hI.r5
            fs := ⟨by simp [bset]; rw [hl]; omega, fun j hj k hk => ?_⟩
            sl := by simp [bset]; rw [hl]; omega
            Dl := hI.Dl }, hb 0 (by decide) (by decide)⟩
  simp only [List.length_append, List.length_singleton] at hj
  rw [getD_bset, if_neg (by simp; omega), hg]
  by_cases hjF : j = FL.length
  · subst hjF
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [fk]
  · have hj' : j < FL.length := by omega
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hI.fs.2 j hj' k hk]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']

def fset (f : Fr) (j : Nat) (v : UInt64) : Fr :=
  match j with
  | 0 => (v, f.2.1, f.2.2.1, f.2.2.2)
  | 1 => (f.1, v, f.2.2.1, f.2.2.2)
  | 2 => (f.1, f.2.1, v, f.2.2.2)
  | _ => (f.1, f.2.1, f.2.2.1, v)

theorem fk_fset (f : Fr) (j k : Nat) (v : UInt64) (hj : j < 4) (hk : k < 4) : fk (fset f j v) k = if j = k then v else fk f k := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [fk, fset]

/-- write field j of the top frame (g46) -/
theorem WI_g46 {D p q d s FL f} (hI : WI D p q d s (FL ++ [f])) (j : Nat) (hj : j < 4) (v : UInt64) :
    WI D p q d (g46 s j.toUInt64 v) (FL ++ [fset f j v]) ∧ bget (g46 s j.toUInt64 v) 0 = bget s 0 := by
  have hf := hI.fs.1
  have hsl := hI.sl
  simp only [List.length_append, List.length_singleton] at hf
  have hl : FL.length < 2 ^ 40 := by omega
  unfold g46
  have hix : (8 + 4 * (bget s 4 - 1) + j.toUInt64 : UInt64).toNat = 8 + 4 * FL.length + j := by
    rw [hI.r4, show (FL ++ [f]).length = FL.length + 1 by simp]; exact fidx _ _ hl hj
  have hb : ∀ i : UInt64, i.toNat < 8 → bget (bset s (8 + 4 * (bget s 4 - 1) + j.toUInt64) v) i = bget s i := fun i hi => by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by rw [hix] at e; omega)]
  refine ⟨{ dl := hI.dl, dv := hI.dv
            e1 := by rw [hb 1 (by decide)]; exact hI.e1
            r2 := by rw [hb 2 (by decide)]; exact hI.r2
            r3 := by rw [hb 3 (by decide)]; exact hI.r3
            r4 := by rw [hb 4 (by decide), hI.r4]; simp
            r5 := by rw [hb 5 (by decide)]; exact hI.r5
            fs := ⟨by simp [bset]; omega, fun i hi k hk => ?_⟩
            sl := by simp [bset]; exact hsl
            Dl := hI.Dl }, hb 0 (by decide)⟩
  simp only [List.length_append, List.length_singleton] at hi
  rw [getD_bset, hix]
  by_cases hiF : i = FL.length
  · subst hiF
    rw [show (FL ++ [fset f j v]).getD FL.length (0, 0, 0, 0) = fset f j v by simp [List.getD_eq_getElem?_getD],
      fk_fset _ _ _ _ hj hk]
    by_cases hjk : j = k
    · subst hjk; rw [if_pos ⟨rfl, by omega⟩, if_pos rfl]
    · rw [if_neg (by omega), if_neg hjk, hI.fs.2 FL.length (by simp) k hk]
      simp [List.getD_eq_getElem?_getD]
  · have hi' : i < FL.length := by omega
    rw [if_neg (by omega), hI.fs.2 i (by simp; omega) k hk]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

/-- pop the top frame -/
theorem WI_pop {D p q d s FL f} (hI : WI D p q d s (FL ++ [f])) :
    WI D p q d (bset s 4 (bget s 4 - 1)) FL ∧ bget (bset s 4 (bget s 4 - 1)) 0 = bget s 0 := by
  have hf := hI.fs.1
  simp only [List.length_append, List.length_singleton] at hf
  have hb : ∀ i : UInt64, i ≠ 4 → bget (bset s 4 (bget s 4 - 1)) i = bget s i := fun i hi => by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => hi (UInt64.toNat.inj e).symm)]
  refine ⟨{ dl := hI.dl, dv := hI.dv
            e1 := by rw [hb 1 (by decide)]; exact hI.e1
            r2 := by rw [hb 2 (by decide)]; exact hI.r2
            r3 := by rw [hb 3 (by decide)]; exact hI.r3
            r4 := by
              rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩, hI.r4]
              simp [Nat.toUInt64]
            r5 := by rw [hb 5 (by decide)]; exact hI.r5
            fs := ⟨by simp [bset]; omega, fun i hi k hk => ?_⟩
            sl := by simp [bset]; exact hI.sl
            Dl := hI.Dl }, hb 0 (by decide)⟩
  rw [getD_bset, if_neg (by simp; omega), hI.fs.2 i (by simp; omega) k hk]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem err_g48 (s : Buf) (h : 2 ≤ s.length) : bget (g48 s) 1 = 1 := by
  unfold g48; rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]

/-! ## g49 (deliver a child's width to the top frame), g50 (pop) -/

/-- g49's check (1 = error) -/
def zf (t r a e c q : UInt64) : UInt64 :=
  if t == 3 then (if c == 1 then g_0 else g_1)
  else if t == 4 then (if 2 < r then (if c == 1 then g_0 else g_1) else if r == 2 then g_0 else if c == a then g_0 else g_1)
  else if t == 5 then (if r == 2 then (if c == e then g_0 else g_1) else g_0)
  else if t == 9 then (if c == 1 then g_0 else g_1)
  else if t == 10 then (if c == q then g_0 else g_1)
  else if t < 12 then g_0 else if t == 100 then g_0 else g_1
/-- g49's new width so far -/
def vf (t a c : UInt64) : UInt64 := if t == 6 then a + c else if t == 8 then a + c else c

theorem g49_ok {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) (c : UInt64) (hz : zf t r a e c q ≠ 1) :
    WI D p q d (g49 s c) (FL ++ [(t, r - 1, vf t a c, e)]) ∧ bget (g49 s c) 0 = bget s 0 := by
  obtain ⟨h1, h1'⟩ := WI_g46 hI 1 (by decide) (r - 1)
  obtain ⟨h2, h2'⟩ := WI_g46 h1 2 (by decide) (vf t a c)
  have e0 := g44_0 hI; have e1 := g44_1 hI; have e2 := g44_2 hI; have e3 := g44_3 hI
  have hq := hI.r3
  unfold g49
  extract_lets t' r' a' e' q' s1 z v
  have ht : t' = t := e0
  have hr : r' = r := e1
  have ha : a' = a := e2
  have he : e' = e := e3
  have hq' : q' = q := hq
  clear_value t' r' a' e' q'
  subst ht hr ha he hq'
  have hz' : z = zf t' r' a' e' c q' := rfl
  have hv : v = vf t' a' c := rfl
  have hs1 : s1 = g46 s 1 (r' - 1) := rfl
  clear_value z v s1
  subst hz' hv hs1
  rw [if_neg (by simpa using hz)]
  exact ⟨h2, h2'.trans h1'⟩

theorem g49_bad {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) (c : UInt64) (hz : zf t r a e c q = 1) :
    bget (g49 s c) 1 = 1 := by
  obtain ⟨h1, -⟩ := WI_g46 hI 1 (by decide) (r - 1)
  have e0 := g44_0 hI; have e1 := g44_1 hI; have e2 := g44_2 hI; have e3 := g44_3 hI
  have hq := hI.r3
  unfold g49
  extract_lets t' r' a' e' q' s1 z v
  have ht : t' = t := e0
  have hr : r' = r := e1
  have ha : a' = a := e2
  have he : e' = e := e3
  have hq' : q' = q := hq
  clear_value t' r' a' e' q'
  subst ht hr ha he hq'
  have hz' : z = zf t' r' a' e' c q' := rfl
  have hs1 : s1 = g46 s 1 (r' - 1) := rfl
  clear_value z s1
  subst hz' hs1
  rw [if_pos (by simp [hz])]
  exact err_g48 _ (by unfold g46; rw [BufL.length_bset]; have := hI.fs.1; omega)

/-! ## the pass as a state machine -/

abbrev WSt := Buf × Buf

def wst (x : Buf) (st : WSt) : WSt := g51 x st.1 st.2
def wlive (st : WSt) : Prop := bget st.2 1 ≠ 1 ∧ bget st.2 5 ≠ 1
def werr (st : WSt) : Prop := bget st.2 1 = 1 ∧ 2 ≤ st.2.length

def wit (x : Buf) : Nat → WSt → WSt
  | 0, st => st
  | n + 1, st => wit x n (wst x st)

theorem wit_add (x : Buf) : ∀ (n m : Nat) (st : WSt), wit x (n + m) st = wit x n (wit x m st)
  | n, 0, st => rfl
  | n, m + 1, st => by rw [show n + (m + 1) = (n + m) + 1 by omega]; simp only [wit]; exact wit_add x n m (wst x st)

def WReach (x : Buf) (st : WSt) (P : WSt → Prop) : Prop :=
  ∃ m, (∀ j < m, wlive (wit x j st)) ∧ (P (wit x m st) ∨ werr (wit x m st))

theorem WReach.done {x st} {P : WSt → Prop} (h : P st) : WReach x st P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inl h⟩
theorem WReach.error {x st} {P : WSt → Prop} (h : werr st) : WReach x st P :=
  ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr h⟩
theorem WReach.step {x st} {P : WSt → Prop} (hl : wlive st) (h : WReach x (wst x st) P) : WReach x st P := by
  obtain ⟨m, hm, hp⟩ := h
  refine ⟨m + 1, fun j hj => ?_, hp⟩
  rcases j with _ | j
  · exact hl
  · exact hm j (by omega)
theorem WReach.bind {x st} {P Q : WSt → Prop} (h : WReach x st P) (hq : ∀ st', P st' → WReach x st' Q) : WReach x st Q := by
  obtain ⟨m, hm, hp⟩ := h
  rcases hp with hp | he
  · obtain ⟨n, hn, hq⟩ := hq _ hp
    refine ⟨n + m, fun j hj => ?_, by rw [wit_add]; exact hq⟩
    by_cases hjm : j < m
    · exact hm j hjm
    · have := hn (j - m) (by omega)
      rw [← wit_add] at this
      rwa [show j - m + m = j by omega] at this
  · exact ⟨m, hm, .inr he⟩

theorem wlive_of {D p q d s FL} (hI : WI D p q d s FL) : wlive (d, s) := ⟨hI.e1, hI.r5⟩
theorem werr_of {d s : Buf} (h : bget s 1 = 1) (hl : 2 ≤ s.length) : werr (d, s) := ⟨h, hl⟩

/-- g52 on a live state is one step -/
theorem g52_step (x : Buf) (st : WSt) (h : wlive st) (n : Nat) :
    g52 (n + 1) (x, st) = g52 n (x, wst x st) := by
  obtain ⟨d, s⟩ := st
  obtain ⟨h1, h5⟩ := h
  simp only [g52]
  rw [if_neg (by simpa using h1), if_neg (by simpa using h5)]
  unfold wst
  generalize g51 x d s = r
  obtain ⟨_, _⟩ := r
  rfl

theorem g52_iter (x : Buf) : ∀ (m n : Nat) (st : WSt), (∀ j < m, wlive (wit x j st)) →
    g52 (n + m) (x, st) = g52 n (x, wit x m st)
  | 0, n, st, _ => rfl
  | m + 1, n, st, h => by
    rw [show n + (m + 1) = (n + m) + 1 by omega, g52_step x st (h 0 (by omega))]
    exact g52_iter x m n (wst x st) (fun j hj => h (j + 1) (by omega))

/-- an error state stays one -/
theorem g52_err (x : Buf) (st : WSt) (h : werr st) : ∀ n, bget (g52 n (x, st)).2.2 1 = 1
  | 0 => by obtain ⟨d, s⟩ := st; simp only [g52]; exact err_g48 _ h.2
  | n + 1 => by obtain ⟨d, s⟩ := st; simp only [g52]; rw [if_pos (by simpa using h.1)]; exact h.1

/-- the bridge: a pass ending without error passed through every `WReach` claim -/
theorem wreach_run {x st} {P : WSt → Prop} (h : WReach x st P) (N : Nat) (hok : bget (g52 N (x, st)).2.2 1 ≠ 1)
    (hlen : ∀ m, 2 ≤ (wit x m st).2.length) :
    ∃ m, m ≤ N ∧ P (wit x m st) ∧ g52 N (x, st) = g52 (N - m) (x, wit x m st) := by
  obtain ⟨m, hm, hp⟩ := h
  by_cases hNm : N < m
  · exfalso
    have e := g52_iter x N 0 st (fun j hj => hm j (by omega))
    simp only [Nat.zero_add] at e
    rw [e] at hok
    apply hok
    generalize hw : wit x N st = w at hok
    obtain ⟨d, s⟩ := w
    simp only [g52]
    exact err_g48 _ (by have := hlen N; rw [hw] at this; exact this)
  have e := g52_iter x m (N - m) st hm
  rw [show N - m + m = N by omega] at e
  rcases hp with hp | he
  · exact ⟨m, by omega, hp, e⟩
  · exfalso; rw [e] at hok; exact hok (g52_err x _ he (N - m))

/-! ## g51 at a node (frames present, the top frame wants a child) -/

/-- g51's node branch, on its inputs (cursor i, tag c, word i+1 e, #defs h, word i+2 p, frame count n) -/
def gnode (s d : Buf) (i c e h p n : UInt64) : Buf × Buf :=
  if c == 1 then (d, g49 (bset s 0 (i + 2)) 1)
  else if c == 2 then (d, g49 (bset s 0 (i + 3)) p)
  else if c == 3 then (d, g47 (bset s 0 (i + 2)) 3 2 0 0)
  else if c == 4 then (d, g47 (bset s 0 (i + 2)) 4 4 0 0)
  else if c == 5 then (d, g47 (bset s 0 (i + 3)) 5 2 0 p)
  else if c == 6 then (d, g47 (bset s 0 (i + 2)) 6 e 0 0)
  else if c == 8 then
    if e < h then (d, g47 (bset s 0 (i + 3)) 8 p 0 e) else (d, g48 s)
  else if c == 9 then (d, g47 (bset s 0 (i + 2)) 9 (g33 e) 0 0)
  else if c == 10 then (if n == 1 then (d, g47 (bset s 0 (i + 1)) 10 2 0 0) else (d, g48 s))
  else if c == 11 then (d, g47 (bset s 0 (i + 1)) 11 1 0 0)
  else (d, g48 s)

theorem n_ne0 (n : Nat) (h : n < 2 ^ 40) : ¬ ((n + 1).toUInt64 == 0) = true := by
  simp [Nat.toUInt64]; intro e; have := congrArg UInt64.toNat e; simp at this; omega

theorem g51_node (x : Buf) {D p q d s FL f} (hI : WI D p q d s (FL ++ [f])) (hr : f.2.1 ≠ 0) :
    g51 x d s = gnode s d (bget s 0) (bget x (bget s 0)) (bget x (bget s 0 + 1)) (bsize d >>> 1) (bget x (bget s 0 + 2))
      (bget s 4) := by
  have hl : FL.length < 2 ^ 40 := by have := hI.fs.1; have := hI.sl; simp at *; omega
  have h4 : ¬ (bget s 4 == 0) = true := by
    rw [hI.r4, show (FL ++ [f]).length = FL.length + 1 by simp]; exact n_ne0 _ hl
  have h1 : ¬ (g44 s 1 == 0) = true := by
    rw [show g44 s 1 = f.2.1 from g44_top hI 1 (by decide)]; simpa using hr
  unfold g51
  extract_lets i c e h p' q' f' u v
  rw [if_neg h4, if_neg h1]
  rfl

/-- g51 when the top frame has all its children: pop (g50) -/
theorem g51_pop (x : Buf) {D p q d s FL t a e} (hI : WI D p q d s (FL ++ [(t, 0, a, e)])) :
    g51 x d s = (d, g50 x s (bget d (2 * e)) (bget d (2 * e + 1))) := by
  have hl : FL.length < 2 ^ 40 := by have := hI.fs.1; have := hI.sl; simp at *; omega
  have h4 : ¬ (bget s 4 == 0) = true := by
    rw [hI.r4]; simp only [List.length_append, List.length_singleton]; exact n_ne0 _ hl
  have h1 : (g44 s 1 == 0) = true := by rw [g44_1 hI]; rfl
  unfold g51
  extract_lets i c e' h p' q' f' u v
  rw [if_neg h4, if_pos h1]
  have hf : f' = e := by simp only [f']; rw [if_neg h4, g44_3 hI]
  simp only [u, v, hf]

/-- g50's check on the popped frame (CALL arity, CONTINUE = npw − 1) -/
def zp (t a u p : UInt64) : UInt64 :=
  if t == 8 then (if a == u then g_0 else g_1) else if t == 11 then (if a + 1 == p then g_0 else g_1) else g_0
/-- the popped frame's width -/
def wf (t a v q : UInt64) : UInt64 :=
  if t == 3 then g_1 else if t == 8 then v else if t == 9 then g_1 else if t == 10 then q else if t == 11 then q else a

theorem g50_eq (x : Buf) {D p q d s FL t r a e} (hI : WI D p q d s (FL ++ [(t, r, a, e)])) (ht : t ≠ 100) (u v : UInt64) :
    g50 x s u v = if zp t a u p == 1 then g48 (bset s 4 (bget s 4 - 1)) else g49 (bset s 4 (bget s 4 - 1)) (wf t a v q) := by
  unfold g50
  extract_lets t' a' e' p' q' s1 i
  have h1 : t' = t := g44_0 hI
  have h2 : a' = a := g44_2 hI
  have h3 : p' = p := hI.r2
  have h4 : q' = q := hI.r3
  clear_value t' a' e' p' q'
  subst h1 h2 h3 h4
  rw [if_neg (by simpa using ht)]
  rfl

theorem g50_root (x : Buf) {D p q d s FL r a e} (hI : WI D p q d s (FL ++ [(100, r, a, e)])) (u v : UInt64) :
    g50 x s u v = if a == q then (if bget x (bget s 0) == 21 then bset (bset s 4 (bget s 4 - 1)) 0 (bget s 0 + 1)
      else g48 (bset s 4 (bget s 4 - 1))) else g48 (bset s 4 (bget s 4 - 1)) := by
  have hb : bget (bset s 4 (bget s 4 - 1)) 0 = bget s 0 := by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e)]
  unfold g50
  extract_lets t' a' e' p' q' s1 i
  have h1 : t' = 100 := g44_0 hI
  have h2 : a' = a := g44_2 hI
  have h4 : q' = q := hI.r3
  have hi : i = bget s 0 := hb
  clear_value t' a' e' p' q' i
  subst h1 h2 h4 hi
  rw [if_pos (by decide)]

theorem g49_len (s : Buf) (c : UInt64) : (g49 s c).length = s.length := by
  unfold g49; extract_lets t r a e q s1 z v
  split <;> simp [g48, g46, bset, s1]

theorem WI_len {D p q d s FL} (hI : WI D p q d s FL) : 8 ≤ s.length := by have := hI.fs.1; omega

theorem uk1 (i : Nat) : i.toUInt64 + 1 = (i + 1).toUInt64 := u_add i 1
theorem uk2 (i : Nat) : i.toUInt64 + 2 = (i + 2).toUInt64 := u_add i 2
theorem uk3 (i : Nat) : i.toUInt64 + 3 = (i + 3).toUInt64 := u_add i 3
theorem uk5 (i : Nat) : i.toUInt64 + 5 = (i + 5).toUInt64 := u_add i 5
theorem uk6 (i : Nat) : i.toUInt64 + 6 = (i + 6).toUInt64 := u_add i 6
theorem tk1 (X : Buf) (i : Nat) (h : i + 1 < 2 ^ 64) : bget X (i.toUInt64 + 1) = tg X (i + 1) := tg_u1 X i 1 h
theorem tk2 (X : Buf) (i : Nat) (h : i + 2 < 2 ^ 64) : bget X (i.toUInt64 + 2) = tg X (i + 2) := tg_u1 X i 2 h
theorem tk5 (X : Buf) (i : Nat) (h : i + 5 < 2 ^ 64) : bget X (i.toUInt64 + 5) = tg X (i + 5) := tg_u1 X i 5 h

/-! ## visiting one node -/

/-- after the node at i: its width w (W), cursor at i', the width delivered to the parent frame f -/
def NP (X : Buf) (D : List (UInt64 × UInt64)) (p q : UInt64) (d0 : Buf) (FL : List Fr) (f : Fr) (i : Nat) (st : WSt) : Prop :=
  ∃ w i', W X D p q FL.isEmpty i w i' ∧ i < i' ∧ i' ≤ X.length + 3 ∧ st.1 = d0 ∧ bget st.2 0 = i'.toUInt64 ∧
    zf f.1 f.2.1 f.2.2.1 f.2.2.2 w q ≠ 1 ∧ WI D p q d0 st.2 (FL ++ [(f.1, f.2.1 - 1, vf f.1 f.2.2.1 w, f.2.2.2)])

def NS (X : Buf) (D : List (UInt64 × UInt64)) (p q : UInt64) (i : Nat) : Prop :=
  i ≤ X.length + 3 → ∀ d s FL f, WI D p q d s (FL ++ [f]) → bget s 0 = i.toUInt64 → f.2.1 ≠ 0 →
    (FL ++ [f]).length ≤ i → WReach X (d, s) (NP X D p q d FL f i)

/-- deliver width w at the end of a node (cursor i') -/
theorem fin_node {X D p q d s FL f i i' w} (hI : WI D p q d s (FL ++ [f])) (hc : bget s 0 = i'.toUInt64)
    (hW : W X D p q FL.isEmpty i w i') (hii : i < i') (hiX : i' ≤ X.length + 3) :
    WReach X (d, g49 s w) (NP X D p q d FL f i) := by
  obtain ⟨t, r, a, e⟩ := f
  by_cases hz : zf t r a e w q = 1
  · exact WReach.error (werr_of (g49_bad hI w hz) (by rw [g49_len]; have := WI_len hI; omega))
  obtain ⟨hI2, h0⟩ := g49_ok hI w hz
  exact WReach.done ⟨w, i', hW, hii, hiX, rfl, by rw [h0, hc], hz, hI2⟩

theorem n_const {X D p q i} (hX : X.length < 2 ^ 31) (ht : tg X i = 1) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr _
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht]
  unfold gnode; rw [if_pos (by decide)]
  have hI1 := WI_cur hI (i.toUInt64 + 2)
  exact fin_node hI1 (by rw [cur_set hI, uk2]) (W.const ht) (by omega) (by omega)

theorem n_local {X D p q i} (hX : X.length < 2 ^ 31) (ht : tg X i = 2) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr _
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht, tk2 X i (by omega)]
  unfold gnode; rw [if_neg (by decide), if_pos (by decide)]
  have hI1 := WI_cur hI (i.toUInt64 + 3)
  exact fin_node hI1 (by rw [cur_set hI, uk3]) (W.local ht) (by omega) (by omega)

/-- a composite node's last step: pop its frame (g50), check, deliver its width -/
theorem fin_pop {X D p q d s FL f t a e i i'} (hI : WI D p q d s ((FL ++ [f]) ++ [(t, 0, a, e)])) (ht : t ≠ 100)
    (hc : bget s 0 = i'.toUInt64)
    (hW : zp t a (bget d (2 * e)) p ≠ 1 → W X D p q FL.isEmpty i (wf t a (bget d (2 * e + 1)) q) i')
    (hii : i < i') (hiX : i' ≤ X.length + 3) : WReach X (d, s) (NP X D p q d FL f i) := by
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_pop X hI, g50_eq X hI ht]
  obtain ⟨hI1, h0⟩ := WI_pop hI
  by_cases hz : zp t a (bget d (2 * e)) p = 1
  · rw [if_pos (by simp [hz])]
    exact WReach.error (werr_of (err_g48 _ (by have := WI_len hI1; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega))
  rw [if_neg (by simpa using hz)]
  exact fin_node hI1 (by rw [h0, hc]) (hW hz) hii hiX

theorem WI_fr {D p q d s FL f} (f' : Fr) (h : WI D p q d s (FL ++ [f])) (e : f = f') : WI D p q d s (FL ++ [f']) := e ▸ h

theorem ie (FL : List Fr) (f : Fr) : (FL ++ [f]).isEmpty = false := by simp

theorem n_bin {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 3) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht]
  unfold gnode; rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 2)) (by simp at hl ⊢; omega) 3 2 0 0
  refine (IH (i + 2) (by omega) (by omega) _ _ _ _ hI1 (by rw [h0, cur_set hI, uk2]) (by decide) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨w1, i1, hW1, hi1, hi1X, rfl, hc1, hz1, hI2⟩
  rw [ie] at hW1
  have e1 : w1 = 1 := Classical.byContradiction fun h => hz1 (by simp [zf, h, g_1])
  subst e1
  refine (IH i1 (by omega) hi1X _ _ _ _ hI2 hc1 (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d2, s2⟩ ⟨w2, i2, hW2, hi2, hi2X, rfl, hc2, hz2, hI3⟩
  rw [ie] at hW2
  have e2 : w2 = 1 := Classical.byContradiction fun h => hz2 (by simp [zf, h, g_1])
  subst e2
  exact fin_pop hI3 (by decide) hc2 (fun _ => W.bin ht hW1 hW2) (by omega) hi2X

theorem n_ite {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 4) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht]
  unfold gnode; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 2)) (by simp at hl ⊢; omega) 4 4 0 0
  refine (IH (i + 2) (by omega) (by omega) _ _ _ _ hI1 (by rw [h0, cur_set hI, uk2]) (by decide) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨w1, i1, hW1, hi1, hi1X, rfl, hc1, hz1, hI2⟩
  rw [ie] at hW1
  have e1 : w1 = 1 := Classical.byContradiction fun h => hz1 (by simp [zf, h, g_1])
  subst e1
  replace hI2 := WI_fr ((4 : UInt64), (3 : UInt64), (1 : UInt64), (0 : UInt64)) hI2 (by simp [vf])
  refine (IH i1 (by omega) hi1X _ _ _ _ hI2 hc1 (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d2, s2⟩ ⟨w2, i2, hW2, hi2, hi2X, rfl, hc2, hz2, hI3⟩
  rw [ie] at hW2
  have e2 : w2 = 1 := Classical.byContradiction fun h => hz2 (by simp [zf, h, g_1])
  subst e2
  replace hI3 := WI_fr ((4 : UInt64), (2 : UInt64), (1 : UInt64), (0 : UInt64)) hI3 (by simp [vf])
  refine (IH i2 (by omega) hi2X _ _ _ _ hI3 hc2 (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d3, s3⟩ ⟨w3, i3, hW3, hi3, hi3X, rfl, hc3, -, hI4⟩
  rw [ie] at hW3
  replace hI4 := WI_fr ((4 : UInt64), (1 : UInt64), w3, (0 : UInt64)) hI4 (by simp [vf])
  refine (IH i3 (by omega) hi3X _ _ _ _ hI4 hc3 (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d4, s4⟩ ⟨w4, i4, hW4, hi4, hi4X, rfl, hc4, hz4, hI5⟩
  rw [ie] at hW4
  change zf 4 1 w3 0 w4 q ≠ 1 at hz4
  have e4 : w4 = w3 := Classical.byContradiction fun h => hz4 (by simp [zf, h, g_1])
  subst e4
  replace hI5 := WI_fr ((4 : UInt64), (0 : UInt64), w4, (0 : UInt64)) hI5 (by simp [vf])
  exact fin_pop hI5 (by decide) hc4 (fun _ => by simpa [wf, vf] using W.ite ht hW1 hW2 hW3 hW4) (by omega) hi4X

theorem n_let {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 5) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht, tk2 X i (by omega)]
  unfold gnode; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 3)) (by simp at hl ⊢; omega) 5 2 0 (tg X (i + 2))
  refine (IH (i + 3) (by omega) (by omega) _ _ _ _ hI1 (by rw [h0, cur_set hI, uk3]) (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨w1, i1, hW1, hi1, hi1X, rfl, hc1, hz1, hI2⟩
  rw [ie] at hW1
  have e1 : w1 = tg X (i + 2) := Classical.byContradiction fun h => hz1 (by simp [zf, h, g_1])
  subst e1
  replace hI2 := WI_fr ((5 : UInt64), (1 : UInt64), tg X (i + 2), tg X (i + 2)) hI2 (by simp [vf])
  refine (IH i1 (by omega) hi1X _ _ _ _ hI2 hc1 (by simp) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d2, s2⟩ ⟨w2, i2, hW2, hi2, hi2X, rfl, hc2, -, hI3⟩
  rw [ie] at hW2
  replace hI3 := WI_fr ((5 : UInt64), (0 : UInt64), w2, tg X (i + 2)) hI3 (by simp [vf])
  exact fin_pop hI3 (by decide) hc2 (fun _ => by simpa [wf, vf] using W.lett ht hW1 hW2) (by omega) hi2X

theorem n_cont {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 11) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht]
  unfold gnode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 1)) (by simp at hl ⊢; omega) 11 1 0 0
  refine (IH (i + 1) (by omega) (by omega) _ _ _ _ hI1 (by rw [h0, cur_set hI, uk1]) (by decide) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨w1, i1, hW1, hi1, hi1X, rfl, hc1, -, hI2⟩
  rw [ie] at hW1
  replace hI2 := WI_fr ((11 : UInt64), (0 : UInt64), w1, (0 : UInt64)) hI2 (by simp [vf])
  refine fin_pop hI2 (by decide) hc1 (fun hz => ?_) (by omega) hi1X
  have e : w1 + 1 = p := Classical.byContradiction fun h => hz (by simp [zp, vf, h, g_1])
  simpa [wf] using W.cont ht hW1 e

theorem n_loop {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 10) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht]
  unfold gnode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  rcases FL with _ | ⟨g, FL'⟩
  · rw [if_pos (by rw [hI.r4]; rfl)]
    obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 1)) (by simp) 10 2 0 0
    refine (IH (i + 1) (by omega) (by omega) _ _ _ _ hI1 (by rw [h0, cur_set hI, uk1]) (by decide) (by simp at hl ⊢; omega)).bind ?_
    rintro ⟨d1, s1⟩ ⟨w1, i1, hW1, hi1, hi1X, rfl, hc1, hz1, hI2⟩
    rw [ie] at hW1
    have e1 : w1 = q := Classical.byContradiction fun h => hz1 (by simp [zf, h, g_1])
    subst e1
    replace hI2 := WI_fr ((10 : UInt64), (1 : UInt64), w1, (0 : UInt64)) hI2 (by simp [vf])
    refine (IH i1 (by omega) hi1X _ _ _ _ hI2 hc1 (by simp) (by simp at hl ⊢; omega)).bind ?_
    rintro ⟨d2, s2⟩ ⟨w2, i2, hW2, hi2, hi2X, rfl, hc2, hz2, hI3⟩
    rw [ie] at hW2
    change zf 10 1 w1 0 w2 w1 ≠ 1 at hz2
    have e2 : w2 = w1 := Classical.byContradiction fun h => hz2 (by simp [zf, h, g_1])
    subst e2
    replace hI3 := WI_fr ((10 : UInt64), (0 : UInt64), w2, (0 : UInt64)) hI3 (by simp [vf])
    exact fin_pop hI3 (by decide) hc2 (fun _ => by simpa [wf, vf] using W.loop ht hW1 hW2) (by omega) hi2X
  · rw [if_neg]
    · exact WReach.error (werr_of (err_g48 _ (by have := WI_len hI; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega))
    · rw [hI.r4]; simp [Nat.toUInt64]; intro e; have := congrArg UInt64.toNat e; simp at this
      have := hI.fs.1; have := hI.sl; simp at *; omega

end GenRef

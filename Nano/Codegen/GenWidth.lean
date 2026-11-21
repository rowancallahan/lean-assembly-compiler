/- Gen's width pre-pass (g53) on success: every def body satisfies the width relation `W` (each node's stack width,
CONTINUE = npw − 1, CALL arity = callee npw, IF arms equal, LET value = slot width, LOOP arms = nres, PRIM / BIN
operands 1, def body = nres).  State: s[0] cursor, [1] error, [2] npw, [3] nres, [4] frame count, [5] done; frames
of 4 words (tag, children left, width so far, aux) from word 8; d = (npw, nres) per def seen. -/
import Nano.Codegen.GenRef
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
  Dl : D.length < 2 ^ 32

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
def wlive (st : WSt) : Prop := bget st.2 1 ≠ 1 ∧ bget st.2 5 ≠ 1 ∧ 2 ≤ st.2.length
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

theorem wlive_of {D p q d s FL} (hI : WI D p q d s FL) : wlive (d, s) := ⟨hI.e1, hI.r5, by have := hI.fs.1; dsimp only; omega⟩
theorem werr_of {d s : Buf} (h : bget s 1 = 1) (hl : 2 ≤ s.length) : werr (d, s) := ⟨h, hl⟩

/-- g52 on a live state is one step -/
theorem g52_step (x : Buf) (st : WSt) (h : wlive st) (n : Nat) :
    g52 (n + 1) (x, st) = g52 n (x, wst x st) := by
  obtain ⟨d, s⟩ := st
  obtain ⟨h1, h5, -⟩ := h
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
theorem wreach_run {x st} {P : WSt → Prop} (h : WReach x st P) (N : Nat) (hok : bget (g52 N (x, st)).2.2 1 ≠ 1) :
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
    exact err_g48 _ (by have := (hm N hNm).2.2; rw [hw] at this; exact this)
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

/-! ## operand sequences (PAIR, CALL, PRIM) -/

def SqP (X : Buf) (D : List (UInt64 × UInt64)) (p q : UInt64) (d0 : Buf) (FL : List Fr) (t a e : UInt64) (n j : Nat)
    (st : WSt) : Prop :=
  ∃ ws j', Ws X D p q j ws j' ∧ ws.length = n ∧ j ≤ j' ∧ j' ≤ X.length + 3 ∧ st.1 = d0 ∧ bget st.2 0 = j'.toUInt64 ∧
    (t = 9 → ∀ c ∈ ws, c = 1) ∧ WI D p q d0 st.2 (FL ++ [(t, 0, ws.foldl (vf t) a, e)])

theorem wseq {X D p q i0} (IH : ∀ j, i0 < j → NS X D p q j) (t e : UInt64) (ht : t = 6 ∨ t = 8 ∨ t = 9) (FL : List Fr)
    (hFL : FL ≠ []) : ∀ n j d s a, i0 < j → j ≤ X.length + 3 → n < 2 ^ 64 →
    WI D p q d s (FL ++ [(t, n.toUInt64, a, e)]) → bget s 0 = j.toUInt64 → FL.length + 1 ≤ j →
    WReach X (d, s) (SqP X D p q d FL t a e n j) := by
  intro n
  induction n with
  | zero =>
    intro j d s a hj hjX _ hI hc _
    exact WReach.done ⟨[], j, Ws.nil, rfl, Nat.le_refl _, hjX, rfl, hc, fun _ c h => by simp at h, WI_fr _ hI rfl⟩
  | succ n ih =>
    intro j d s a hj hjX hn hI hc hl
    have hr : (t, (n + 1).toUInt64, a, e).2.1 ≠ 0 := by
      show (n + 1).toUInt64 ≠ 0
      intro h; have := congrArg UInt64.toNat h; rw [u_toNat _ hn] at this; simp at this
    refine (IH j hj hjX d s FL _ hI hc hr (by simp; omega)).bind ?_
    rintro ⟨d1, s1⟩ ⟨w, j1, hW, hj1, hj1X, rfl, hc1, hz, hI1⟩
    have hFe : FL.isEmpty = false := by cases FL with | nil => exact absurd rfl hFL | cons => rfl
    rw [hFe] at hW
    replace hI1 := WI_fr (t, n.toUInt64, vf t a w, e) hI1 (by
      show (t, (n + 1).toUInt64 - 1, vf t a w, e) = _
      rw [← uk1]; simp)
    refine (ih j1 d1 s1 (vf t a w) (by omega) hj1X (by omega) hI1 hc1 (by omega)).bind ?_
    rintro st ⟨ws, j', hWs, hlen, hj', hj'X, hd, hc', h9, hI2⟩
    refine WReach.done ⟨w :: ws, j', Ws.cons hW hWs, by simp [hlen], by omega, hj'X, hd, hc', fun h9' c hc => ?_, hI2⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · subst h9'
      exact Classical.byContradiction fun h => hz (by simp [zf, h, g_1])
    · exact h9 h9' c hc

theorem toNat_toUInt64 (u : UInt64) : u.toNat.toUInt64 = u := by simp [Nat.toUInt64]

theorem foldl_vf6 (ws : List UInt64) (a : UInt64) : ws.foldl (vf 6) a = ws.foldl (· + ·) a := by
  induction ws generalizing a with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl]; rw [ih]; rfl

theorem foldl_vf8 (ws : List UInt64) (a : UInt64) : ws.foldl (vf 8) a = ws.foldl (· + ·) a := by
  induction ws generalizing a with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl]; rw [ih]; rfl

theorem n_pair {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 6) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht, tk1 X i (by omega)]
  unfold gnode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 2)) (by simp at hl ⊢; omega) 6 (tg X (i + 1)) 0 0
  replace hI1 := WI_fr ((6 : UInt64), (tg X (i + 1)).toNat.toUInt64, (0 : UInt64), (0 : UInt64)) hI1 (by rw [toNat_toUInt64])
  refine (wseq IH 6 0 (by simp) (FL ++ [f]) (by simp) _ (i + 2) d _ 0 (by omega) (by omega) (UInt64.toNat_lt _) hI1
    (by rw [h0, cur_set hI, uk2]) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨ws, j', hWs, hlen, hj', hj'X, rfl, hc, -, hI2⟩
  exact fin_pop hI2 (by decide) hc (fun _ => by simpa [wf, foldl_vf6] using W.pair ht hWs hlen) (by omega) hj'X

theorem n_prim {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 9) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht, tk1 X i (by omega)]
  unfold gnode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 2)) (by simp at hl ⊢; omega) 9 (g33 (tg X (i + 1))) 0 0
  replace hI1 := WI_fr ((9 : UInt64), (g33 (tg X (i + 1))).toNat.toUInt64, (0 : UInt64), (0 : UInt64)) hI1
    (by rw [toNat_toUInt64])
  refine (wseq IH 9 0 (by simp) (FL ++ [f]) (by simp) _ (i + 2) d _ 0 (by omega) (by omega) (UInt64.toNat_lt _) hI1
    (by rw [h0, cur_set hI, uk2]) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨ws, j', hWs, hlen, hj', hj'X, rfl, hc, h1, hI2⟩
  exact fin_pop hI2 (by decide) hc (fun _ => W.prim ht hWs hlen (h1 rfl)) (by omega) hj'X

theorem nd_eq {D p q d s FL} (hI : WI D p q d s FL) : bsize d >>> 1 = D.length.toUInt64 := by
  have h1 := hI.dl; have h2 := hI.Dl
  apply UInt64.toNat.inj
  rw [UInt64.toNat_shiftRight, bsize_u, u_toNat _ (by omega), u_toNat _ (by omega), h1]
  simp; omega

theorem dget {D p q d s FL} (hI : WI D p q d s FL) (e : UInt64) (he : e.toNat < D.length) :
    bget d (2 * e) = (D.getD e.toNat (0, 0)).1 ∧ bget d (2 * e + 1) = (D.getD e.toNat (0, 0)).2 := by
  have h2 := hI.Dl
  have a1 : (2 * e).toNat = 2 * e.toNat := by simp [UInt64.toNat_mul]; omega
  have a2 : (2 * e + 1).toNat = 2 * e.toNat + 1 := by simp [UInt64.toNat_mul, UInt64.toNat_add]; omega
  rw [bget_eq_getD, bget_eq_getD, a1, a2]
  exact hI.dv _ he

theorem n_call {X D p q i} (hX : X.length < 2 ^ 31) (IH : ∀ j, i < j → NS X D p q j) (ht : tg X i = 8) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  have hi := tg_lt X i (by rw [ht]; decide)
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega), ht, tk1 X i (by omega), tk2 X i (by omega), nd_eq hI]
  unfold gnode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  by_cases he : ¬ tg X (i + 1) < D.length.toUInt64
  · rw [if_neg he]
    exact WReach.error (werr_of (err_g48 _ (by have := WI_len hI; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega))
  rw [Classical.not_not] at he
  rw [if_pos he]
  have he' : (tg X (i + 1)).toNat < D.length := by
    have := UInt64.lt_iff_toNat_lt.mp he; rw [u_toNat _ (by have := hI.Dl; omega)] at this; exact this
  obtain ⟨hI1, h0⟩ := WI_push (WI_cur hI (i.toUInt64 + 3)) (by simp at hl ⊢; omega) 8 (tg X (i + 2)) 0 (tg X (i + 1))
  replace hI1 := WI_fr ((8 : UInt64), (tg X (i + 2)).toNat.toUInt64, (0 : UInt64), tg X (i + 1)) hI1 (by rw [toNat_toUInt64])
  refine (wseq IH 8 (tg X (i + 1)) (by simp) (FL ++ [f]) (by simp) _ (i + 3) d _ 0 (by omega) (by omega) (UInt64.toNat_lt _) hI1
    (by rw [h0, cur_set hI, uk3]) (by simp at hl ⊢; omega)).bind ?_
  rintro ⟨d1, s1⟩ ⟨ws, j', hWs, hlen, hj', hj'X, rfl, hc, -, hI2⟩
  obtain ⟨u1, u2⟩ := dget hI (tg X (i + 1)) he'
  refine fin_pop hI2 (by decide) hc (fun hz => ?_) (by omega) hj'X
  rw [u1] at hz
  have hs : ws.foldl (· + ·) 0 = (D.getD (tg X (i + 1)).toNat (0, 0)).1 := by
    rw [← foldl_vf8]
    exact Classical.byContradiction fun h => hz (by unfold zp; rw [if_pos (by decide), if_neg (by simpa using h)]; rfl)
  simpa [wf, u2] using W.call ht he' hWs hlen hs

theorem n_bad {X D p q i} (hX : X.length < 2 ^ 31) (h1 : tg X i ≠ 1) (h2 : tg X i ≠ 2) (h3 : tg X i ≠ 3) (h4 : tg X i ≠ 4) (h5 : tg X i ≠ 5)
    (h6 : tg X i ≠ 6) (h8 : tg X i ≠ 8) (h9 : tg X i ≠ 9) (h10 : tg X i ≠ 10) (h11 : tg X i ≠ 11) : NS X D p q i := by
  intro hiX d s FL f hI hr0 hr hl
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega)]
  unfold gnode
  rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_neg (by simpa using h3), if_neg (by simpa using h4),
    if_neg (by simpa using h5), if_neg (by simpa using h6), if_neg (by simpa using h8), if_neg (by simpa using h9),
    if_neg (by simpa using h10), if_neg (by simpa using h11)]
  exact WReach.error (werr_of (err_g48 _ (by have := WI_len hI; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega))

/-- **every node**: from a frame wanting a child at cursor i, the pass errs or delivers the node's width (W) -/
theorem n_all {X D p q} (hX : X.length < 2 ^ 31) (i : Nat) : NS X D p q i := by
  by_cases hiX : i ≤ X.length + 3
  · have IH : ∀ j, i < j → NS X D p q j := fun j hj =>
      if hj' : j ≤ X.length + 3 then n_all hX j else fun h => absurd h hj'
    by_cases t1 : tg X i = 1; · exact n_const hX t1
    by_cases t2 : tg X i = 2; · exact n_local hX t2
    by_cases t3 : tg X i = 3; · exact n_bin hX IH t3
    by_cases t4 : tg X i = 4; · exact n_ite hX IH t4
    by_cases t5 : tg X i = 5; · exact n_let hX IH t5
    by_cases t6 : tg X i = 6; · exact n_pair hX IH t6
    by_cases t8 : tg X i = 8; · exact n_call hX IH t8
    by_cases t9 : tg X i = 9; · exact n_prim hX IH t9
    by_cases t10 : tg X i = 10; · exact n_loop hX IH t10
    by_cases t11 : tg X i = 11; · exact n_cont hX IH t11
    exact n_bad hX t1 t2 t3 t4 t5 t6 t8 t9 t10 t11
  · intro h; exact absurd h hiX
termination_by X.length + 3 - i
decreasing_by all_goals omega

/-! ## defs and the whole pass -/

/-- consecutive defs from cursor i: headers hs, each body (the root's child) of width nres, then ENDDEF -/
inductive WDefs (X : Buf) : List (UInt64 × UInt64) → Nat → List Nat → List (UInt64 × UInt64) → Nat → Prop
  | nil {D i} : WDefs X D i [] D i
  | cons {D i i1 hs D' i'} : tg X i = 20 →
      W X (D ++ [(tg X (i + 2), tg X (i + 5))]) (tg X (i + 2)) (tg X (i + 5)) true (i + 6) (tg X (i + 5)) i1 →
      tg X i1 = 21 → WDefs X (D ++ [(tg X (i + 2), tg X (i + 5))]) (i1 + 1) hs D' i' → WDefs X D i (i :: hs) D' i'

/-- g51 with no frames: a def header, the end, or an error -/
theorem g51_top (x : Buf) {D p q d s} (hI : WI D p q d s []) :
    g51 x d s = if bget s 0 < bsize x then
      (if bget x (bget s 0) == 20 then (bpush (bpush d (bget x (bget s 0 + 2))) (bget x (bget s 0 + 5)),
        g47 (bset (bset (bset s 0 (bget s 0 + 6)) 2 (bget x (bget s 0 + 2))) 3 (bget x (bget s 0 + 5))) 100 1 0 0)
       else (d, g48 s))
      else (d, bset s 5 1) := by
  have h4 : (bget s 4 == 0) = true := by rw [hI.r4]; rfl
  unfold g51
  extract_lets i c e h p' q' f' u v
  rw [if_pos h4]

/-- a new def: npw, nres registers, its (npw, nres) appended to d -/
theorem WI_def {D p q d s} (hI : WI D p q d s []) (a b : UInt64) (hD : D.length + 1 < 2 ^ 32) :
    WI (D ++ [(a, b)]) a b (bpush (bpush d a) b) (bset (bset s 2 a) 3 b) [] := by
  have hs8 := WI_len hI
  have hb : ∀ i : UInt64, i ≠ 2 → i ≠ 3 → bget (bset (bset s 2 a) 3 b) i = bget s i := fun i h2 h3 => by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => h3 (UInt64.toNat.inj e).symm), BufL.bget_bset,
      if_neg (fun ⟨e, _⟩ => h2 (UInt64.toNat.inj e).symm)]
  exact { dl := by simp [bpush, hI.dl]; omega
          dv := fun j hj => by
            have e : bpush (bpush d a) b = d ++ [a, b] := by simp [bpush]
            rw [e]
            simp only [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_or_ge j D.length with hjD | hjD
            · have := hI.dv j hjD
              simp only [List.getD_eq_getElem?_getD] at this ⊢
              have q1 : (d ++ [a, b])[2 * j]? = d[2 * j]? := List.getElem?_append_left (by rw [hI.dl]; omega)
              have q2 : (d ++ [a, b])[2 * j + 1]? = d[2 * j + 1]? := List.getElem?_append_left (by rw [hI.dl]; omega)
              have q3 : (D ++ [(a, b)])[j]? = D[j]? := List.getElem?_append_left hjD
              rw [q1, q2, q3]
              exact this
            · have : j = D.length := by omega
              subst this
              simp only [List.getD_eq_getElem?_getD]
              have q1 : (d ++ [a, b])[2 * D.length]? = [a, b][0]? := by
                rw [List.getElem?_append_right (by rw [hI.dl]; omega), hI.dl, Nat.sub_self]
              have q2 : (d ++ [a, b])[2 * D.length + 1]? = [a, b][1]? := by
                rw [List.getElem?_append_right (by rw [hI.dl]; omega), hI.dl]; simp
              have q3 : (D ++ [(a, b)])[D.length]? = some (a, b) := by simp
              rw [q1, q2, q3]
              simp
          e1 := by rw [hb 1 (by decide) (by decide)]; exact hI.e1
          r2 := by rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e), BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]
          r3 := by rw [BufL.bget_bset, if_pos ⟨rfl, by rw [BufL.length_bset]; simp; omega⟩]
          r4 := by rw [hb 4 (by decide) (by decide)]; exact hI.r4
          r5 := by rw [hb 5 (by decide) (by decide)]; exact hI.r5
          fs := ⟨by simp [bset]; omega, fun j hj => by simp at hj⟩
          sl := by simp [bset]; exact hI.sl
          Dl := by simp; omega }

def DP (X : Buf) (D : List (UInt64 × UInt64)) (d0 : Buf) (i : Nat) (st : WSt) : Prop :=
  ∃ i1, tg X i = 20 ∧ W X (D ++ [(tg X (i + 2), tg X (i + 5))]) (tg X (i + 2)) (tg X (i + 5)) true (i + 6) (tg X (i + 5)) i1 ∧
    tg X i1 = 21 ∧ i + 6 < i1 ∧ i1 < X.length ∧ st.1 = bpush (bpush d0 (tg X (i + 2))) (tg X (i + 5)) ∧
    bget st.2 0 = (i1 + 1).toUInt64 ∧ WI (D ++ [(tg X (i + 2), tg X (i + 5))]) (tg X (i + 2)) (tg X (i + 5)) st.1 st.2 []

theorem werr_g48 {D p q d s FL} (hI : WI D p q d s FL) (d' : Buf) : werr (d', g48 s) :=
  werr_of (err_g48 _ (by have := WI_len hI; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega)

/-- any node with an invalid tag (also past the AST): error -/
theorem n_err {X D p q i} (hi : i < 2 ^ 40) (h1 : tg X i ≠ 1) (h2 : tg X i ≠ 2) (h3 : tg X i ≠ 3) (h4 : tg X i ≠ 4)
    (h5 : tg X i ≠ 5) (h6 : tg X i ≠ 6) (h8 : tg X i ≠ 8) (h9 : tg X i ≠ 9) (h10 : tg X i ≠ 10) (h11 : tg X i ≠ 11)
    {d s FL f} (P : WSt → Prop) (hI : WI D p q d s (FL ++ [f])) (hr0 : bget s 0 = i.toUInt64) (hr : f.2.1 ≠ 0) :
    WReach X (d, s) P := by
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_node X hI hr, hr0, tg_u _ _ (by omega)]
  unfold gnode
  rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_neg (by simpa using h3), if_neg (by simpa using h4),
    if_neg (by simpa using h5), if_neg (by simpa using h6), if_neg (by simpa using h8), if_neg (by simpa using h9),
    if_neg (by simpa using h10), if_neg (by simpa using h11)]
  exact WReach.error (werr_g48 hI d)

/-- one def -/
theorem w_def {X D p q d s i} (hX : X.length < 2 ^ 31) (hI : WI D p q d s []) (hr0 : bget s 0 = i.toUInt64)
    (hi : i < X.length) (hD : D.length ≤ i) : WReach X (d, s) (DP X D d i) := by
  refine WReach.step (wlive_of hI) ?_
  unfold wst; dsimp only
  rw [g51_top X hI, hr0, if_pos (by rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega), u_toNat _ (by omega)]; exact hi),
    tg_u _ _ (by omega)]
  by_cases h20 : ¬ tg X i = 20
  · rw [if_neg (by simpa using h20)]
    exact WReach.error (werr_of (err_g48 _ (by have := WI_len hI; omega)) (by unfold g48; simp [bset]; have := WI_len hI; omega))
  rw [Classical.not_not] at h20
  rw [if_pos (by simp [h20]), tk2 X i (by omega), tk5 X i (by omega)]
  have hI0 := WI_def (WI_cur hI (i.toUInt64 + 6)) (tg X (i + 2)) (tg X (i + 5)) (by omega)
  have hc0 : bget (bset (bset (bset s 0 (i.toUInt64 + 6)) 2 (tg X (i + 2))) 3 (tg X (i + 5))) 0 = (i + 6).toUInt64 := by
    rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e), BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e),
      cur_set hI, uk6]
  obtain ⟨hI1, h0⟩ := WI_push hI0 (by simp) 100 1 0 0
  by_cases hfar : X.length + 3 < i + 6
  · have t0 : tg X (i + 6) = 0 := by
      simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : X.length ≤ i + 6)]
    exact n_err (i := i + 6) (by omega) (by simp [t0]) (by simp [t0]) (by simp [t0]) (by simp [t0]) (by simp [t0]) (by simp [t0])
      (by simp [t0]) (by simp [t0]) (by simp [t0]) (by simp [t0]) _ (FL := []) hI1 (by rw [h0, hc0]) (by decide)
  refine (n_all hX (i + 6) (by omega) _ _ [] _ hI1 (by rw [h0, hc0]) (by decide) (by simp)).bind ?_
  rintro ⟨d1, s1⟩ ⟨w, i1, hW, hi1, hi1X, rfl, hc1, -, hI2⟩
  replace hI2 := WI_fr ((100 : UInt64), (0 : UInt64), w, (0 : UInt64)) hI2 (by simp [vf])
  refine WReach.step (wlive_of hI2) ?_
  unfold wst; dsimp only
  rw [g51_pop X hI2, g50_root X hI2]
  obtain ⟨hI3, h3⟩ := WI_pop (FL := []) hI2
  by_cases hq : ¬ w = tg X (i + 5)
  · rw [if_neg (by simpa using hq)]
    exact WReach.error (werr_g48 hI3 _)
  rw [Classical.not_not] at hq
  subst hq
  rw [if_pos (by simp), hc1, tg_u _ _ (by omega)]
  by_cases h21 : ¬ tg X i1 = 21
  · rw [if_neg (by simpa using h21)]
    exact WReach.error (werr_g48 hI3 _)
  rw [Classical.not_not] at h21
  rw [if_pos (by simp [h21])]
  have hi1l := tg_lt X i1 (by rw [h21]; decide)
  exact WReach.done ⟨i1, h20, hW, h21, hi1, hi1l, rfl, by rw [cur_set hI3, uk1], WI_cur hI3 _⟩

def PD (X : Buf) (D : List (UInt64 × UInt64)) (i : Nat) (st : WSt) : Prop :=
  ∃ hs D' i', WDefs X D i hs D' i' ∧ X.length ≤ i' ∧ bget st.2 1 ≠ 1 ∧ bget st.2 5 = 1

/-- all defs, then the done flag -/
theorem w_prog {X} (hX : X.length < 2 ^ 31) : ∀ n D p q d s i, X.length - i ≤ n → WI D p q d s [] →
    bget s 0 = i.toUInt64 → D.length ≤ i → i < 2 ^ 32 → WReach X (d, s) (PD X D i) := by
  intro n
  induction n with
  | zero =>
    intro D p q d s i hn hI hr0 _ hi
    refine WReach.step (wlive_of hI) ?_
    unfold wst; dsimp only
    rw [g51_top X hI, hr0, if_neg (by rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega), u_toNat _ (by omega)]; omega)]
    have hs8 := WI_len hI
    exact WReach.done ⟨[], D, i, .nil, by omega,
      by rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e)]; exact hI.e1,
      by rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]⟩
  | succ n ih =>
    intro D p q d s i hn hI hr0 hD hi
    by_cases hiX : ¬ i < X.length
    · refine WReach.step (wlive_of hI) ?_
      unfold wst; dsimp only
      rw [g51_top X hI, hr0, if_neg (by rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by omega), u_toNat _ (by omega)]; omega)]
      have hs8 := WI_len hI
      exact WReach.done ⟨[], D, i, .nil, by omega,
        by rw [BufL.bget_bset, if_neg (fun ⟨e, _⟩ => by simp at e)]; exact hI.e1,
        by rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]⟩
    rw [Classical.not_not] at hiX
    refine (w_def hX hI hr0 hiX hD).bind ?_
    rintro ⟨d1, s1⟩ ⟨i1, h20, hW, h21, hi1, hi1l, hd1, hc1, hI1⟩
    refine (ih _ _ _ d1 s1 (i1 + 1) (by omega) hI1 hc1 (by simp; omega) (by omega)).bind ?_
    rintro st ⟨hs, D', i', hDs, hi', h1, h5⟩
    exact WReach.done ⟨i :: hs, D', i', .cons h20 hW h21 hDs, hi', h1, h5⟩

/-- **the width pass on success**: every def of the AST (from word 1) satisfies `W` with body width = nres -/
theorem g53_ok (x : Buf) (hX : x.length < 2 ^ 31) (h : (g53 x).2 ≠ 0) :
    ∃ hs D i', WDefs x [] 1 hs D i' ∧ x.length ≤ i' := by
  let s0 : Buf := bpush (bpush (bpush (bpush (bpush (bpush (bpush (bpush bnew 1) 0) 0) 0) 0) 0) 0) 0
  have hI : WI [] 0 0 bnew s0 [] := {
    dl := rfl
    dv := fun j hj => by simp at hj
    e1 := by decide
    r2 := rfl
    r3 := rfl
    r4 := rfl
    r5 := by decide
    fs := ⟨by decide, fun j hj => by simp at hj⟩
    sl := by decide
    Dl := by decide }
  have hR := w_prog hX x.length [] 0 0 bnew s0 1 (by omega) hI rfl (by simp) (by decide)
  unfold g53 at h
  -- Lean 4.34.1: hide the fuel from the kernel, which otherwise unfolds `g52 16777216` when re-checking `dsimp`
  revert h; generalize hN : (16777216 : Nat) = N; revert N; apply id; intro N hN h
  dsimp only at h
  generalize hg : g52 N (x, (bnew, s0)) = r at h
  obtain ⟨x1, d1, s1⟩ := r
  dsimp only at h
  have hok : bget (g52 N (x, (bnew, s0))).2.2 1 ≠ 1 := by
    rw [hg]; intro e; apply h; simp only at e; rw [if_pos (by simp [e])]; rfl
  obtain ⟨m, -, ⟨hs, D, i', hD, hi', -⟩, -⟩ := wreach_run hR N hok
  exact ⟨hs, D, i', hD, hi'⟩

end GenRef

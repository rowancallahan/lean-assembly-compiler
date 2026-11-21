/- Nano/Parser/NumP2: the `lw` machine `u28` computes `NumSpec.lw` (node by node, continuation style: `GL Q σ` says
every run from σ ends in an output satisfying Q; error outputs satisfy every Q considered). -/
import Nano.Parser.NumP1
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the body of `u28` after the checks (k, a, a2: the top task) -/
def L28 (n : Nat) (x d b : Buf) (bt : UInt64) (v : Buf) (vt : UInt64) (t : Buf) (tt c k a a2 : UInt64) :
    Buf × (Buf × (UInt64 × (UInt64 × UInt64))) :=
  let u := tt - 1;
  if k == 0 then
    (let (v1, z) := u29 x d b bt v vt t u c;
     let (vt1, z1) := z;
     let (t1, z2) := z1;
     let (tt1, z3) := z2;
     let (c1, ok) := z3;
     if ok == 1 then u28 n x d b bt v1 vt1 t1 tt1 c1 else (b, (v1, (vt1, (c1, 0)))))
  else if k == 1 then u28 n x d b bt (u20 v a (if a < vt then bget v a else 0)) (a + 1) t u c
  else if k == 2 then u28 n x d b bt (bset v a (bget v a &&& bget v (a + 1))) (a + 1) t u c
  else if k == 3 then u28 n x d b bt (bset v a (vt - a - 1)) vt t u c
  else if k == 4 then
    (let l := bget v a;
     let m := a + 1 + l;
     let e := vt - m;
     let q := (if l < e then l else e);
     let (v1, ok) := u24 16777216 v a m 0 q;
     if ok == 1 then u28 n x d b bt v1 (a + q) t u c else (b, (v1, (vt, (c, 0)))))
  else if k == 5 then
    (let (b1, z) := u26 b bt v a2 vt a;
     let (bt1, ok) := z;
     if ok == 1 then u28 n x d b1 bt1 v a2 t u c else (b1, (v, (vt, (c, 0)))))
  else if k == 6 then u28 n x d b a v vt t u c
  else if k == 7 then
    (if a == 0 then u28 n x d b bt v vt t u c
     else u28 n x d b bt v vt (u27 (bset t (3 * tt - 2) (a - 1)) tt 0 0 0) (tt + 1) c)
  else (b, (v, (vt, (c, 0))))

theorem u28_eq (n : Nat) (x d b : Buf) (bt : UInt64) (v : Buf) (vt : UInt64) (t : Buf) (tt c : UInt64)
    (h0 : (tt == 0) = false) (h1 : (u35 v t b == 0) = false) :
    u28 (n + 1) x d b bt v vt t tt c =
      L28 n x d b bt v vt t tt c (bget t (3 * tt - 3)) (bget t (3 * tt - 2)) (bget t (3 * tt - 1)) := by
  simp only [u28, h0, h1, Bool.false_eq_true, if_false]; rfl

abbrev LO := Buf × (Buf × (UInt64 × (UInt64 × UInt64)))
/-- Q holds for every error output -/
def QE (Q : LO → Prop) : Prop := ∀ r : LO, r.2.2.2.2 ≠ 1 → Q r

def GL (x d : Buf) (Q : LO → Prop) (b : Buf) (bt : UInt64) (v : Buf) (vt : UInt64) (t : Buf) (tt c : UInt64) : Prop :=
  ∀ n, Q (u28 n x d b bt v vt t tt c)

/-- the machine invariant: the chain, the value stack and the task stack are the prefixes of their buffers -/
structure LI (b : Buf) (bs : List (Nat × List Bool)) (v : Buf) (vs : List UInt64) (t : Buf) (ts : List T3) : Prop where
  pb : encB bs <+: b
  lb : b.length < 2 ^ 42
  pv : vs <+: v
  lv : v.length < 2 ^ 42
  pt : encT ts <+: t
  lt : t.length < 2 ^ 42
  sb : ∀ r ∈ bs, r.1 < 2 ^ 32

/-- the continuation: every state with these stacks and this cursor is good -/
def LP (x d : Buf) (Q : LO → Prop) (bs : List (Nat × List Bool)) (vs : List UInt64) (ts : List T3) (c : Nat) : Prop :=
  ∀ b v t, LI b bs v vs t ts → GL x d Q b (u (encB bs).length) v (u vs.length) t (u ts.length) (u c)

theorem u35_eq {v t b : Buf} (hv : v.length < 2 ^ 42) (ht : t.length < 2 ^ 42) (hb : b.length < 2 ^ 42) :
    (u35 v t b == 0) = !(decide (v.length < 2 ^ 40) && decide (t.length < 2 ^ 40) && decide (b.length < 2 ^ 40)) := by
  unfold u35
  have e : (1099511627776 : UInt64) = u (2 ^ 40) := rfl
  simp only [bsize_u, e, ult (show v.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega),
    ult (show t.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega),
    ult (show b.length < 2 ^ 64 by omega) (show 2 ^ 40 < 2 ^ 64 by omega)]
  by_cases h1 : v.length < 2 ^ 40 <;> by_cases h2 : t.length < 2 ^ 40 <;> by_cases h3 : b.length < 2 ^ 40 <;> simp [h1, h2, h3]

/-- one step from a state with a top task: the sizes are checked, then `L28` -/
theorem gl_top {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b : Buf} {bs : List (Nat × List Bool)} {v : Buf}
    {vs : List UInt64} {t : Buf} {ts : List T3} {k a a2 : UInt64} {c : UInt64}
    (hI : LI b bs v vs t (ts ++ [(k, a, a2)]))
    (H : v.length < 2 ^ 40 → t.length < 2 ^ 40 → b.length < 2 ^ 40 →
      ∀ n, Q (L28 n x d b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) c k a a2)) :
    GL x d Q b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) c := by
  intro n
  have htl := hI.pt.length_le
  simp only [encT_len, List.length_append, List.length_singleton] at htl
  have lt := hI.lt
  cases n with
  | zero => exact hQ _ (by simp [u28])
  | succ n =>
    have h0 : (u (ts.length + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have h35 := u35_eq hI.lv hI.lt hI.lb
    by_cases hs : v.length < 2 ^ 40 ∧ t.length < 2 ^ 40 ∧ b.length < 2 ^ 40
    · have h1 : (u35 v t b == 0) = false := by rw [h35]; simp [hs.1, hs.2.1, hs.2.2]
      rw [u28_eq n x d b _ v _ t _ c h0 h1]
      obtain ⟨r1, r2, r3⟩ := top_rd hI.pt (by omega)
      rw [r1, r2, r3]; exact H hs.1 hs.2.1 hs.2.2 n
    · have h1 : (u35 v t b == 0) = true := by
        rw [h35]; by_cases h1 : v.length < 2 ^ 40 <;> by_cases h2 : t.length < 2 ^ 40 <;> simp_all
      apply hQ; simp [u28, h0, h1]

theorem LI.lvs {b bs v vs t ts} (h : LI b bs v vs t ts) : vs.length < 2 ^ 42 := by
  have := h.pv.length_le; have := h.lv; omega
theorem LI.lts {b bs v vs t ts} (h : LI b bs v vs t ts) : ts.length < 2 ^ 41 := by
  have := h.pt.length_le; have := h.lt; rw [encT_len] at *; omega
theorem LI.lbs {b bs v vs t ts} (h : LI b bs v vs t ts) : (encB bs).length < 2 ^ 42 := by
  have := h.pb.length_le; have := h.lb; omega

/-- the task stack after popping: still a prefix -/
theorem LI.pop {b bs v vs t ts r} (h : LI b bs v vs t (ts ++ [r])) : encT ts <+: t :=
  (by rw [encT_snoc]; exact List.prefix_append _ _ : encT ts <+: encT (ts ++ [r])).trans h.pt

theorem prefix_of_app {W R v : Buf} (h : W ++ R <+: v) : W <+: v := (List.prefix_append W R).trans h

/-- FIRST s: the region from s becomes its first word -/
theorem l_first {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b bs v W R t ts a2 c}
    (hI : LI b bs v (W ++ R) t (ts ++ [(1, u W.length, a2)]))
    (hP : LP x d Q bs (W ++ [R.getD 0 0]) ts c) :
    GL x d Q b (u (encB bs).length) v (u (W ++ R).length) t (u (ts.length + 1)) (u c) := by
  apply gl_top hQ hI
  intro hv ht hb n
  have hl := hI.lvs
  simp only [List.length_append] at hl
  have hw : (if u W.length < u (W ++ R).length then bget v (u W.length) else 0) = R.getD 0 0 := by
    simp only [List.length_append, ult (show W.length < 2 ^ 64 by omega) (show W.length + R.length < 2 ^ 64 by omega)]
    by_cases hR : R = []
    · subst hR; simp
    · have : 0 < R.length := List.length_pos_iff.2 hR
      rw [if_pos (by omega), bget_pre hI.pv (by simp; omega) (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  simp only [L28, show ((1 : UInt64) == 0) = false from rfl, show ((1 : UInt64) == 1) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  rw [hw]
  have hp := u20_push (prefix_of_app hI.pv) (by have := hI.lv; omega) (R.getD 0 0)
  have e1 : u W.length + 1 = u (W ++ [R.getD 0 0]).length := by simp [u1, uadd]
  have hts := hI.lts; simp at hts
  have hvp := hI.pv.length_le; simp at hvp
  have e2 : u (ts.length + 1) - 1 = u ts.length := by rw [u1, usub (by omega) (by omega)]; rfl
  rw [e1, e2]
  exact hP _ _ _ ⟨hI.pb, hI.lb, hp.1, by have := hI.lv; omega, hI.pop, hI.lt, hI.sb⟩ n

theorem pop_e (ts : List T3) (h : ts.length + 1 < 2 ^ 64) : u (ts.length + 1) - 1 = u ts.length := by
  rw [u1, usub (by omega) h]; rfl

theorem prefix_of_getD {L b : Buf} (hl : L.length ≤ b.length) (h : ∀ i, i < L.length → b.getD i 0 = L.getD i 0) :
    L <+: b := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have := h i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem (show i < b.length by omega),
    Option.getD_some] at this
  simp [this]

theorem set_prefix {W R b : Buf} {z : UInt64} (h : W ++ z :: R <+: b) (y : UInt64) :
    W ++ y :: R <+: b.set W.length y := by
  obtain ⟨r, rfl⟩ := h
  rw [List.append_assoc, List.cons_append, set_mid]
  exact ⟨r, by simp⟩

/-- AND s -/
theorem l_and {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b bs v W t ts a2 c} {p q : UInt64}
    (hI : LI b bs v (W ++ [p, q]) t (ts ++ [(2, u W.length, a2)]))
    (hP : LP x d Q bs (W ++ [p &&& q]) ts c) :
    GL x d Q b (u (encB bs).length) v (u (W ++ [p, q]).length) t (u (ts.length + 1)) (u c) := by
  apply gl_top hQ hI
  intro hv ht hb n
  have hvp := hI.pv.length_le; simp at hvp
  have hts := hI.lts; simp at hts
  simp only [L28, show ((2 : UInt64) == 0) = false from rfl, show ((2 : UInt64) == 1) = false from rfl,
    show ((2 : UInt64) == 2) = true from rfl, Bool.false_eq_true, if_false, if_true]
  have r1 : bget v (u W.length) = p := by
    rw [bget_pre hI.pv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have r2 : bget v (u W.length + 1) = q := by
    rw [u1, uadd, bget_pre hI.pv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rw [r1, r2, bset_u v (by omega), pop_e ts (by omega)]
  have e1 : u W.length + 1 = u (W ++ [p &&& q]).length := by simp [u1, uadd]
  rw [e1]
  refine hP _ _ _ ⟨hI.pb, hI.lb, ?_, by simp; omega, hI.pop, hI.lt, hI.sb⟩ n
  have := set_prefix (W := W) (R := [q]) (z := p) (by simpa using hI.pv) (p &&& q)
  exact (List.prefix_append _ [q]).trans (by simpa using this)

/-- LEN s: the word at s := the size of the region above it -/
theorem l_len {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b bs v W R t ts a2 c} {z : UInt64}
    (hI : LI b bs v (W ++ z :: R) t (ts ++ [(3, u W.length, a2)]))
    (hP : LP x d Q bs (W ++ u R.length :: R) ts c) :
    GL x d Q b (u (encB bs).length) v (u (W ++ z :: R).length) t (u (ts.length + 1)) (u c) := by
  apply gl_top hQ hI
  intro hv ht hb n
  have hvp := hI.pv.length_le; simp at hvp
  have hts := hI.lts; simp at hts
  simp only [L28, show ((3 : UInt64) == 0) = false from rfl, show ((3 : UInt64) == 1) = false from rfl,
    show ((3 : UInt64) == 2) = false from rfl, show ((3 : UInt64) == 3) = true from rfl, Bool.false_eq_true, if_false, if_true]
  have e : u (W ++ z :: R).length - u W.length - 1 = u R.length := by
    simp only [List.length_append, List.length_cons]
    rw [usub (by omega) (by omega), u1, usub (by omega) (by omega)]; congr 1; omega
  rw [e, bset_u v (by omega), pop_e ts (by omega)]
  have e2 : (W ++ z :: R).length = (W ++ u R.length :: R).length := by simp
  rw [e2]
  exact hP _ _ _ ⟨hI.pb, hI.lb, set_prefix hI.pv _, by simp; omega, hI.pop, hI.lt, hI.sb⟩ n

theorem getD_app_lt {L R : Buf} {i : Nat} (h : i < L.length) : (L ++ R).getD i 0 = L.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge {L R : Buf} {i : Nat} (h : L.length ≤ i) : (L ++ R).getD i 0 = R.getD (i - L.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- ZIP s: the regions [s+1, m) and [m, top) (the word at s is the first one's size) become their zip -/
theorem l_zip {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b bs v W A B t ts a2 c}
    (hI : LI b bs v (W ++ u A.length :: (A ++ B)) t (ts ++ [(4, u W.length, a2)]))
    (hP : LP x d Q bs (W ++ List.zipWith (· &&& ·) A B) ts c) :
    GL x d Q b (u (encB bs).length) v (u (W ++ u A.length :: (A ++ B)).length) t (u (ts.length + 1)) (u c) := by
  apply gl_top hQ hI
  intro hv ht hb n
  have hvp := hI.pv.length_le; simp at hvp
  have hts := hI.lts; simp at hts
  simp only [L28, show ((4 : UInt64) == 0) = false from rfl, show ((4 : UInt64) == 1) = false from rfl,
    show ((4 : UInt64) == 2) = false from rfl, show ((4 : UInt64) == 3) = false from rfl,
    show ((4 : UInt64) == 4) = true from rfl, Bool.false_eq_true, if_false, if_true]
  have r1 : bget v (u W.length) = u A.length := by
    rw [bget_pre hI.pv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have em : u W.length + 1 + u A.length = u (W.length + 1 + A.length) := by rw [u1, uadd, uadd]
  have ee : u (W ++ u A.length :: (A ++ B)).length - u (W.length + 1 + A.length) = u B.length := by
    simp only [List.length_append, List.length_cons]; rw [usub (by omega) (by omega)]; congr 1; omega
  have eq : (if u A.length < u B.length then u A.length else u B.length) = u (min A.length B.length) := by
    simp only [ult (show A.length < 2 ^ 64 by omega) (show B.length < 2 ^ 64 by omega)]; split <;> (congr 1; omega)
  rw [r1, em, ee, eq, u0]
  have hz := u24_ok v W.length (W.length + 1 + A.length) (min A.length B.length) (by omega) (by omega) (by omega)
    16777216 0 v rfl (by omega) (by intro q; rw [if_neg (by omega)])
  generalize u24 16777216 v _ _ _ _ = R at hz ⊢
  obtain ⟨v1, ok⟩ := R
  simp only at hz ⊢
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨hl1, hg⟩ := hz rfl
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    rw [pop_e ts (by omega), uadd]
    have e3 : W.length + min A.length B.length = (W ++ List.zipWith (· &&& ·) A B).length := by simp
    rw [e3]
    refine hP _ _ _ ⟨hI.pb, hI.lb, ?_, by omega, hI.pop, hI.lt, hI.sb⟩ n
    apply prefix_of_getD (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_zipWith] at hi
    rw [hg i]
    by_cases hiW : i < W.length
    · rw [if_neg (by omega), prefix_getD hI.pv (by simp; omega), getD_app_lt hiW, getD_app_lt hiW]
    · rw [if_pos (by omega), getD_app_ge (by omega), prefix_getD hI.pv (by simp; omega),
        prefix_getD hI.pv (by simp; omega), getD_app_ge (by omega), getD_app_ge (by omega)]
      simp only [show i + 1 - W.length = (i - W.length) + 1 by omega,
        show W.length + 1 + A.length + (i - W.length) - W.length = (A.length + (i - W.length)) + 1 by omega,
        List.getD_cons_succ]
      rw [getD_app_lt (by omega), getD_app_ge (by omega), show A.length + (i - W.length) - A.length = i - W.length by omega]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
      rw [List.getElem?_eq_getElem (show i - W.length < A.length by omega),
        List.getElem?_eq_getElem (show i - W.length < B.length by omega)]
      rfl
  · simp only [show (ok == 1) = false by simpa using hok, Bool.false_eq_true, if_false]
    exact hQ _ (show u 0 ≠ 1 by decide)

end NumP

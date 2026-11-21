/- Nano/Parser/NumP1: the binding chain (environment) and the small loops of the `lw` machine. -/
import Nano.Parser.NumP0
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

def w2 (b : Bool) : UInt64 := if b then 1 else 0

theorem w2_lt (b : Bool) : w2 b = u (if b then 1 else 0) := by cases b <;> rfl

/-- a binding record: the flags, the slot, the count -/
def encR (r : Nat × List Bool) : List UInt64 := r.2.map w2 ++ [u r.1, u r.2.length]
def encB (bs : List (Nat × List Bool)) : List UInt64 := bs.flatMap encR

/-- the environment of a chain (outermost first) -/
def envOf (bs : List (Nat × List Bool)) : List Bool := bs.foldl (fun env r => NumSpec.setW env r.1 r.2) []

def lookf (q : Nat) (o : Option Bool) (r : Nat × List Bool) : Option Bool :=
  if r.1 ≤ q ∧ q < r.1 + r.2.length then some (r.2.getD (q - r.1) false) else o

/-- the innermost binding of slot q -/
def look (bs : List (Nat × List Bool)) (q : Nat) : Option Bool := bs.foldl (lookf q) none

def lookW (bs : List (Nat × List Bool)) (q : Nat) : UInt64 :=
  match look bs q with | none => 2 | some v => w2 v

theorem getD_lt {α} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
theorem getD_ge {α} {l : List α} {i : Nat} (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem setW_getD (env : List Bool) (s : Nat) (ws : List Bool) (q : Nat) :
    (NumSpec.setW env s ws).getD q false =
      if s ≤ q ∧ q < s + ws.length then ws.getD (q - s) false else env.getD q false := by
  unfold NumSpec.setW
  by_cases hq : q < max env.length (s + ws.length)
  · rw [getD_lt _ (by simpa using hq)]; simp
  · rw [getD_ge _ (by simp; omega)]
    rw [getD_ge _ (show env.length ≤ q by omega)]
    split <;> first | rfl | omega
theorem foldl_lookf (q : Nat) : ∀ (bs : List (Nat × List Bool)) (o : Option Bool),
    bs.foldl (lookf q) o = match bs.foldl (lookf q) none with | some v => some v | none => o
  | [], o => by simp
  | r :: bs, o => by
    simp only [List.foldl_cons]
    rw [foldl_lookf q bs (lookf q o r), foldl_lookf q bs (lookf q none r)]
    cases bs.foldl (lookf q) none <;> simp only
    unfold lookf; by_cases hc : r.1 ≤ q ∧ q < r.1 + r.2.length <;> simp [hc]
theorem env_look (bs : List (Nat × List Bool)) (q : Nat) : (envOf bs).getD q false = (look bs q).getD false := by
  suffices ∀ env, (bs.foldl (fun env r => NumSpec.setW env r.1 r.2) env).getD q false =
      (bs.foldl (lookf q) none).getD (env.getD q false) by
    have := this []; simpa [envOf, look] using this
  induction bs with
  | nil => intro env; simp
  | cons r bs ih =>
    intro env
    simp only [List.foldl_cons]
    rw [ih, foldl_lookf q bs (lookf q none r), setW_getD]
    cases bs.foldl (lookf q) none <;> simp only [Option.getD_some]
    unfold lookf; by_cases hc : r.1 ≤ q ∧ q < r.1 + r.2.length <;> simp [hc]

theorem look_snoc (bs : List (Nat × List Bool)) (r : Nat × List Bool) (q : Nat) :
    look (bs ++ [r]) q = if r.1 ≤ q ∧ q < r.1 + r.2.length then some (r.2.getD (q - r.1) false) else look bs q := by
  simp [look, List.foldl_append, lookf]

theorem envOf_snoc (bs : List (Nat × List Bool)) (r : Nat × List Bool) :
    envOf (bs ++ [r]) = NumSpec.setW (envOf bs) r.1 r.2 := by simp [envOf, List.foldl_append]

theorem encB_snoc (bs : List (Nat × List Bool)) (r : Nat × List Bool) : encB (bs ++ [r]) = encB bs ++ encR r := by
  simp [encB]

theorem encR_len (r : Nat × List Bool) : (encR r).length = r.2.length + 2 := by simp [encR]

/-! ## arithmetic on words that hold naturals -/
theorem ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (u a < u b) = (a < b) := u_lt' ha hb
theorem ueq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (u a == u b) = decide (a = b) := u_beq ha hb
theorem usub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) : u a - u b = u (a - b) := u_sub h ha
theorem uadd (a b : Nat) : u a + u b = u (a + b) := u_add a b
theorem u0 : (0 : UInt64) = u 0 := rfl
theorem u1 : (1 : UInt64) = u 1 := rfl
theorem u2 : (2 : UInt64) = u 2 := rfl
theorem u3 : (3 : UInt64) = u 3 := rfl

/-! ## `u18`: lookup in the chain -/
theorem u18_succ (n : Nat) (b : Buf) (t q : UInt64) : u18 (n + 1) b t q =
    if t == 0 then 2
    else if t < 2 then 3
    else
      let m := bget b (t - 1);
      let s := bget b (t - 2);
      if t - 2 < m then 3
      else if q < s then u18 n b (t - 2 - m) q
      else if q - s < m then bget b (t - 2 - m + (q - s))
      else u18 n b (t - 2 - m) q := rfl

theorem w2_getD (ws : List Bool) (k : Nat) (hk : k < ws.length) : (ws.map w2).getD k 0 = w2 (ws.getD k false) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_app_right (l1 l2 : Buf) (k : Nat) : (l1 ++ l2).getD (l1.length + k) 0 = l2.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem encR_slot (r : Nat × List Bool) : (encR r).getD r.2.length 0 = u r.1 := by
  simp [encR, List.getD_eq_getElem?_getD, List.getElem?_append_right]
theorem encR_cnt (r : Nat × List Bool) : (encR r).getD (r.2.length + 1) 0 = u r.2.length := by
  simp [encR, List.getD_eq_getElem?_getD, List.getElem?_append_right]
theorem encR_flag (r : Nat × List Bool) {k : Nat} (hk : k < r.2.length) : (encR r).getD k 0 = w2 (r.2.getD k false) := by
  simp [encR, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < (r.2.map w2).length by simpa using hk), hk]

theorem w2_ne3 (v : Bool) : w2 v ≠ 3 := by cases v <;> decide

theorem u18_ok : ∀ (n : Nat) (bs : List (Nat × List Bool)) (b : Buf) (q : Nat), encB bs <+: b → b.length < 2 ^ 64 →
    q < 2 ^ 64 → (∀ r ∈ bs, r.1 < 2 ^ 64) →
    u18 n b (u (encB bs).length) (u q) = 3 ∨ u18 n b (u (encB bs).length) (u q) = lookW bs q
  | 0, _, _, _, _, _, _, _ => Or.inl rfl
  | n + 1, bs, b, q, hp, hb, hq, hs => by
    rcases List.eq_nil_or_concat bs with h0 | ⟨bs0, r, h0⟩
    all_goals try rw [List.concat_eq_append] at h0
    all_goals subst h0
    · right; rw [u18_succ]; simp [encB, lookW, look, show u 0 = 0 from rfl]
    · have hl := hp.length_le
      rw [encB_snoc] at hp hl ⊢
      have hr := hs r (by simp)
      have hs0 : ∀ r ∈ bs0, r.1 < 2 ^ 64 := fun r h => hs r (by simp [h])
      have hp0 : encB bs0 <+: b := (List.prefix_append _ _).trans hp
      have ih := u18_ok n bs0 b q hp0 hb hq hs0
      simp only [List.length_append, encR_len] at hl ⊢
      have rdk : ∀ k, k < r.2.length + 2 → bget b (u ((encB bs0).length + k)) = (encR r).getD k 0 := by
        intro k hk
        rw [bget_pre hp (by simp [encR_len]; omega) (by omega), getD_app_right]
      generalize hA : (encB bs0).length = A at rdk ih hl
      generalize hm : r.2.length = m at rdk hl
      have rd1 : bget b (u (A + (m + 2)) - 1) = u m := by
        rw [u1, usub (by omega) (by omega), show A + (m + 2) - 1 = A + (m + 1) by omega, rdk _ (by omega), ← hm, encR_cnt]
      have rd2 : bget b (u (A + (m + 2)) - 2) = u r.1 := by
        rw [u2, usub (by omega) (by omega), show A + (m + 2) - 2 = A + m by omega, rdk _ (by omega), ← hm, encR_slot]
      have h_t0 : (u (A + (m + 2)) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
      have h_t2 : (u (A + (m + 2)) < 2) = False := by
        rw [u2, ult (by omega) (by omega)]; exact propext ⟨fun h => by omega, False.elim⟩
      have h_sub2 : u (A + (m + 2)) - 2 = u (A + m) := by
        rw [u2, usub (show 2 ≤ A + (m + 2) by omega) (show A + (m + 2) < 2 ^ 64 by omega)]; congr 1
      have h_c : (u (A + m) < u m) = False := by
        rw [ult (by omega) (by omega)]; exact propext ⟨fun h => by omega, False.elim⟩
      have h_sm : u (A + m) - u m = u A := by rw [usub (by omega) (by omega)]; congr 1; omega
      rw [u18_succ]
      simp only [h_t0, h_t2, rd1, rd2, Bool.false_eq_true, if_false]
      rw [h_sub2]
      simp only [h_c, if_false, h_sm, ult hq hr]
      have hlk : lookW (bs0 ++ [r]) q = if r.1 ≤ q ∧ q < r.1 + m then w2 (r.2.getD (q - r.1) false) else lookW bs0 q := by
        unfold lookW; rw [look_snoc, hm]; by_cases hc : r.1 ≤ q ∧ q < r.1 + m <;> simp [hc]
      rw [hlk]
      by_cases h1 : q < r.1
      · simp only [h1, if_true, show ¬ (r.1 ≤ q ∧ q < r.1 + m) by omega, if_false]; exact ih
      · simp only [h1, if_false]
        simp only [usub (show r.1 ≤ q by omega) hq, ult (show q - r.1 < 2 ^ 64 by omega) (show m < 2 ^ 64 by omega)]
        by_cases h2 : q - r.1 < m
        · simp only [h2, if_true, show r.1 ≤ q ∧ q < r.1 + m by omega]
          right
          rw [uadd, rdk _ (by omega), encR_flag r (by omega)]; simp
        · simp only [h2, if_false, show ¬ (r.1 ≤ q ∧ q < r.1 + m) by omega]; exact ih

/-! ## pushing words -/
theorem u20_push {vs v : Buf} (h : vs <+: v) (hl : v.length < 2 ^ 63) (w : UInt64) :
    vs ++ [w] <+: u20 v (u vs.length) w ∧ (u20 v (u vs.length) w).length ≤ max v.length (vs.length + 1) := by
  have := h.length_le
  rw [u20_eq v (by omega) (by omega)]
  exact ⟨wr_prefix h w, wr_len_le _ _ _⟩

theorem range_succ_shift (g : Nat → UInt64) (s k : Nat) :
    g s :: (List.range k).map (fun i => g (s + 1 + i)) = (List.range (k + 1)).map (fun i => g (s + i)) := by
  rw [List.range_succ_eq_map]; simp [Function.comp_def]; intro i _; congr 1; omega

theorem lookW_w2 (bs : List (Nat × List Bool)) (q : Nat) (h : lookW bs q ≠ 3) :
    (if lookW bs q == 1 then (1 : UInt64) else 0) = w2 ((envOf bs).getD q false) := by
  rw [env_look]; unfold lookW at *
  cases look bs q with
  | none => rfl
  | some v => cases v <;> rfl

/-- `u22`: the env words of k slots -/
theorem u22_ok {bs : List (Nat × List Bool)} {b : Buf} (hb : encB bs <+: b) (hbl : b.length < 2 ^ 64)
    (hs : ∀ r ∈ bs, r.1 < 2 ^ 64) : ∀ (n k : Nat) (vs v : Buf) (s : Nat), vs <+: v → v.length < 2 ^ 62 →
    s + k < 2 ^ 62 → vs.length + k < 2 ^ 62 →
    (u22 n b (u (encB bs).length) v (u vs.length) (u s) (u k)).2.2 = 1 →
    vs ++ (List.range k).map (fun i => w2 ((envOf bs).getD (s + i) false)) <+: (u22 n b (u (encB bs).length) v (u vs.length) (u s) (u k)).1 ∧
    (u22 n b (u (encB bs).length) v (u vs.length) (u s) (u k)).2.1 = u (vs.length + k) ∧
    (u22 n b (u (encB bs).length) v (u vs.length) (u s) (u k)).1.length ≤ max v.length (vs.length + k)
  | 0, _, _, _, _, _, _, _, _, h => by simp [u22] at h
  | n + 1, 0, vs, v, s, hv, _, _, _, _ => by simp [u22, show u 0 = 0 from rfl, hv]; omega
  | n + 1, k + 1, vs, v, s, hv, hvl, hsk, hk, h => by
    have hk0 : (u (k + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have hl := u18_ok 16777216 bs b s hb hbl (by omega) hs
    have hvl' := hv.length_le
    simp only [u22, hk0, Bool.false_eq_true, if_false] at h ⊢
    rcases hl with h3 | hw
    · simp [h3] at h
    · rw [hw] at h ⊢
      have hn3 : lookW bs s ≠ 3 := by intro e; rw [e] at h; simp at h
      have hn3' : (lookW bs s == 3) = false := by simp [hn3]
      simp only [hn3', Bool.false_eq_true, if_false] at h ⊢
      rw [lookW_w2 bs s hn3] at h ⊢
      obtain ⟨hp1, hl1⟩ := u20_push hv (by omega) (w2 ((envOf bs).getD s false))
      have e1 : u vs.length + 1 = u (vs ++ [w2 ((envOf bs).getD s false)]).length := by simp [u1, uadd]
      have e2 : u s + 1 = u (s + 1) := by rw [u1, uadd]
      have e3 : u (k + 1) - 1 = u k := by rw [u1, usub (by omega) (by omega)]; rfl
      rw [e1, e2, e3] at h ⊢
      have ih := u22_ok hb hbl hs n k _ _ (s + 1) hp1 (by omega) (by omega) (by simp; omega) h
      generalize u22 n b _ _ _ _ _ = R at h ih ⊢
      obtain ⟨i1, i2, i3⟩ := ih
      simp only [List.length_append, List.length_singleton] at i2 i3
      refine ⟨?_, by rw [i2]; congr 1; omega, by omega⟩
      have := i1
      rw [List.append_assoc, List.singleton_append, range_succ_shift (fun i => w2 ((envOf bs).getD i false)) s k] at this
      exact this

/-- `u23`: k zero words -/
theorem u23_ok : ∀ (n k : Nat) (vs v : Buf), vs <+: v → v.length < 2 ^ 62 → vs.length + k < 2 ^ 62 →
    (u23 n v (u vs.length) (u k)).2.2 = 1 →
    vs ++ List.replicate k 0 <+: (u23 n v (u vs.length) (u k)).1 ∧ (u23 n v (u vs.length) (u k)).2.1 = u (vs.length + k) ∧
    (u23 n v (u vs.length) (u k)).1.length ≤ max v.length (vs.length + k)
  | 0, _, _, _, _, _, _, h => by simp [u23] at h
  | n + 1, 0, vs, v, hv, _, _, _ => by simp [u23, show u 0 = 0 from rfl, hv]; omega
  | n + 1, k + 1, vs, v, hv, hvl, hk, h => by
    have hk0 : (u (k + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    have hvl' := hv.length_le
    simp only [u23, hk0, Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨hp1, hl1⟩ := u20_push hv (by omega) 0
    have e1 : u vs.length + 1 = u (vs ++ [(0 : UInt64)]).length := by simp [u1, uadd]
    have e3 : u (k + 1) - 1 = u k := by rw [u1, usub (by omega) (by omega)]; rfl
    rw [e1, e3] at h ⊢
    have ih := u23_ok n k _ _ hp1 (by omega) (by simp; omega) h
    generalize u23 n _ _ _ = R at h ih ⊢
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.length_append, List.length_singleton] at i2 i3
    refine ⟨?_, by rw [i2]; congr 1; omega, by omega⟩
    rw [List.append_assoc, List.singleton_append, ← List.replicate_succ] at i1; exact i1

/-- `u24`: the zip loop, as a function of the word index -/
theorem u24_ok (v0 : Buf) (s m k : Nat) (hsm : s + 1 ≤ m) (hk : m + k ≤ v0.length) (hl : v0.length < 2 ^ 62) :
    ∀ (n j : Nat) (v : Buf), v.length = v0.length → j ≤ k →
    (∀ q, v.getD q 0 = if s ≤ q ∧ q < s + j then v0.getD (q + 1) 0 &&& v0.getD (m + (q - s)) 0 else v0.getD q 0) →
    (u24 n v (u s) (u m) (u j) (u k)).2 = 1 →
    (u24 n v (u s) (u m) (u j) (u k)).1.length = v0.length ∧
    ∀ q, (u24 n v (u s) (u m) (u j) (u k)).1.getD q 0 =
      if s ≤ q ∧ q < s + k then v0.getD (q + 1) 0 &&& v0.getD (m + (q - s)) 0 else v0.getD q 0
  | 0, _, _, _, _, _, h => by simp [u24] at h
  | n + 1, j, v, hvl, hj, hv, h => by
    simp only [u24] at h ⊢
    by_cases hjk : j < k
    · have c1 : (u j < u k) = True := by rw [ult (by omega) (by omega)]; simp [hjk]
      simp only [c1, if_true] at h ⊢
      have r1 : bget v (u s + 1 + u j) = v0.getD (s + 1 + j) 0 := by
        rw [u1, uadd, uadd, bget_u v (by omega), hv]; simp; omega
      have r2 : bget v (u m + u j) = v0.getD (m + j) 0 := by
        rw [uadd, bget_u v (by omega), hv]; simp; omega
      rw [r1, r2, uadd, bset_u v (by omega)] at h ⊢
      rw [u1, uadd] at h ⊢
      have ih := u24_ok v0 s m k hsm hk hl n (j + 1) _ (by simp [hvl]) (by omega) (by
        intro q
        rw [getD_set, hv]
        by_cases hq : s + j = q
        · subst hq; simp [hvl, show s + j < v0.length by omega, show s + j + 1 = s + 1 + j by omega]
        · simp only [hq, false_and, if_false]
          by_cases h2 : s ≤ q ∧ q < s + j
          · simp [h2, show q < s + (j + 1) by omega]
          · rw [if_neg h2, if_neg (by omega)]) h
      exact ih
    · have hjk' : j = k := by omega
      subst hjk'
      have c1 : (u j < u j) = False := by rw [ult (by omega) (by omega)]; simp
      simp only [c1, if_false]
      exact ⟨hvl, hv⟩

/-- `u25`: copy a list of words to a stack -/
theorem u25_ok : ∀ (n : Nat) (L W B b v : Buf), W ++ L <+: v → B <+: b → b.length < 2 ^ 62 →
    B.length + L.length < 2 ^ 62 → W.length + L.length < 2 ^ 62 →
    (u25 n b (u B.length) v (u W.length) (u (W.length + L.length))).2.2 = 1 →
    B ++ L <+: (u25 n b (u B.length) v (u W.length) (u (W.length + L.length))).1 ∧
    (u25 n b (u B.length) v (u W.length) (u (W.length + L.length))).2.1 = u (B.length + L.length) ∧
    (u25 n b (u B.length) v (u W.length) (u (W.length + L.length))).1.length ≤ max b.length (B.length + L.length)
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [u25] at h
  | n + 1, [], W, B, b, v, _, hB, _, _, _, _ => by
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by omega) (by omega)]; simp
    simp [u25, this, hB]; omega
  | n + 1, w :: L, W, B, b, v, hv, hB, hbl, h1, h2, h => by
    simp only [List.length_cons] at h1 h2
    have hBl := hB.length_le
    have c1 : (u W.length < u (W.length + (w :: L).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    simp only [u25, c1, if_true] at h ⊢
    have rw1 : bget v (u W.length) = w := by
      rw [bget_pre hv (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD]
    rw [rw1] at h ⊢
    obtain ⟨hp1, hl1⟩ := u20_push hB (by omega) w
    have e1 : u B.length + 1 = u (B ++ [w]).length := by simp [u1, uadd]
    have e2 : u W.length + 1 = u (W ++ [w]).length := by simp [u1, uadd]
    have e3 : u (W.length + (w :: L).length) = u ((W ++ [w]).length + L.length) := by
      simp only [List.length_cons, List.length_append, List.length_nil]; congr 1; omega
    rw [e1, e2, e3] at h ⊢
    have ih := u25_ok n L (W ++ [w]) (B ++ [w]) _ v (by simpa using hv) hp1 (by omega) (by simp; omega) (by simp; omega) h
    generalize u25 n _ _ _ _ _ = R at h ih ⊢
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.length_append, List.length_cons, List.length_nil] at i2 i3 hl1 ⊢
    refine ⟨by simpa using i1, by rw [i2]; congr 1; omega, by omega⟩

/-- `u26`: push a binding record -/
theorem u26_ok {L W B b v : Buf} (hv : W ++ L <+: v) (hB : B <+: b) (hbl : b.length < 2 ^ 61)
    (h1 : B.length + L.length < 2 ^ 61) (h2 : W.length + L.length < 2 ^ 62) (s : UInt64)
    (h : (u26 b (u B.length) v (u W.length) (u (W.length + L.length)) s).2.2 = 1) :
    B ++ L ++ [s, u L.length] <+: (u26 b (u B.length) v (u W.length) (u (W.length + L.length)) s).1 ∧
    (u26 b (u B.length) v (u W.length) (u (W.length + L.length)) s).2.1 = u (B.length + L.length + 2) ∧
    (u26 b (u B.length) v (u W.length) (u (W.length + L.length)) s).1.length ≤ max b.length (B.length + L.length + 2) := by
  unfold u26 at h ⊢
  have hc := u25_ok 16777216 L W B b v hv hB (by omega) (by omega) h2
  generalize u25 16777216 b _ v _ _ = R at h hc ⊢
  obtain ⟨R1, R2, ok⟩ := R
  simp only at h hc ⊢
  obtain ⟨i1, i2, i3⟩ := hc h
  subst i2
  obtain ⟨p1, l1⟩ := u20_push i1 (by omega) s
  simp only [List.length_append] at p1 l1
  have e1 : u (B.length + L.length) + 1 = u (B.length + L.length + 1) := by rw [u1, uadd]
  have ps := u20_push p1 (by simp; omega) (u L.length)
  simp only [List.length_append, List.length_singleton] at ps
  have e2 : u (W.length + L.length) - u W.length = u L.length := by rw [usub (by omega) (by omega)]; congr 1; omega
  rw [e1, e2]
  refine ⟨by simpa using ps.1, by rw [u2, uadd], by have := ps.2; omega⟩

/-! ## the task stack: records of three words -/
abbrev T3 := UInt64 × UInt64 × UInt64
def encT (ts : List T3) : List UInt64 := ts.flatMap fun r => [r.1, r.2.1, r.2.2]

theorem encT_len (ts : List T3) : (encT ts).length = 3 * ts.length := by
  induction ts with
  | nil => rfl
  | cons r ts ih => simp [encT] at *; omega

theorem encT_snoc (ts : List T3) (r : T3) : encT (ts ++ [r]) = encT ts ++ [r.1, r.2.1, r.2.2] := by simp [encT]

theorem u27_ok {ts : List T3} {t : Buf} (ht : encT ts <+: t) (htl : t.length < 2 ^ 61) (hl : ts.length < 2 ^ 59)
    (k a c : UInt64) : encT (ts ++ [(k, a, c)]) <+: u27 t (u ts.length) k a c ∧
      (u27 t (u ts.length) k a c).length ≤ max t.length (3 * ts.length + 3) := by
  unfold u27
  have h3 : (3 : UInt64) * u ts.length = u (encT ts).length := by rw [encT_len, u3, u_mul]
  rw [h3]
  obtain ⟨p1, l1⟩ := u20_push ht (by omega) k
  have e1 : u (encT ts).length + 1 = u (encT ts ++ [k]).length := by simp [u1, uadd]
  rw [e1]
  obtain ⟨p2, l2⟩ := u20_push p1 (by simp [encT_len] at l1 ⊢; omega) a
  have e2 : u (encT ts).length + 2 = u (encT ts ++ [k] ++ [a]).length := by simp [u2, uadd]
  rw [e2]
  obtain ⟨p3, l3⟩ := u20_push p2 (by simp [encT_len] at l1 l2 ⊢; omega) c
  refine ⟨by rw [encT_snoc]; simpa using p3, ?_⟩
  simp only [List.length_append, List.length_singleton, encT_len] at l1 l2 l3 ⊢
  omega

theorem top_rd {ts : List T3} {t : Buf} {k a c : UInt64} (ht : encT (ts ++ [(k, a, c)]) <+: t) (htl : t.length < 2 ^ 62) :
    bget t (3 * u (ts.length + 1) - 3) = k ∧ bget t (3 * u (ts.length + 1) - 2) = a ∧
    bget t (3 * u (ts.length + 1) - 1) = c := by
  have hl := ht.length_le
  rw [encT_snoc] at ht
  simp only [encT_len, List.length_append, List.length_singleton] at hl
  have hE := encT_len ts
  have e : ∀ j m, m = 3 - j → j < 3 → 3 * u (ts.length + 1) - u m = u ((encT ts).length + j) := by
    intro j m hm hj; subst hm; rw [u3, u_mul, usub (by omega) (by omega)]; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [show (3 * u (ts.length + 1) - 3 : UInt64) = 3 * u (ts.length + 1) - u 3 from rfl, e 0 3 rfl (by omega),
      bget_pre ht (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by omega),
      getD_app_right]; rfl
  · rw [u2, e 1 2 rfl (by omega), bget_pre ht (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by omega),
      getD_app_right]; rfl
  · rw [u1, e 2 1 rfl (by omega), bget_pre ht (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by omega),
      getD_app_right]; rfl

theorem set_mid {α} (L R : List α) (a a' : α) : (L ++ a :: R).set L.length a' = L ++ a' :: R := by
  simp [List.set_append_right]

/-- rewrite the middle word of the top record -/
theorem bset_top {ts : List T3} {t : Buf} {k a c : UInt64} (ht : encT (ts ++ [(k, a, c)]) <+: t) (htl : t.length < 2 ^ 62)
    (a' : UInt64) : encT (ts ++ [(k, a', c)]) <+: bset t (3 * u (ts.length + 1) - 2) a' ∧
      (bset t (3 * u (ts.length + 1) - 2) a').length = t.length := by
  have hl := ht.length_le
  rw [encT_snoc] at ht ⊢
  simp only [encT_len, List.length_append, List.length_singleton] at hl
  have hE := encT_len ts
  have e : 3 * u (ts.length + 1) - 2 = u ((encT ts ++ [k]).length) := by
    rw [u3, u_mul, u2, usub (by omega) (by omega)]; congr 1; simp; omega
  rw [e, bset_u t (by simp; omega)]
  refine ⟨?_, by simp⟩
  obtain ⟨r, hr⟩ := ht
  rw [← hr]
  have : encT ts ++ [(k, a, c).1, (k, a, c).2.1, (k, a, c).2.2] ++ r = (encT ts ++ [k]) ++ a :: (c :: r) := by simp
  rw [this, set_mid]
  exact ⟨r, by simp⟩

end NumP

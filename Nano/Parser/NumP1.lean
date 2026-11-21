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

end NumP

/- Facts about the native image (Nano/Run/NatImg.lean) for the segment law (M3) and the static laws:
the J instructions and the A64 words of the atom at a position (`at_j`, `at_words`), the boundaries (`at_bnd`,
`at_bnd_end`, `at_widx`, `at_widx_end`, `at_inner`), lengths (`NTm.j_pos`, `NTm.a_len`, `wordsOf_len`, `at_le`). -/
import Nano.Run.NatImg
namespace JT
open Proven.Top SimW CallProbe ArmEnc

/-- the number of A64 words of an atom list -/
def alenL : List NAt → Nat
  | [] => 0
  | x :: l => x.t.alen + alenL l

theorem jOf_cons (x : NAt) (l : List NAt) : jOf (x :: l) = x.t.j ++ jOf l := by simp [jOf]

theorem jOf_append (a b : List NAt) : jOf (a ++ b) = jOf a ++ jOf b := by simp [jOf]

theorem alenL_append (a b : List NAt) : alenL (a ++ b) = alenL a + alenL b := by
  induction a with
  | nil => simp [alenL]
  | cons x l ih => simp only [List.cons_append, alenL, ih]; omega

theorem liT_pos (d : Nat) (v : UInt64) : 1 ≤ (liT d v).length := by
  unfold liT; split <;> simp

/-- every atom has a J instruction -/
theorem NTm.j_pos (t : NTm) : 1 ≤ t.j.length := by
  cases t <;> simp only [NTm.j] <;> first | exact liT_pos _ _ | (split <;> simp) | simp

/-- the word count of an atom does not depend on its position -/
theorem NTm.a_len (t : NTm) (π : Nat → Nat) (q h : Nat) : (t.a π q h).length = t.alen := by
  cases t <;> simp only [NTm.alen, NTm.a] <;> (try rfl) <;> (repeat' split) <;> (try rfl) <;> simp_all

/-! ## boundaries -/

theorem bnd_head (l : List NAt) (q h : Nat) : (q, h) ∈ bnd l q h := by
  cases l <;> simp [bnd]

theorem bnd_ge : ∀ (l : List NAt) (q h p w : Nat), (p, w) ∈ bnd l q h → q ≤ p ∧ h ≤ w
  | [], q, h, p, w, hm => by
    simp only [bnd, List.mem_singleton, Prod.mk.injEq] at hm; omega
  | x :: l, q, h, p, w, hm => by
    simp only [bnd, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · omega
    · have := bnd_ge l _ _ p w hm; omega

theorem bnd_mem_append : ∀ (pre suf : List NAt) (q h : Nat),
    (q + (jOf pre).length, h + alenL pre) ∈ bnd (pre ++ suf) q h
  | [], suf, q, h => by simpa [jOf, alenL] using bnd_head suf q h
  | x :: pre, suf, q, h => by
    have := bnd_mem_append pre suf (q + x.t.j.length) (h + x.t.alen)
    simp only [List.cons_append, bnd, List.mem_cons, jOf_cons, List.length_append, alenL]
    right; rw [← Nat.add_assoc, ← Nat.add_assoc]; exact this

/-- no boundary strictly inside an atom -/
theorem bnd_split : ∀ (pre : List NAt) (x : NAt) (suf : List NAt) (q h p w : Nat),
    (p, w) ∈ bnd (pre ++ x :: suf) q h →
    p ≤ q + (jOf pre).length ∨ q + (jOf pre).length + x.t.j.length ≤ p
  | [], x, suf, q, h, p, w, hm => by
    simp only [List.nil_append, bnd, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, -⟩ | hm
    · left; omega
    · right; have := (bnd_ge _ _ _ _ _ hm).1; simp only [jOf, List.flatMap_nil, List.length_nil]; omega
  | y :: pre, x, suf, q, h, p, w, hm => by
    simp only [List.cons_append, bnd, List.mem_cons, Prod.mk.injEq] at hm
    rw [jOf_cons, List.length_append]
    rcases hm with ⟨rfl, -⟩ | hm
    · left; omega
    · have := bnd_split pre x suf _ _ p w hm; omega

/-- a J pc has one word index -/
theorem bnd_fun : ∀ (l : List NAt) (q h p w w' : Nat), (p, w) ∈ bnd l q h → (p, w') ∈ bnd l q h → w = w'
  | [], q, h, p, w, w', h1, h2 => by
    simp only [bnd, List.mem_singleton, Prod.mk.injEq] at h1 h2; omega
  | x :: l, q, h, p, w, w', h1, h2 => by
    have hp := x.t.j_pos
    simp only [bnd, List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨e1, e1'⟩ | h1 <;> rcases h2 with ⟨e2, e2'⟩ | h2
    · omega
    · have := (bnd_ge _ _ _ _ _ h2).1; omega
    · have := (bnd_ge _ _ _ _ _ h1).1; omega
    · exact bnd_fun l _ _ p w w' h1 h2

theorem widx_eq {B : List (Nat × Nat)} {p w : Nat} (hm : (p, w) ∈ B) (hu : ∀ w', (p, w') ∈ B → w' = w) :
    widx B p = w := by
  unfold widx
  cases hf : B.find? (fun x => x.1 == p) with
  | none => exact absurd (by simp) (List.find?_eq_none.1 hf (p, w) hm)
  | some y =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := y
    have e : a = p := by simpa using h1
    subst e
    simp [hu b h2]

/-! ## words -/

theorem wordsFrom_len (π : Nat → Nat) : ∀ (l : List NAt) (q h : Nat), (wordsFrom π l q h).length = alenL l
  | [], _, _ => rfl
  | x :: l, q, h => by
    simp only [wordsFrom, List.length_append, NTm.a_len, wordsFrom_len π l, alenL]

theorem wordsFrom_append (π : Nat → Nat) : ∀ (pre suf : List NAt) (q h : Nat),
    wordsFrom π (pre ++ suf) q h = wordsFrom π pre q h ++ wordsFrom π suf (q + (jOf pre).length) (h + alenL pre)
  | [], suf, q, h => by simp [wordsFrom, jOf, alenL]
  | x :: pre, suf, q, h => by
    simp only [List.cons_append, wordsFrom, wordsFrom_append π pre suf, jOf_cons, List.length_append, alenL,
      List.append_assoc, Nat.add_assoc]

theorem wordsOf_len (tl : List NAt) : (wordsOf tl).length = alenL tl := wordsFrom_len _ tl 0 0

theorem wordBytes_len (A : List Nat) : (wordBytes A).length = 4 * A.length := by
  induction A with
  | nil => rfl
  | cons w A ih => simp only [wordBytes, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢; omega

theorem imgOf_code_len (tl : List NAt) : (imgOf tl).code.length = 4 * (wordsOf tl).length := wordBytes_len _

/-! ## the atom at a position: `tl = pre ++ x :: suf`, J pc `(jOf pre).length`, word index `alenL pre` -/

section
variable {tl pre suf : List NAt} {x : NAt}

/-- its J instructions -/
theorem at_j (e : tl = pre ++ x :: suf) {i : Nat} (hi : i < x.t.j.length) :
    (jOf tl)[(jOf pre).length + i]? = x.t.j[i]? := by
  subst e
  rw [jOf_append, jOf_cons, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

/-- its A64 words -/
theorem at_words (e : tl = pre ++ x :: suf) {i : Nat} (hi : i < x.t.alen) :
    (wordsOf tl)[alenL pre + i]? = (x.t.a (widx (bnd tl 0 0)) (jOf pre).length (alenL pre))[i]? := by
  subst e
  unfold wordsOf
  rw [wordsFrom_append]
  simp only [wordsFrom, Nat.zero_add]
  rw [List.getElem?_append_right (by rw [wordsFrom_len]; omega), wordsFrom_len, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [NTm.a_len]; exact hi)]

theorem at_bnd (e : tl = pre ++ x :: suf) : ((jOf pre).length, alenL pre) ∈ bnd tl 0 0 := by
  subst e
  have := bnd_mem_append pre (x :: suf) 0 0
  simpa only [Nat.zero_add] using this

theorem at_bnd_end (e : tl = pre ++ x :: suf) :
    ((jOf pre).length + x.t.j.length, alenL pre + x.t.alen) ∈ bnd tl 0 0 := by
  subst e
  have := bnd_mem_append (pre ++ [x]) suf 0 0
  have e1 : (jOf (pre ++ [x])).length = (jOf pre).length + x.t.j.length := by
    rw [jOf_append, List.length_append, jOf_cons]; simp [jOf]
  have e2 : alenL (pre ++ [x]) = alenL pre + x.t.alen := by rw [alenL_append]; simp [alenL]
  rw [e1, e2, Nat.zero_add, Nat.zero_add, List.append_assoc, List.singleton_append] at this
  exact this

theorem at_widx (e : tl = pre ++ x :: suf) : widx (bnd tl 0 0) (jOf pre).length = alenL pre :=
  widx_eq (at_bnd e) fun _ h => bnd_fun _ _ _ _ _ _ h (at_bnd e)

theorem at_widx_end (e : tl = pre ++ x :: suf) :
    widx (bnd tl 0 0) ((jOf pre).length + x.t.j.length) = alenL pre + x.t.alen :=
  widx_eq (at_bnd_end e) fun _ h => bnd_fun _ _ _ _ _ _ h (at_bnd_end e)

theorem at_vis (e : tl = pre ++ x :: suf) : nVis tl (jOf pre).length := ⟨_, at_bnd e⟩

theorem at_vis_end (e : tl = pre ++ x :: suf) : nVis tl ((jOf pre).length + x.t.j.length) := ⟨_, at_bnd_end e⟩

/-- the interior J pcs of an atom are not anchors -/
theorem at_inner (e : tl = pre ++ x :: suf) {i : Nat} (h0 : 0 < i) (hi : i < x.t.j.length) :
    ¬ nVis tl ((jOf pre).length + i) := by
  rintro ⟨w, hm⟩
  subst e
  have := bnd_split pre x suf 0 0 _ w hm
  omega

/-- the atom's words lie in the code -/
theorem at_le (e : tl = pre ++ x :: suf) : alenL pre + x.t.alen ≤ (wordsOf tl).length := by
  subst e
  rw [wordsOf_len, alenL_append]; simp only [alenL]; omega

end

/-! ## every atom has a word -/

theorem walk0_nil {t V e : Nat} (h : walk0 t V e 4 0 = []) :
    chk V 0 = e ∧ chk V 1 = e ∧ chk V 2 = e ∧ chk V 3 = e := by
  by_cases h0 : chk V 0 = e
  · by_cases h1 : chk V 1 = e
    · by_cases h2 : chk V 2 = e
      · by_cases h3 : chk V 3 = e
        · exact ⟨h0, h1, h2, h3⟩
        · simp [walk0, h0, h1, h2, h3] at h
      · simp [walk0, h0, h1, h2] at h
    · simp [walk0, h0, h1] at h
  · simp [walk0, h0] at h

theorem liL_pos (t : Nat) {V : Nat} (hV : V < 2 ^ 64) : 1 ≤ (liL t V).length := by
  unfold liL
  by_cases h1 : V < 65536
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : 2 ^ 64 - 1 - V < 65536
    · rw [if_pos h2]; simp
    · rw [if_neg h2]
      split
      · cases hl : walk0 t V 65535 4 0 with
        | nil =>
          obtain ⟨c0, c1, c2, c3⟩ := walk0_nil hl
          change V / 1 % 65536 = 65535 at c0
          change V / 65536 % 65536 = 65535 at c1
          change V / 4294967296 % 65536 = 65535 at c2
          change V / 281474976710656 % 65536 = 65535 at c3
          omega
        | cons a l => simp
      · cases hl : walk0 t V 0 4 0 with
        | nil =>
          obtain ⟨c0, c1, c2, c3⟩ := walk0_nil hl
          change V / 1 % 65536 = 0 at c0
          change V / 65536 % 65536 = 0 at c1
          change V / 4294967296 % 65536 = 0 at c2
          change V / 281474976710656 % 65536 = 0 at c3
          omega
        | cons a l => simp

theorem memW_pos (st : Bool) (t n : Nat) (off : Int) : 1 ≤ (NTm.memW st t n off).length := by
  unfold NTm.memW; split
  · simp
  · split <;> simp

/-- every atom has an A64 word -/
theorem NTm.alen_pos (t : NTm) : 1 ≤ t.alen := by
  cases t <;> simp only [NTm.alen, NTm.a]
  case li d v => exact liL_pos _ v.toNat_lt
  case addi d n imm =>
    split
    · exact liL_pos _ (UInt64.toNat_lt _)
    · split <;> simp
  case alu op d x y => split <;> simp
  case ld d n off => exact memW_pos _ _ _ _
  case sd s n off =>
    split
    · simp
    · exact memW_pos _ _ _ _
  all_goals simp

/-! ## boundaries: word indices -/

theorem bnd_le : ∀ (l : List NAt) (q h p w : Nat), (p, w) ∈ bnd l q h → w ≤ h + alenL l
  | [], q, h, p, w, hm => by
    simp only [bnd, List.mem_singleton, Prod.mk.injEq] at hm; simp only [alenL]; omega
  | x :: l, q, h, p, w, hm => by
    simp only [bnd, List.mem_cons, Prod.mk.injEq] at hm
    simp only [alenL]
    rcases hm with ⟨-, rfl⟩ | hm
    · omega
    · have := bnd_le l _ _ p w hm; omega

/-- a word index has one J pc -/
theorem bnd_inj : ∀ (l : List NAt) (q h p p' w : Nat), (p, w) ∈ bnd l q h → (p', w) ∈ bnd l q h → p = p'
  | [], q, h, p, p', w, h1, h2 => by
    simp only [bnd, List.mem_singleton, Prod.mk.injEq] at h1 h2; omega
  | x :: l, q, h, p, p', w, h1, h2 => by
    have hp := x.t.alen_pos
    simp only [bnd, List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨e1, e1'⟩ | h1 <;> rcases h2 with ⟨e2, e2'⟩ | h2
    · omega
    · have := (bnd_ge _ _ _ _ _ h2).2; omega
    · have := (bnd_ge _ _ _ _ _ h1).2; omega
    · exact bnd_inj l _ _ p p' w h1 h2

/-- an anchor with its word index -/
theorem vis_widx {tl : List NAt} {p : Nat} (h : nVis tl p) : (p, widx (bnd tl 0 0) p) ∈ bnd tl 0 0 := by
  obtain ⟨w, hm⟩ := h
  rw [widx_eq hm fun _ h => bnd_fun _ _ _ _ _ _ h hm]; exact hm

/-- the word index of an anchor lies in the code (or is its end) -/
theorem vis_le {tl : List NAt} {p : Nat} (h : nVis tl p) : widx (bnd tl 0 0) p ≤ (wordsOf tl).length := by
  have := bnd_le tl 0 0 _ _ (vis_widx h)
  rw [wordsOf_len]; omega

/-- the byte offset of an anchor -/
theorem vis_off {tl : List NAt} {p : Nat} (h : nVis tl p) (hs : (wordsOf tl).length < 2 ^ 18) :
    (imgOf tl).off p = 4 * widx (bnd tl 0 0) p := by
  have hm := vis_widx h
  have hle := vis_le h
  show nOff (bnd tl 0 0) p = _
  unfold nOff
  rw [if_pos]
  refine ⟨by omega, ?_⟩
  cases hf : (bnd tl 0 0).find? (fun y => 4 * y.2 == 4 * widx (bnd tl 0 0) p) with
  | none => exact absurd (by simp) (List.find?_eq_none.1 hf _ hm)
  | some y =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := y
    have e : b = widx (bnd tl 0 0) p := by
      have : 4 * b = 4 * widx (bnd tl 0 0) p := by simpa using h1
      omega
    subst e
    simp [bnd_inj _ _ _ _ _ _ h2 hm]

/-! ## dead flags -/

theorem dl_ge : ∀ (l : List NAt) (q p : Nat) (y : NAt), (p, y) ∈ dl l q → q ≤ p
  | [], _, _, _, hm => by simp [dl] at hm
  | x :: l, q, p, y, hm => by
    simp only [dl, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, -⟩ | hm
    · omega
    · have := dl_ge l _ p y hm; omega

theorem dl_mem_append : ∀ (pre : List NAt) (x : NAt) (suf : List NAt) (q : Nat),
    (q + (jOf pre).length, x) ∈ dl (pre ++ x :: suf) q
  | [], x, suf, q => by simp [dl, jOf]
  | y :: pre, x, suf, q => by
    have := dl_mem_append pre x suf (q + y.t.j.length)
    simp only [List.cons_append, dl, List.mem_cons, jOf_cons, List.length_append]
    right; rw [← Nat.add_assoc]; exact this

theorem dl_fun : ∀ (l : List NAt) (q p : Nat) (y y' : NAt), (p, y) ∈ dl l q → (p, y') ∈ dl l q → y = y'
  | [], _, _, _, _, h1, _ => by simp [dl] at h1
  | x :: l, q, p, y, y', h1, h2 => by
    have hp := x.t.j_pos
    simp only [dl, List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨e1, e1'⟩ | h1 <;> rcases h2 with ⟨e2, e2'⟩ | h2
    · rw [e1', e2']
    · have := dl_ge _ _ _ _ h2; omega
    · have := dl_ge _ _ _ _ h1; omega
    · exact dl_fun l _ p y y' h1 h2

/-- the dead flags at an atom's start are the atom's -/
theorem at_dead {tl pre suf : List NAt} {x : NAt} (e : tl = pre ++ x :: suf) (r : Nat) :
    nDead tl (jOf pre).length r ↔ x.dead r = true := by
  subst e
  have hm : ((jOf pre).length, x) ∈ dl (pre ++ x :: suf) 0 := by
    have := dl_mem_append pre x suf 0; simpa only [Nat.zero_add] using this
  constructor
  · rintro ⟨y, hy, hd⟩
    rw [← dl_fun _ _ _ _ _ hy hm]; exact hd
  · exact fun hd => ⟨x, hm, hd⟩

/-- a jump target of an atom is an anchor in the code -/
theorem at_tgt {tl pre suf : List NAt} {x : NAt} (W : NWf tl) (e : tl = pre ++ x :: suf) {p : Nat}
    (hp : p ∈ x.t.tg (jOf pre).length) :
    nVis tl p ∧ widx (bnd tl 0 0) p ≤ (wordsOf tl).length ∧ ∀ r, x.out r = true → nDead tl p r :=
  have h := W.tgt pre x suf e p hp
  ⟨h.1, vis_le h.1, h.2⟩

end JT

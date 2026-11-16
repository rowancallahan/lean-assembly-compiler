/- Paged dynamic arrays (NOTES section 30), part 2: arrays as pages.

An array of `n` words at page table `pt` (a page of the pool): entry `i < npages n` of the page table is the
first word of the data page holding elements `i P .. i P + P - 1`; element `j` is word `j % P` of the page in
entry `j / P` (`j >>> lg`, `j &&& (P - 1)`: one extra load per access).  At most `P` entries, so `n ≤ P * P`.

`Store C env W arrs`: the pool holds exactly the pages of the arrays `arrs` (page table and data pages of
each) and every array is at its page table.  Operations (each a short statement of the middle layer):
`getEl` (two loads), `setEl` (a load and a store), `pushEl` (a page from the pool when the size is a multiple
of `P`, else a load and a store), `newArr` (one page), `freeArr` (every page back to the free list). -/
import Riscv.Frontx.WpPool

namespace Proven.WP
open Proven Proven.WA
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj)

abbrev W64 := List (BitVec 64)

/-! ## Arrays at page tables -/

/-- data pages of `n` elements -/
def npages (n : Nat) : Nat := (n + (P - 1)) / P

/-- entry `i` of the page table at `pt` -/
def ent (W : W64) (pt i : Nat) : Nat := (W[pt + i]?.getD 0).toNat

/-- the pages of an array: its page table, then its data pages -/
def pagesOf (W : W64) (pt n : Nat) : List Nat := pt :: (List.range (npages n)).map (ent W pt)

structure ArrAt (W : W64) (pt : Nat) (xs : W64) : Prop where
  pt_al : pt % P = 0
  pt_in : pt + P ≤ W.length
  len : xs.length ≤ P * P
  ents : ∀ i, i < npages xs.length → ent W pt i % P = 0 ∧ ent W pt i + P ≤ W.length
  els : ∀ j, j < xs.length → W[ent W pt (j / P) + j % P]? = xs[j]?
  nd : (pagesOf W pt xs.length).Nodup

/-- word `q` lies in one of the pages `S` -/
def InPages (S : List Nat) (q : Nat) : Prop := ∃ p ∈ S, p ≤ q ∧ q < p + P

theorem npages_le {n : Nat} (h : n ≤ P * P) : npages n ≤ P := by
  unfold npages; rw [P] at *; omega

theorem div_lt_npages {j n : Nat} (h : j < n) : j / P < npages n := by
  unfold npages; rw [P] at *; omega

theorem mod_lt_P (j : Nat) : j % P < P := Nat.mod_lt _ P_pos

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]; rw [h a (List.mem_cons_self ..), flatMap_congr' fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem ent_inj {W : W64} {pt n : Nat} (h : (pagesOf W pt n).Nodup) {i i' : Nat} (hi : i < npages n)
    (hi' : i' < npages n) (e : ent W pt i = ent W pt i') : i = i' := by
  have h2 := (List.nodup_cons.1 h).2
  unfold List.Nodup at h2
  rw [List.pairwise_map, List.pairwise_iff_getElem] at h2
  rcases Nat.lt_trichotomy i i' with hl | hl | hl
  · exact absurd e (by have := h2 i i' (by simpa using hi) (by simpa using hi') hl; simpa using this)
  · exact hl
  · exact absurd e.symm (by have := h2 i' i (by simpa using hi') (by simpa using hi) hl; simpa using this)

theorem pt_ne_ent {W : W64} {pt n : Nat} (h : (pagesOf W pt n).Nodup) {i : Nat} (hi : i < npages n) :
    pt ≠ ent W pt i := fun e =>
  (List.nodup_cons.1 h).1 (List.mem_map.2 ⟨i, List.mem_range.2 hi, e.symm⟩)

/-- an array survives writes outside its pages -/
theorem ArrAt.frame {W W' : W64} {pt : Nat} {xs : W64} (h : ArrAt W pt xs) (hl : W'.length = W.length)
    (hw : ∀ q, InPages (pagesOf W pt xs.length) q → W'[q]? = W[q]?) :
    ArrAt W' pt xs ∧ pagesOf W' pt xs.length = pagesOf W pt xs.length := by
  have hent : ∀ i, i < npages xs.length → ent W' pt i = ent W pt i := fun i hi => by
    unfold ent
    rw [hw (pt + i) ⟨pt, List.mem_cons_self .., by omega, by have := npages_le h.len; omega⟩]
  have hpg : pagesOf W' pt xs.length = pagesOf W pt xs.length := by
    unfold pagesOf; congr 1
    exact List.map_congr_left fun i hi => hent i (List.mem_range.1 hi)
  refine ⟨⟨h.pt_al, by rw [hl]; exact h.pt_in, h.len, fun i hi => by rw [hent i hi, hl]; exact h.ents i hi,
    fun j hj => ?_, by rw [hpg]; exact h.nd⟩, hpg⟩
  have hi := div_lt_npages hj
  rw [hent _ hi, hw _ ⟨ent W pt (j / P), List.mem_cons_of_mem _ (List.mem_map.2 ⟨j / P, List.mem_range.2 hi, rfl⟩),
    by omega, by have := mod_lt_P j; omega⟩]
  exact h.els j hj

/-! ## The store: the pool holds exactly the arrays' pages -/

def owned (W : W64) (arrs : List (Nat × W64)) : List Nat := arrs.flatMap fun a => pagesOf W a.1 a.2.length

def Store (C : Nat) (env : Mach.BEnv) (W : W64) (arrs : List (Nat × W64)) : Prop :=
  PoolInv C env W (owned W arrs) ∧ ∀ a ∈ arrs, ArrAt W a.1 a.2

theorem PoolInv.perm {C : Nat} {env : Mach.BEnv} {W : W64} {u u' : List Nat} (h : PoolInv C env W u)
    (hp : u.Perm u') : PoolInv C env W u' := by
  obtain ⟨b, fr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨b, fr, h1, h2, h3, h4, h5, h6, h7, (hp.symm.append_right fr).trans h8⟩

theorem owned_append (W : W64) (a b : List (Nat × W64)) : owned W (a ++ b) = owned W a ++ owned W b := by
  simp [owned]

theorem owned_cons (W : W64) (a : Nat × W64) (b : List (Nat × W64)) :
    owned W (a :: b) = pagesOf W a.1 a.2.length ++ owned W b := by simp [owned]

/-- the pages in use, counted: one page table and the data pages per array -/
def pageCount (arrs : List (Nat × W64)) : Nat := (arrs.map fun a => 1 + npages a.2.length).sum

theorem owned_length (W : W64) : ∀ arrs : List (Nat × W64), (owned W arrs).length = pageCount arrs
  | [] => rfl
  | a :: as => by
    rw [owned_cons, List.length_append, owned_length W as]
    simp [pageCount, pagesOf]; omega

/-- words in the pages of one array of the store are in no other array's pages and in no free page: a
write there keeps the rest of the store -/
theorem Store.write {C : Nat} {env env' : Mach.BEnv} {W W' : W64} {pre post : List (Nat × W64)} {pt : Nat}
    {xs xs' : W64} (h : Store C env W (pre ++ (pt, xs) :: post))
    (he : ∀ j, j = vCap ∨ j = vBump ∨ j = vFh → env' j = env j) (hl : W'.length = W.length)
    (hw : ∀ q, ¬ InPages (pagesOf W pt xs.length) q → W'[q]? = W[q]?)
    (hnew : ArrAt W' pt xs') (hpg : pagesOf W' pt xs'.length = pagesOf W pt xs.length) :
    Store C env' W' (pre ++ (pt, xs') :: post) := by
  obtain ⟨hp, ha⟩ := h
  have hnd := hp.nodup
  rw [owned_append, owned_cons] at hnd
  -- the other arrays' pages are apart from this array's pages
  have hsep : ∀ a ∈ pre ++ post, ∀ q, InPages (pagesOf W a.1 a.2.length) q → ¬ InPages (pagesOf W pt xs.length) q := by
    intro a ha' q ⟨p1, hp1, h1, h1'⟩ ⟨p2, hp2, h2, h2'⟩
    have hin1 : p1 ∈ owned W (pre ++ (pt, xs) :: post) := by
      rcases List.mem_append.1 ha' with h | h
      · rw [owned_append]; exact List.mem_append_left _ (List.mem_flatMap.2 ⟨a, h, hp1⟩)
      · rw [owned_append, owned_cons]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, h, hp1⟩))
    have hin2 : p2 ∈ owned W (pre ++ (pt, xs) :: post) := by
      rw [owned_append, owned_cons]; exact List.mem_append_right _ (List.mem_append_left _ hp2)
    have b1 := hp.page hin1
    have b2 := hp.page hin2
    have hne : p1 ≠ p2 := by
      intro e; subst e
      rcases List.mem_append.1 ha' with h | h
      · exact (List.nodup_append.1 hnd).2.2 p1 (List.mem_flatMap.2 ⟨a, h, hp1⟩) p1
          (List.mem_append_left _ hp2) rfl
      · have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1)
        exact this.2.2 p1 hp2 p1 (List.mem_flatMap.2 ⟨a, h, hp1⟩) rfl
    rcases page_apart b1.1 b2.1 hne with h | h <;> omega
  have hother : ∀ a ∈ pre ++ post, ArrAt W' a.1 a.2 ∧ pagesOf W' a.1 a.2.length = pagesOf W a.1 a.2.length :=
    fun a ha' => ArrAt.frame (ha a (by rcases List.mem_append.1 ha' with h | h <;> simp [h])) hl
      (fun q hq => hw q (hsep a ha' q hq))
  have howned : owned W' (pre ++ (pt, xs') :: post) = owned W (pre ++ (pt, xs) :: post) := by
    rw [owned_append, owned_cons, owned_append, owned_cons]
    have e1 : owned W' pre = owned W pre := by
      unfold owned; exact flatMap_congr' fun a h => (hother a (List.mem_append_left _ h)).2
    have e2 : owned W' post = owned W post := by
      unfold owned; exact flatMap_congr' fun a h => (hother a (List.mem_append_right _ h)).2
    rw [e1, e2, hpg]
  refine ⟨?_, fun a ha' => ?_⟩
  · rw [howned]
    refine hp.frame he hl fun q hq => hw q fun ⟨p, hp', h1, h2⟩ => ?_
    have := hq p (by rw [owned_append, owned_cons]; exact List.mem_append_right _ (List.mem_append_left _ hp'))
    omega
  · rcases List.mem_append.1 ha' with h | h
    · exact (hother a (List.mem_append_left _ h)).1
    · rcases List.mem_cons.1 h with rfl | h
      · exact hnew
      · exact (hother a (List.mem_append_right _ h)).1

/-! ## Index arithmetic -/

theorem lshr_lg {j : Nat} (h : j < 2 ^ 64) : Op.eval .lshr (rN j) (BitVec.ofNat 64 lg) = rN (j / P) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Op.eval, BitVec.toNat_ushiftRight, rN_toNat h, lg, P]
  rw [rN_toNat (by omega)]; simp [Nat.shiftRight_eq_div_pow]

theorem and_mask {j : Nat} (h : j < 2 ^ 64) : Op.eval .and (rN j) (BitVec.ofNat 64 (P - 1)) = rN (j % P) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Op.eval, BitVec.toNat_and, rN_toNat h, P]
  rw [rN_toNat (by omega)]
  show j &&& (2 ^ 10 - 1) = j % 2 ^ 10
  exact Nat.and_two_pow_sub_one_eq_mod _ 10

theorem add_rN (a b : Nat) : Op.eval .add (rN a) (rN b) = rN (a + b) := (rN_add a b).symm

/-- `pt + (j >>> lg)` -/
def ptIx (ptv jv : Nat) : MB := .bin .add (.var ptv) (.bin .lshr (.var jv) (.const (BitVec.ofNat 64 lg)))
/-- `e + (j &&& (P - 1))` -/
def elIx (ev jv : Nat) : MB := .bin .add (.var ev) (.bin .and (.var jv) (.const (BitVec.ofNat 64 (P - 1))))

theorem ptIx_den {env : Mach.BEnv} {ptv jv pt j : Nat} (h1 : env ptv = rN pt) (h2 : env jv = rN j)
    (hj : j < 2 ^ 32) (hp : pt < 2 ^ 32) : ((ptIx ptv jv).denote env).toNat = pt + j / P := by
  simp only [ptIx, Mach.BExp.denote, h1, h2]
  rw [lshr_lg (by omega), add_rN, rN_toNat (by have : j / P ≤ j := Nat.div_le_self _ _; omega)]

theorem elIx_den {env : Mach.BEnv} {ev jv e j : Nat} (h1 : env ev = rN e) (h2 : env jv = rN j)
    (hj : j < 2 ^ 32) (he : e < 2 ^ 32) : ((elIx ev jv).denote env).toNat = e + j % P := by
  simp only [elIx, Mach.BExp.denote, h1, h2]
  rw [and_mask (by omega), add_rN, rN_toNat (by have := mod_lt_P j; rw [P] at *; omega)]

theorem ent_rN {W : W64} {pt i : Nat} (h : pt + i < W.length) : W[pt + i] = rN (ent W pt i) := by
  unfold ent; rw [List.getElem?_eq_getElem h]; simp [rN]

/-! ## Reading and writing an element -/

/-- `d := a[d]` for the array with page table in `ptv` (temporary `d + 1`) -/
def getEl (ptv d : Nat) : MS :=
  .seq (.load64 (d + 1) 0 (ptIx ptv d)) (.load64 d 0 (elIx (d + 1) d))

theorem getEl_ok {W : W64} {pt : Nat} {xs : W64} (hA : ArrAt W pt xs) (H : Heap) (env : Mach.BEnv) (ptv d : Nat)
    (hv : ptv ≠ d + 1 ∧ ptv ≠ d) (h1 : env ptv = rN pt) (j : Nat) (h2 : env d = rN j) (hj : j < xs.length)
    (h32 : W.length < 2 ^ 32) :
    ∃ x, xs[j]? = some x ∧ Mach.BExec (getEl ptv d) ⟨env, H, [W]⟩
      ⟨(env.set (d + 1) (rN (ent W pt (j / P)))).set d x, H, [W]⟩ := by
  have hjP := hA.len
  have hjl : j < 2 ^ 32 := by rw [P] at hjP; omega
  have hpt := hA.pt_in
  have hi := div_lt_npages hj
  have hnp := npages_le hjP
  have hix := ptIx_den (env := env) h1 h2 hjl (by omega)
  have hl1 : pt + j / P < W.length := by omega
  have e1 := Mach.BExec.load64 (v := d + 1) (b := 0) (i := ptIx ptv d) (σ := ⟨env, H, [W]⟩) (by simp)
    (by simp only [List.getElem_cons_zero]; rw [hix]; exact hl1)
  simp only [List.getElem_cons_zero, hix, ent_rN hl1] at e1
  have he := hA.ents _ hi
  have hix2 := elIx_den (env := env.set (d + 1) (rN (ent W pt (j / P)))) (ev := d + 1) (jv := d)
    set_eq (by rw [set_ne (by omega)]; exact h2) hjl (by omega)
  have hl2 : ent W pt (j / P) + j % P < W.length := by have := mod_lt_P j; omega
  have hx := hA.els j hj
  rw [List.getElem?_eq_getElem hl2, List.getElem?_eq_getElem hj] at hx
  have e2 := Mach.BExec.load64 (v := d) (b := 0) (i := elIx (d + 1) d)
    (σ := ⟨env.set (d + 1) (rN (ent W pt (j / P))), H, [W]⟩) (by simp)
    (by simp only [List.getElem_cons_zero]; rw [hix2]; exact hl2)
  simp only [List.getElem_cons_zero, hix2, Option.some.inj hx] at e2
  exact ⟨_, List.getElem?_eq_getElem hj, .seq e1 e2⟩

/-- `a[i] := x` for the array with page table in `ptv` (index in `iv`, value in `xv`, temporary `t`) -/
def setEl (ptv iv xv t : Nat) : MS :=
  .seq (.load64 t 0 (ptIx ptv iv)) (.store64 0 (elIx t iv) (.var xv))

theorem setEl_ok {W : W64} {pt : Nat} {xs : W64} (hA : ArrAt W pt xs) (H : Heap) (env : Mach.BEnv)
    (ptv iv xv t : Nat) (hv : t ≠ ptv ∧ t ≠ iv ∧ t ≠ xv) (h1 : env ptv = rN pt) (j : Nat) (h2 : env iv = rN j)
    (hj : j < xs.length) (h32 : W.length < 2 ^ 32) :
    ∃ W', Mach.BExec (setEl ptv iv xv t) ⟨env, H, [W]⟩ ⟨env.set t (rN (ent W pt (j / P))), H, [W']⟩ ∧
      W'.length = W.length ∧ (∀ q, ¬ InPages (pagesOf W pt xs.length) q → W'[q]? = W[q]?) ∧
      ArrAt W' pt (xs.set j (env xv)) ∧ pagesOf W' pt (xs.set j (env xv)).length = pagesOf W pt xs.length := by
  have hjP := hA.len
  have hjl : j < 2 ^ 32 := by rw [P] at hjP; omega
  have hpt := hA.pt_in
  have hi := div_lt_npages hj
  have hnp := npages_le hjP
  have hix := ptIx_den (env := env) h1 h2 hjl (by omega)
  have hl1 : pt + j / P < W.length := by omega
  have e1 := Mach.BExec.load64 (v := t) (b := 0) (i := ptIx ptv iv) (σ := ⟨env, H, [W]⟩) (by simp)
    (by simp only [List.getElem_cons_zero]; rw [hix]; exact hl1)
  simp only [List.getElem_cons_zero, hix, ent_rN hl1] at e1
  have he := hA.ents _ hi
  generalize hE : ent W pt (j / P) = E at he e1
  have hix2 := elIx_den (env := env.set t (rN E)) (ev := t) (jv := iv) set_eq
    (by rw [set_ne (Ne.symm hv.2.1)]; exact h2) hjl (by omega)
  have hl2 : E + j % P < W.length := by have := mod_lt_P j; omega
  have e2 := store64_at (σ := ⟨env.set t (rN E), H, [W]⟩) rfl (elIx t iv) (.var xv) (E + j % P) hix2 hl2
  simp only [Mach.BExp.denote, set_ne (Ne.symm hv.2.2)] at e2
  have hin : InPages (pagesOf W pt xs.length) (E + j % P) :=
    ⟨E, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j / P, List.mem_range.2 hi, hE⟩), by omega,
      by have := mod_lt_P j; omega⟩
  have hnd := hA.nd
  have hptE : pt ≠ E := hE ▸ pt_ne_ent hnd hi
  have hpte : ∀ i, i < P → pt + i ≠ E + j % P := by
    intro i hi' e
    rcases page_apart hA.pt_al he.1 hptE with h | h <;> have := mod_lt_P j <;> omega
  have hent : ∀ i, i < npages xs.length →
      ent (W.set (E + j % P) (env xv)) pt i = ent W pt i := fun i hi' => by
    unfold ent; rw [List.getElem?_set_ne (Ne.symm (hpte i (by omega)))]
  have hpg : pagesOf (W.set (E + j % P) (env xv)) pt xs.length = pagesOf W pt xs.length := by
    unfold pagesOf; congr 1
    exact List.map_congr_left fun i hi' => hent i (List.mem_range.1 hi')
  refine ⟨_, .seq e1 e2, by simp, fun q hq => ?_, ⟨hA.pt_al, by simpa using hpt, by simpa using hjP,
    fun i hi' => by rw [List.length_set] at hi'; rw [hent i hi', List.length_set]; exact hA.ents i hi',
    fun j' hj' => ?_, by rw [List.length_set, hpg]; exact hnd⟩, by rw [List.length_set, hpg]⟩
  · rw [List.getElem?_set_ne]; intro e; subst e; exact hq hin
  · rw [List.length_set] at hj'
    have hi2 := div_lt_npages hj'
    rw [hent _ hi2, List.getElem?_set, List.getElem?_set]
    by_cases hjj : j = j'
    · subst hjj; rw [if_pos (by rw [hE]), if_pos (by omega), if_pos rfl, if_pos hj]
    · rw [if_neg hjj]
      have hne : E + j % P ≠ ent W pt (j' / P) + j' % P := by
        intro e
        have hm1 := mod_lt_P j; have hm2 := mod_lt_P j'
        have he2 := hA.ents _ hi2
        by_cases hq : j / P = j' / P
        · rw [← hE, hq] at e
          have : j % P = j' % P := by omega
          exact hjj (by rw [← Nat.div_add_mod j P, ← Nat.div_add_mod j' P, hq, this])
        · have : E ≠ ent W pt (j' / P) := fun e' => hq (ent_inj hnd hi hi2 (hE.trans e'))
          rcases page_apart he.1 he2.1 this with h | h <;> omega
      rw [if_neg hne]; exact hA.els j' hj'

/-! ## Fresh pages, pushes -/

/-- the other arrays keep their elements and pages when only words in the pages `S` change -/
theorem keep_others {C : Nat} {env : Mach.BEnv} {W W' : W64} {U : List Nat} (hp : PoolInv C env W U)
    {others : List (Nat × W64)} {S : List Nat} (hnd : (owned W others ++ S).Nodup)
    (hin : ∀ p ∈ owned W others ++ S, p ∈ U) (ha : ∀ a ∈ others, ArrAt W a.1 a.2) (hl : W'.length = W.length)
    (hw : ∀ q, ¬ InPages S q → W'[q]? = W[q]?) :
    (∀ a ∈ others, ArrAt W' a.1 a.2 ∧ pagesOf W' a.1 a.2.length = pagesOf W a.1 a.2.length) ∧
      owned W' others = owned W others := by
  have key : ∀ a ∈ others, ∀ q, InPages (pagesOf W a.1 a.2.length) q → W'[q]? = W[q]? := by
    intro a ha' q ⟨p1, hp1, h1, h1'⟩
    apply hw; rintro ⟨p2, hp2, h2, h2'⟩
    have m1 : p1 ∈ owned W others := List.mem_flatMap.2 ⟨a, ha', hp1⟩
    have b1 := hp.page (hin p1 (List.mem_append_left _ m1))
    have b2 := hp.page (hin p2 (List.mem_append_right _ hp2))
    have hne : p1 ≠ p2 := fun e => (List.nodup_append.1 hnd).2.2 p1 m1 p2 hp2 e
    rcases page_apart b1.1 b2.1 hne with h | h <;> omega
  have hk := fun a ha' => ArrAt.frame (ha a ha') hl (key a ha')
  exact ⟨hk, by unfold owned; exact flatMap_congr' fun a h => (hk a h).2⟩

/-- a new empty array: one page for its page table, size `0` -/
def newArr (ptv sv t : Nat) : MS := .seq (allocCode ptv t) (.assign sv (.const 0))

theorem newArr_ok {C : Nat} {env : Mach.BEnv} {W : W64} {arrs : List (Nat × W64)} (H : Heap)
    (h : Store C env W arrs) (ptv sv t : Nat) (h8 : 8 ≤ ptv ∧ 8 ≤ t ∧ 8 ≤ sv) (hd : ptv ≠ t ∧ ptv ≠ t + 1)
    (hsv : sv ≠ ptv) :
    ∃ env', Mach.BExec (newArr ptv sv t) ⟨env, H, [W]⟩ ⟨env', H, [W]⟩ ∧
      (∀ j, ¬ AllocVars ptv t j → j ≠ sv → env' j = env j) ∧
      ((pageCount arrs < C ∧ env' vOk = env vOk ∧ env' sv = 0 ∧ ∃ p, env' ptv = rN p ∧
          Store C env' W ((p, []) :: arrs)) ∨
        (pageCount arrs = C ∧ env' vOk = 0)) := by
  obtain ⟨hp, ha⟩ := h
  obtain ⟨env1, e1, k1, r1⟩ := alloc_ok H hp ptv t h8.1 h8.2.1 hd
  have hsv7 : sv ≠ vOk := by simp only [vOk]; omega
  refine ⟨env1.set sv 0, .seq e1 .assign, fun j hj hj' => by rw [set_ne hj']; exact k1 j hj, ?_⟩
  rcases r1 with ⟨hlt, hok, p, hpv, hpa, hpc, hpu, hp1⟩ | ⟨heq, hok⟩
  · refine .inl ⟨by rw [← owned_length]; exact hlt, by rw [set_ne (Ne.symm hsv7)]; exact hok, set_eq, p,
      by rw [set_ne (Ne.symm hsv)]; exact hpv, ?_, ?_⟩
    · rw [owned_cons]
      exact (hp1.frame (fun j hj => by
        rcases hj with rfl | rfl | rfl <;> rw [set_ne (by simp only [vCap, vBump, vFh]; omega)]) rfl
        (fun _ _ => rfl)).perm (by simp [pagesOf, npages, P])
    · intro a ha'
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ⟨hpa, by have := hp1.wlen; omega, by simp, fun i hi => by simp [npages, P] at hi,
          fun j hj => by simp at hj, by simp [pagesOf, npages, P]⟩
      · exact ha a ha'
  · exact .inr ⟨by rw [← owned_length]; exact heq, by rw [set_ne (Ne.symm hsv7)]; exact hok⟩

theorem npages_succ_of_mod {n : Nat} (h : n % P = 0) : npages (n + 1) = npages n + 1 ∧ npages n = n / P := by
  unfold npages; rw [P] at *; omega

theorem npages_succ_of_mod_ne {n : Nat} (h : n % P ≠ 0) : npages (n + 1) = npages n ∧ n / P < npages n := by
  unfold npages; rw [P] at *; omega

/-- `a.push x` (size in `sv`, page table in `ptv`, value in `xv`, temporaries `t .. t + 6`): a new data page
when the size is a multiple of `P` -/
def pushEl (ptv sv xv t : Nat) : MS :=
  .seq (.assign (t + 2) (.bin .eq (.bin .and (.var sv) (.const (BitVec.ofNat 64 (P - 1)))) (.const 0)))
  (.seq (.assign (t + 3) (.bin .xor (.var (t + 2)) (.const 1)))
  (.seq (when (t + 2) (.seq (allocCode (t + 4) t)
      (.seq (.store64 0 (ptIx ptv sv) (.var (t + 4)))
      (.seq (.assign (t + 5) (.var vOk))
        (when (t + 5) (.seq (.store64 0 (.var (t + 4)) (.var xv))
          (.assign sv (.bin .add (.var sv) (.const 1)))))))))
    (when (t + 3) (.seq (setEl ptv sv xv (t + 6)) (.assign sv (.bin .add (.var sv) (.const 1)))))))

/-- writing element `n = xs.length` into the last data page (room left: `n % P ≠ 0`) -/
theorem setEl_end_ok {W : W64} {pt : Nat} {xs : W64} (hA : ArrAt W pt xs) (H : Heap) (env : Mach.BEnv)
    (ptv iv xv t : Nat) (hv : t ≠ ptv ∧ t ≠ iv ∧ t ≠ xv) (h1 : env ptv = rN pt) (h2 : env iv = rN xs.length)
    (hm : xs.length % P ≠ 0) (hlt : xs.length < P * P) (h32 : W.length < 2 ^ 32) :
    ∃ W', Mach.BExec (setEl ptv iv xv t) ⟨env, H, [W]⟩ ⟨env.set t (rN (ent W pt (xs.length / P))), H, [W']⟩ ∧
      W'.length = W.length ∧ (∀ q, ¬ InPages (pagesOf W pt xs.length) q → W'[q]? = W[q]?) ∧
      ArrAt W' pt (xs ++ [env xv]) ∧ pagesOf W' pt (xs ++ [env xv]).length = pagesOf W pt xs.length := by
  have hjl : xs.length < 2 ^ 32 := by rw [P] at hlt; omega
  have hpt := hA.pt_in
  obtain ⟨hnp1, hi⟩ := npages_succ_of_mod_ne hm
  have hnp := npages_le (Nat.le_of_lt hlt)
  have hix := ptIx_den (env := env) h1 h2 hjl (by omega)
  have hl1 : pt + xs.length / P < W.length := by have := npages_le hA.len; omega
  have e1 := Mach.BExec.load64 (v := t) (b := 0) (i := ptIx ptv iv) (σ := ⟨env, H, [W]⟩) (by simp)
    (by simp only [List.getElem_cons_zero]; rw [hix]; exact hl1)
  simp only [List.getElem_cons_zero, hix, ent_rN hl1] at e1
  have he := hA.ents _ hi
  generalize hE : ent W pt (xs.length / P) = E at he e1
  have hix2 := elIx_den (env := env.set t (rN E)) (ev := t) (jv := iv) set_eq
    (by rw [set_ne (Ne.symm hv.2.1)]; exact h2) hjl (by omega)
  have hl2 : E + xs.length % P < W.length := by have := mod_lt_P xs.length; omega
  have e2 := store64_at (σ := ⟨env.set t (rN E), H, [W]⟩) rfl (elIx t iv) (.var xv) (E + xs.length % P) hix2 hl2
  simp only [Mach.BExp.denote, set_ne (Ne.symm hv.2.2)] at e2
  have hin : InPages (pagesOf W pt xs.length) (E + xs.length % P) :=
    ⟨E, List.mem_cons_of_mem _ (List.mem_map.2 ⟨xs.length / P, List.mem_range.2 hi, hE⟩), by omega,
      by have := mod_lt_P xs.length; omega⟩
  have hnd := hA.nd
  have hptE : pt ≠ E := hE ▸ pt_ne_ent hnd hi
  have hpte : ∀ i, i < P → pt + i ≠ E + xs.length % P := by
    intro i hi' e
    rcases page_apart hA.pt_al he.1 hptE with h | h <;> have := mod_lt_P xs.length <;> omega
  have hent : ∀ i, i < npages xs.length → ent (W.set (E + xs.length % P) (env xv)) pt i = ent W pt i := fun i hi' => by
    unfold ent; rw [List.getElem?_set_ne (Ne.symm (hpte i (by omega)))]
  have hpg : pagesOf (W.set (E + xs.length % P) (env xv)) pt (xs.length + 1) = pagesOf W pt xs.length := by
    unfold pagesOf; rw [hnp1]; congr 1
    exact List.map_congr_left fun i hi' => hent i (List.mem_range.1 hi')
  refine ⟨_, .seq e1 e2, by simp, fun q hq => ?_, ⟨hA.pt_al, by simpa using hpt, by simp; omega,
    fun i hi' => by simp only [List.length_append, List.length_cons, List.length_nil, hnp1] at hi'
                    rw [hent i hi', List.length_set]; exact hA.ents i hi',
    fun j' hj' => ?_, by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hpg]; exact hnd⟩,
    by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hpg]⟩
  · rw [List.getElem?_set_ne]; intro e; subst e; exact hq hin
  · simp only [List.length_append, List.length_cons, List.length_nil] at hj'
    have hi2 : j' / P < npages xs.length := by rw [← hnp1]; exact div_lt_npages hj'
    rw [hent _ hi2, List.getElem?_set]
    by_cases hjj : j' = xs.length
    · subst hjj; rw [if_pos (by rw [hE]), if_pos (by omega)]
      rw [List.getElem?_append_right (by omega)]; simp
    · have hj2 : j' < xs.length := by omega
      have hne : E + xs.length % P ≠ ent W pt (j' / P) + j' % P := by
        intro e
        have hm1 := mod_lt_P xs.length; have hm2 := mod_lt_P j'
        have he2 := hA.ents _ hi2
        by_cases hq : xs.length / P = j' / P
        · rw [← hE, hq] at e
          have : xs.length % P = j' % P := by omega
          exact hjj (by rw [← Nat.div_add_mod j' P, ← Nat.div_add_mod xs.length P, hq, this])
        · have : E ≠ ent W pt (j' / P) := fun e' => hq (ent_inj hnd hi hi2 (hE.trans e'))
          rcases page_apart he.1 he2.1 this with h | h <;> omega
      rw [if_neg hne, List.getElem?_append_left (by omega)]; exact hA.els j' (by omega)

theorem div_lt_P {n : Nat} (h : n < P * P) : n / P < P := Nat.div_lt_of_lt_mul h

theorem eq_and_mask {n : Nat} (h : n < 2 ^ 64) :
    Op.eval .eq (Op.eval .and (rN n) (BitVec.ofNat 64 (P - 1))) 0 = if n % P = 0 then 1 else 0 := by
  rw [and_mask h]
  simp only [Op.eval]
  have : (rN (n % P) = 0) ↔ n % P = 0 := by
    have hP : P = 1024 := rfl
    rw [show (0 : BitVec 64) = rN 0 from rfl, rN_inj (by have := mod_lt_P n; omega) (by decide)]
  by_cases hm : n % P = 0
  · rw [if_pos (this.2 hm), if_pos hm]
  · rw [if_neg (fun e => hm (this.1 e)), if_neg hm]

/-- the variables of a push: below its temporaries, not the pool's -/
def PushVars (ptv sv xv t : Nat) : Prop :=
  8 ≤ ptv ∧ 8 ≤ sv ∧ 8 ≤ xv ∧ ptv < t ∧ sv < t ∧ xv < t ∧ sv ≠ ptv ∧ sv ≠ xv

set_option maxHeartbeats 4000000 in
/-- **push**: the element lands at the end (a page from the pool when the last page is full), or, exactly
when a page was needed and all `C` pages are in use, `vOk := 0` -/
theorem pushEl_ok {C : Nat} {env : Mach.BEnv} {W : W64} {pt : Nat} {xs : W64} {others : List (Nat × W64)}
    (H : Heap) (h : Store C env W ((pt, xs) :: others)) (ptv sv xv t : Nat) (hv : PushVars ptv sv xv t)
    (h1 : env ptv = rN pt) (h2 : env sv = rN xs.length) (hlt : xs.length < P * P) (hok : env vOk = 1) :
    ∃ env' W', Mach.BExec (pushEl ptv sv xv t) ⟨env, H, [W]⟩ ⟨env', H, [W']⟩ ∧
      (∀ j, j ≠ sv → j ≠ vFh → j ≠ vBump → j ≠ vOk → (j < t ∨ t + 7 ≤ j) → env' j = env j) ∧
      ((env' vOk = 1 ∧ env' sv = rN (xs.length + 1) ∧ Store C env' W' ((pt, xs ++ [env xv]) :: others)) ∨
        (env' vOk = 0 ∧ xs.length % P = 0 ∧ pageCount ((pt, xs) :: others) = C)) := by
  obtain ⟨h8p, h8s, h8x, hpt, hst, hxt, hsp, hsx⟩ := hv
  obtain ⟨hp, ha⟩ := h
  have hA : ArrAt W pt xs := ha (pt, xs) (List.mem_cons_self ..)
  have h32 := hp.wlen.2
  have hCW := hp.wlen.1
  have hjl : xs.length < 2 ^ 32 := by rw [P] at hlt; omega
  have hpv : vCap = 4 ∧ vBump = 5 ∧ vFh = 6 ∧ vOk = 7 := ⟨rfl, rfl, rfl, rfl⟩
  let c : BitVec 64 := if xs.length % P = 0 then 1 else 0
  let e2 := env.set (t + 2) c
  have ha2 : Mach.BExec (.assign (t + 2) (.bin .eq (.bin .and (.var sv) (.const (BitVec.ofNat 64 (P - 1)))) (.const 0)))
      ⟨env, H, [W]⟩ ⟨e2, H, [W]⟩ := by
    have := Mach.BExec.assign (v := t + 2)
      (e := .bin .eq (.bin .and (.var sv) (.const (BitVec.ofNat 64 (P - 1)))) (.const 0)) (σ := ⟨env, H, [W]⟩)
    simp only [Mach.BExp.denote, h2, eq_and_mask (show xs.length < 2 ^ 64 by omega)] at this; exact this
  let e3 := e2.set (t + 3) (c ^^^ 1)
  have ha3 : Mach.BExec (.assign (t + 3) (.bin .xor (.var (t + 2)) (.const 1))) ⟨e2, H, [W]⟩ ⟨e3, H, [W]⟩ := by
    have := Mach.BExec.assign (v := t + 3) (e := .bin .xor (.var (t + 2)) (.const 1)) (σ := ⟨e2, H, [W]⟩)
    simp only [Mach.BExp.denote, Op.eval, e2, set_eq] at this; exact this
  have k3 : ∀ j, j ≠ t + 2 → j ≠ t + 3 → e3 j = env j := fun j a b => by simp only [e3, e2, set_ne a, set_ne b]
  by_cases hm : xs.length % P = 0
  · -- a new data page
    have hc : c = 1 := by simp only [c, if_pos hm]
    have hz3 : e3 (t + 3) = 0 := by simp only [e3, set_eq, hc]; decide
    have hnz2 : e3 (t + 2) ≠ 0 := by simp only [e3, set_ne (show t + 2 ≠ t + 3 by omega), e2, set_eq, hc]; decide
    have hp3 : PoolInv C e3 W (owned W ((pt, xs) :: others)) :=
      hp.frame (fun j hj => k3 j (by rcases hj with rfl | rfl | rfl <;> simp only [vCap, vBump, vFh] <;> omega)
        (by rcases hj with rfl | rfl | rfl <;> simp only [vCap, vBump, vFh] <;> omega)) rfl (fun _ _ => rfl)
    obtain ⟨env1, e4, k4, r4⟩ := alloc_ok H hp3 (t + 4) t (by omega) (by omega) ⟨by omega, by omega⟩
    have k41 : ∀ j, j ≠ t + 2 → j ≠ t + 3 → ¬ AllocVars (t + 4) t j → env1 j = env j := fun j a b c' => by
      rw [k4 j c', k3 j a b]
    have hptv1 : env1 ptv = rN pt := by
      rw [k41 ptv (by omega) (by omega) (by simp only [AllocVars, vFh, vBump, vOk]; omega)]; exact h1
    have hsv1 : env1 sv = rN xs.length := by
      rw [k41 sv (by omega) (by omega) (by simp only [AllocVars, vFh, vBump, vOk]; omega)]; exact h2
    have hix := ptIx_den (env := env1) hptv1 hsv1 hjl (by have := hA.pt_in; omega)
    have hnp := npages_le (Nat.le_of_lt hlt)
    obtain ⟨hnp1, hnpe⟩ := npages_succ_of_mod hm
    have hdP := div_lt_P hlt
    have hl1 : pt + xs.length / P < W.length := by have := hA.pt_in; omega
    have e5 := store64_at (σ := ⟨env1, H, [W]⟩) rfl (ptIx ptv sv) (.var (t + 4)) (pt + xs.length / P) hix hl1
    simp only [Mach.BExp.denote] at e5
    rcases r4 with ⟨hlt4, hok4, r, hr, hra, hrc, hru, hp4⟩ | ⟨heq4, hok4⟩
    · -- the page `r`
      have hok1 : env1 vOk = 1 := by rw [hok4, k3 _ (by simp only [vOk]; omega) (by simp only [vOk]; omega)]; exact hok
      let W1 := W.set (pt + xs.length / P) (rN r)
      have hrW : r + P ≤ W1.length := by simp only [W1, List.length_set]; have := hp.wlen.1; omega
      let env5 := env1.set (t + 5) (env1 vOk)
      have hnz5 : env5 (t + 5) ≠ 0 := by simp only [env5, set_eq, hok1]; decide
      have e6 := store64_at (σ := ⟨env5, H, [W1]⟩) rfl (.var (t + 4)) (.var xv) r
        (by simp only [Mach.BExp.denote, env5, set_ne (show t + 4 ≠ t + 5 by omega), hr]
            exact rN_toNat (by omega)) (by have := P_pos; omega)
      simp only [Mach.BExp.denote] at e6
      have hxv5 : env5 xv = env xv := by
        simp only [env5, set_ne (show xv ≠ t + 5 by omega)]
        rw [k41 xv (by omega) (by omega) (by simp only [AllocVars, vFh, vBump, vOk]; omega)]
      rw [hxv5] at e6
      let W2 := W1.set r (env xv)
      let env6 := env5.set sv ((Mach.BExp.bin .add (.var sv) (.const 1)).denote env5)
      have hsv6 : env6 sv = rN (xs.length + 1) := by
        simp only [env6, set_eq, Mach.BExp.denote, Op.eval, env5, set_ne (show sv ≠ t + 5 by omega), hsv1, rN_add]
        rfl
      let env7 := env6.set (t + 5) 0
      have hw5 : Mach.BExec (when (t + 5) (.seq (.store64 0 (.var (t + 4)) (.var xv))
              (.assign sv (.bin .add (.var sv) (.const 1))))) ⟨env5, H, [W1]⟩ ⟨env7, H, [W2]⟩ :=
        when_true hnz5 (.seq e6 (Mach.BExec.assign (v := sv) (e := .bin .add (.var sv) (.const 1))))
      have hinner : Mach.BExec (.seq (allocCode (t + 4) t)
          (.seq (.store64 0 (ptIx ptv sv) (.var (t + 4)))
          (.seq (.assign (t + 5) (.var vOk))
            (when (t + 5) (.seq (.store64 0 (.var (t + 4)) (.var xv))
              (.assign sv (.bin .add (.var sv) (.const 1))))))))
          ⟨e3, H, [W]⟩ ⟨env7, H, [W2]⟩ := by
        have ha5 : Mach.BExec (.assign (t + 5) (.var vOk)) ⟨env1, H, [W1]⟩ ⟨env5, H, [W1]⟩ := .assign
        refine .seq e4 (.seq ?_ (.seq ha5 hw5))
        simp only [hr] at e5; exact e5
      have hw2 := when_true hnz2 hinner
      let env8 := env7.set (t + 2) 0
      have hz8 : env8 (t + 3) = 0 := by
        simp only [env8, env7, env6, env5, set_ne (show t + 3 ≠ t + 2 by omega), set_ne (show t + 3 ≠ t + 5 by omega),
          set_ne (show t + 3 ≠ sv by omega)]
        rw [k4 _ (by simp only [AllocVars, vFh, vBump, vOk]; omega)]; exact hz3
      have hall : Mach.BExec (pushEl ptv sv xv t) ⟨env, H, [W]⟩ ⟨env8, H, [W2]⟩ :=
        .seq ha2 (.seq ha3 (.seq hw2 (when_false hz8)))
      have k8 : ∀ j, j ≠ sv → j ≠ vFh → j ≠ vBump → j ≠ vOk → (j < t ∨ t + 7 ≤ j) → env8 j = env j := by
        intro j a b c' d e
        simp only [env8, env7, env6, env5, set_ne (show j ≠ t + 2 by omega), set_ne (show j ≠ t + 5 by omega),
          set_ne a]
        exact k41 j (by omega) (by omega) (by simp only [AllocVars]; omega)
      -- the new page table entry and the array
      have hrne : ∀ i, i < P → pt + i ≠ r := by
        intro i hi e
        have hptin : pt ∈ owned W ((pt, xs) :: others) := by rw [owned_cons]; simp [pagesOf]
        have hne : pt ≠ r := fun e' => hru (e' ▸ hptin)
        rcases page_apart hA.pt_al hra hne with h | h <;> omega
      have hW2pt : ∀ i, i < P → W2[pt + i]? = W1[pt + i]? := fun i hi => by
        simp only [W2]; rw [List.getElem?_set_ne (Ne.symm (hrne i hi))]
      have hent2 : ∀ i, i < npages xs.length → ent W2 pt i = ent W pt i := fun i hi => by
        unfold ent; rw [hW2pt i (by omega)]; simp only [W1]; rw [List.getElem?_set_ne (by rw [hnpe] at hi; omega)]
      have hentn : ent W2 pt (xs.length / P) = r := by
        unfold ent; rw [hW2pt _ (by rw [← hnpe]; omega)]; simp only [W1]
        rw [List.getElem?_set_self (by omega)]; simp only [Option.getD_some]; exact rN_toNat (by omega)
      have hpg2 : pagesOf W2 pt (xs.length + 1) = pagesOf W pt xs.length ++ [r] := by
        unfold pagesOf
        rw [hnp1, List.range_succ, List.map_append, List.cons_append]; congr 1
        rw [List.map_congr_left fun i hi => hent2 i (List.mem_range.1 hi)]
        simp only [List.map_cons, List.map_nil, hnpe] at hentn ⊢; rw [hentn]
      have hnd4 := hp4.nodup
      rw [owned_cons] at hnd4
      have hnd2 : (pagesOf W pt xs.length ++ [r]).Nodup := by
        have : (r :: pagesOf W pt xs.length).Nodup := (List.nodup_cons.1 hnd4).1 |> fun h' =>
          List.nodup_cons.2 ⟨fun hm' => h' (List.mem_append_left _ hm'),
            (List.nodup_append.1 (List.nodup_cons.1 hnd4).2).1⟩
        exact (List.perm_append_singleton r _).nodup_iff.2 this
      have hAr : ArrAt W2 pt (xs ++ [env xv]) := by
        refine ⟨hA.pt_al, by simp only [W2, W1, List.length_set]; exact hA.pt_in, by simp; omega,
          fun i hi => ?_, fun j hj => ?_,
          (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hpg2]; exact hnd2)⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, hnp1] at hi
          simp only [W2, W1, List.length_set]
          by_cases hi' : i < npages xs.length
          · rw [hent2 i hi']; exact hA.ents i hi'
          · have : i = xs.length / P := by omega
            subst this; rw [hentn]; exact ⟨hra, by have := hp.wlen.1; omega⟩
        · simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hjn : j = xs.length
          · subst hjn
            rw [hentn, show xs.length % P = 0 from hm, Nat.add_zero, List.getElem?_append_right (by omega)]
            simp only [W2]; rw [List.getElem?_set_self (by simp only [W1, List.length_set]; omega)]; simp
          · have hj' : j < xs.length := by omega
            have hi := div_lt_npages hj'
            rw [hent2 _ hi, List.getElem?_append_left hj']
            have he := hA.ents _ hi
            have hm2 := mod_lt_P j
            have hne1 : ent W pt (j / P) + j % P ≠ r := by
              intro e
              have hin : ent W pt (j / P) ∈ owned W ((pt, xs) :: others) := by
                rw [owned_cons]; exact List.mem_append_left _ (List.mem_cons_of_mem _
                  (List.mem_map.2 ⟨j / P, List.mem_range.2 hi, rfl⟩))
              have hne : ent W pt (j / P) ≠ r := fun e' => hru (e' ▸ hin)
              rcases page_apart he.1 hra hne with h | h <;> omega
            have hne2 : ent W pt (j / P) + j % P ≠ pt + xs.length / P := by
              intro e
              have hne : pt ≠ ent W pt (j / P) := pt_ne_ent hA.nd hi
              rcases page_apart hA.pt_al he.1 hne with h | h <;> omega
            simp only [W2, W1]
            rw [List.getElem?_set_ne (Ne.symm hne1), List.getElem?_set_ne (Ne.symm hne2)]
            exact hA.els j hj'
      -- the others and the pool
      have hS : ∀ q, ¬ InPages (pagesOf W pt xs.length ++ [r]) q → W2[q]? = W[q]? := by
        intro q hq
        have hq1 : q ≠ r := fun e => hq ⟨r, by simp, by omega, by have := P_pos; omega⟩
        have hq2 : q ≠ pt + xs.length / P := fun e => hq ⟨pt, by simp [pagesOf], by omega, by omega⟩
        simp only [W2, W1]; rw [List.getElem?_set_ne (Ne.symm hq1), List.getElem?_set_ne (Ne.symm hq2)]
      have hl2 : W2.length = W.length := by simp [W2, W1]
      have eP : (owned W others ++ (pagesOf W pt xs.length ++ [r])).Perm
          (r :: (pagesOf W pt xs.length ++ owned W others)) := by
        rw [← List.append_assoc]
        exact ((List.perm_append_comm).append_right [r]).trans (List.perm_append_singleton _ _)
      have hnd5 := eP.nodup_iff.2 hnd4
      obtain ⟨hko, hko2⟩ := keep_others hp4 (others := others) (S := pagesOf W pt xs.length ++ [r]) hnd5
        (fun p hp' => by rw [owned_cons]; exact eP.subset hp') (fun a h => ha a (List.mem_cons_of_mem _ h)) hl2 hS
      have hp8 : PoolInv C env8 W2 (r :: owned W ((pt, xs) :: others)) := by
        refine hp4.frame (fun j hj => ?_) hl2 (fun q hq => ?_)
        · simp only [env8, env7, env6, env5]
          rcases hj with rfl | rfl | rfl <;>
            rw [set_ne (by simp only [vCap, vBump, vFh]; omega), set_ne (by simp only [vCap, vBump, vFh]; omega),
              set_ne (by simp only [vCap, vBump, vFh]; omega), set_ne (by simp only [vCap, vBump, vFh]; omega)]
        · apply hS; rintro ⟨p, hp', hp1, hp2⟩
          have := hq p (by rw [owned_cons]; exact (eP.subset (List.mem_append_right _ hp')))
          omega
      refine ⟨env8, W2, hall, k8, .inl ⟨?_, ?_, ?_, fun a h => ?_⟩⟩
      · simp only [env8, env7, env6, env5]
        rw [set_ne (by simp only [vOk]; omega), set_ne (by simp only [vOk]; omega),
          set_ne (by simp only [vOk]; omega), set_ne (by simp only [vOk]; omega)]; exact hok1
      · simp only [env8, env7, set_ne (show sv ≠ t + 2 by omega), set_ne (show sv ≠ t + 5 by omega)]; exact hsv6
      · refine hp8.perm ?_
        rw [owned_cons, owned_cons, hko2]
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [hpg2]
        exact (eP.symm.trans (List.perm_append_comm.trans (by rw [List.append_assoc])))
      · rcases List.mem_cons.1 h with rfl | h
        · exact hAr
        · exact (hko a h).1
    · -- no page left
      have k1' := k41
      let W1 := W.set (pt + xs.length / P) (env1 (t + 4))
      let env5 := env1.set (t + 5) (env1 vOk)
      have hz5 : env5 (t + 5) = 0 := by simp only [env5, set_eq, hok4]
      have hinner : Mach.BExec (.seq (allocCode (t + 4) t)
          (.seq (.store64 0 (ptIx ptv sv) (.var (t + 4)))
          (.seq (.assign (t + 5) (.var vOk))
            (when (t + 5) (.seq (.store64 0 (.var (t + 4)) (.var xv))
              (.assign sv (.bin .add (.var sv) (.const 1))))))))
          ⟨e3, H, [W]⟩ ⟨env5, H, [W1]⟩ :=
        .seq e4 (.seq e5 (.seq .assign (when_false hz5)))
      have hw2 := when_true hnz2 hinner
      let env8 := env5.set (t + 2) 0
      have hz8 : env8 (t + 3) = 0 := by
        simp only [env8, env5, set_ne (show t + 3 ≠ t + 2 by omega), set_ne (show t + 3 ≠ t + 5 by omega)]
        rw [k4 _ (by simp only [AllocVars, vFh, vBump, vOk]; omega)]; exact hz3
      refine ⟨env8, W1, .seq ha2 (.seq ha3 (.seq hw2 (when_false hz8))), fun j a b c' d e => ?_,
        .inr ⟨?_, hm, by rw [← owned_length]; exact heq4⟩⟩
      · simp only [env8, env5, set_ne (show j ≠ t + 2 by omega), set_ne (show j ≠ t + 5 by omega)]
        exact k41 j (by omega) (by omega) (by simp only [AllocVars]; omega)
      · simp only [env8, env5, set_ne (show vOk ≠ t + 2 by simp only [vOk]; omega),
          set_ne (show vOk ≠ t + 5 by simp only [vOk]; omega)]; exact hok4
  · -- room in the last page
    have hc : c = 0 := by simp only [c, if_neg hm]
    have hz2 : e3 (t + 2) = 0 := by simp only [e3, set_ne (show t + 2 ≠ t + 3 by omega), e2, set_eq, hc]
    have hnz3 : e3 (t + 3) ≠ 0 := by simp only [e3, set_eq, hc]; decide
    have hptv3 : e3 ptv = rN pt := by rw [k3 _ (by omega) (by omega)]; exact h1
    have hsv3 : e3 sv = rN xs.length := by rw [k3 _ (by omega) (by omega)]; exact h2
    obtain ⟨W1, e5, hl1, hw1, hA1, hpg1⟩ := setEl_end_ok hA H e3 ptv sv xv (t + 6) ⟨by omega, by omega, by omega⟩
      hptv3 hsv3 hm hlt h32
    have hxv3 : e3 xv = env xv := k3 _ (by omega) (by omega)
    rw [hxv3] at hA1 hpg1
    let env6 := e3.set (t + 6) (rN (ent W pt (xs.length / P)))
    let env7 := env6.set sv ((Mach.BExp.bin .add (.var sv) (.const 1)).denote env6)
    have hsv7 : env7 sv = rN (xs.length + 1) := by
      simp only [env7, set_eq, Mach.BExp.denote, Op.eval, env6, set_ne (show sv ≠ t + 6 by omega), hsv3, rN_add]; rfl
    have hw3 := when_true hnz3 (.seq e5 (Mach.BExec.assign (v := sv) (e := .bin .add (.var sv) (.const 1))))
    let env8 := env7.set (t + 3) 0
    have k8 : ∀ j, j ≠ sv → (j < t ∨ t + 7 ≤ j) → env8 j = env j := fun j a b => by
      simp only [env8, env7, env6, set_ne (show j ≠ t + 3 by omega), set_ne a, set_ne (show j ≠ t + 6 by omega)]
      exact k3 j (by omega) (by omega)
    refine ⟨env8, W1, .seq ha2 (.seq ha3 (.seq (when_false hz2) hw3)), fun j a _ _ _ e => k8 j a e,
      .inl ⟨by rw [k8 _ (by simp only [vOk]; omega) (by simp only [vOk]; omega)]; exact hok,
        by simp only [env8, set_ne (show sv ≠ t + 3 by omega)]; exact hsv7, ?_⟩⟩
    have := Store.write (pre := []) (env' := env8) ⟨hp, ha⟩
      (fun j hj => k8 j (by rcases hj with rfl | rfl | rfl <;> simp only [vCap, vBump, vFh] <;> omega)
        (by rcases hj with rfl | rfl | rfl <;> simp only [vCap, vBump, vFh] <;> omega)) hl1 hw1 hA1 hpg1
    simpa using this

/-! ## Freeing an array -/

/-- the loop over the data pages: `i` in `t + 1`, their number in `t`, the page in `t + 2` -/
def freeLoop (ptv t : Nat) : MS :=
  .loop (.bin .ult (.var (t + 1)) (.var t))
    (.seq (.load64 (t + 2) 0 (.bin .add (.var ptv) (.var (t + 1))))
      (.seq (freeCode (t + 2)) (.assign (t + 1) (.bin .add (.var (t + 1)) (.const 1)))))

/-- every page of the array (size in `sv`, page table in `ptv`) back to the free list -/
def freeArr (ptv sv t : Nat) : MS :=
  .seq (.assign t (.bin .lshr (.bin .add (.var sv) (.const (BitVec.ofNat 64 (P - 1)))) (.const (BitVec.ofNat 64 lg))))
  (.seq (.assign (t + 1) (.const 0)) (.seq (freeLoop ptv t) (freeCode ptv)))

theorem perm_swap3 {a b : Nat} {l m : List Nat} : (a :: (b :: l ++ m)).Perm (b :: (a :: l ++ m)) :=
  List.Perm.swap b a _

set_option maxHeartbeats 2000000 in
theorem freeLoop_ok {C : Nat} {W0 : W64} {pt : Nat} {xs : W64} {others : List (Nat × W64)} (H : Heap)
    (hA : ArrAt W0 pt xs) (hnd0 : (owned W0 ((pt, xs) :: others)).Nodup) (ptv t : Nat)
    (hv : 8 ≤ t ∧ 8 ≤ ptv ∧ ptv < t) :
    ∀ m i (env : Mach.BEnv) (W : W64), npages xs.length - i = m → i ≤ npages xs.length →
      PoolInv C env W (pt :: ((List.range (npages xs.length)).drop i).map (ent W0 pt) ++ owned W0 others) →
      (∀ k, k < P → W[pt + k]? = W0[pt + k]?) →
      (∀ a ∈ others, ArrAt W a.1 a.2) → owned W others = owned W0 others →
      env ptv = rN pt → env t = rN (npages xs.length) → env (t + 1) = rN i → W.length = W0.length →
      ∃ env' W', Mach.BExec (freeLoop ptv t) ⟨env, H, [W]⟩ ⟨env', H, [W']⟩ ∧
        PoolInv C env' W' (pt :: owned W0 others) ∧ (∀ k, k < P → W'[pt + k]? = W0[pt + k]?) ∧
        (∀ a ∈ others, ArrAt W' a.1 a.2) ∧ owned W' others = owned W0 others ∧
        (∀ j, j ≠ t + 1 → j ≠ t + 2 → j ≠ vFh → env' j = env j) ∧ W'.length = W0.length
  | 0, i, env, W, hm, hi, hp, hpt', ho, ho2, h1, h2, h3, hl => by
    have hin : i = npages xs.length := by omega
    subst hin
    rw [List.drop_eq_nil_of_le (by simp)] at hp
    refine ⟨env, W, .loopF ?_, by simpa using hp, hpt', ho, ho2, fun _ _ _ _ => rfl, hl⟩
    simp only [Mach.BExp.denote, Op.eval, h2, h3]; simp
  | m + 1, i, env, W, hm, hi, hp, hpt', ho, ho2, h1, h2, h3, hl => by
    have hnp := npages_le hA.len
    have hP : P = 1024 := rfl
    have hil : i < npages xs.length := by omega
    have hW := hp.wlen
    have hlt : (Mach.BExp.bin .ult (.var (t + 1)) (.var t)).denote env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, h2, h3,
        rN_lt (show i < 2 ^ 64 by omega) (show npages xs.length < 2 ^ 64 by omega), if_pos hil]; decide
    -- load entry `i`
    have hix : ((Mach.BExp.bin .add (.var ptv) (.var (t + 1))).denote env).toNat = pt + i := by
      simp only [Mach.BExp.denote, Op.eval, h1, h3, ← rN_add]; exact rN_toNat (by have := hA.pt_in; omega)
    have hpl : pt + i < W.length := by have := hA.pt_in; rw [hP] at hnp; omega
    have e1 := Mach.BExec.load64 (v := t + 2) (b := 0) (i := .bin .add (.var ptv) (.var (t + 1)))
      (σ := ⟨env, H, [W]⟩) (by simp) (by simp only [List.getElem_cons_zero]; rw [hix]; exact hpl)
    have hWi : W[pt + i] = rN (ent W0 pt i) := by
      have e := hpt' i (by omega)
      rw [List.getElem?_eq_getElem hpl] at e
      unfold ent; rw [← e]; simp [rN]
    simp only [List.getElem_cons_zero, hix, hWi] at e1
    let env1 := env.set (t + 2) (rN (ent W0 pt i))
    have hdrop : (List.range (npages xs.length)).drop i = i :: (List.range (npages xs.length)).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hil)]; simp
    rw [hdrop, List.map_cons] at hp
    have hp1 : PoolInv C env1 W (pt :: (ent W0 pt i :: ((List.range (npages xs.length)).drop (i + 1)).map
        (ent W0 pt) ++ owned W0 others)) :=
      hp.frame (fun j hj => by rcases hj with rfl | rfl | rfl <;> simp only [env1] <;>
        rw [set_ne (by simp only [vCap, vBump, vFh]; omega)]) rfl (fun _ _ => rfl)
    obtain ⟨e2, hp2⟩ := free_ok H hp1 (List.Perm.swap _ _ _) (t + 2) set_eq
    let W2 := W.set (ent W0 pt i) (env1 vFh)
    let env2 := env1.set vFh (rN (ent W0 pt i))
    let env3 := env2.set (t + 1) ((Mach.BExp.bin .add (.var (t + 1)) (.const 1)).denote env2)
    -- the page written is entry `i`'s page, not the page table, not another array's
    have hnd := hp.nodup
    have hE := hA.ents i hil
    have hpte : pt ≠ ent W0 pt i := pt_ne_ent hA.nd hil
    have hptk : ∀ k, k < P → ¬ (ent W0 pt i ≤ pt + k ∧ pt + k < ent W0 pt i + P) := by
      intro k hk e; rcases page_apart hA.pt_al hE.1 hpte with h | h <;> omega
    have hS : ∀ q, ¬ InPages [ent W0 pt i] q → W2[q]? = W[q]? := by
      intro q hq; simp only [W2]; rw [List.getElem?_set_ne]; intro e
      exact hq ⟨ent W0 pt i, by simp, by omega, by omega⟩
    have hU : (owned W others ++ [ent W0 pt i]).Nodup := by
      rw [ho2]
      have hsub : (ent W0 pt i :: owned W0 others).Sublist
          (pt :: (ent W0 pt i :: ((List.range (npages xs.length)).drop (i + 1)).map (ent W0 pt) ++ owned W0 others)) :=
        .cons pt (.cons₂ _ (List.sublist_append_right _ _))
      exact (List.perm_append_singleton _ _).nodup_iff.2 (hsub.nodup hnd)
    obtain ⟨hko, hko2⟩ := keep_others hp (others := others) hU (fun p hp' => by
      rw [ho2] at hp'
      rcases List.mem_append.1 hp' with h | h
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h))
      · simp at h; subst h; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)) ho (by simp [W2]) hS
    have h1' : env3 ptv = rN pt := by
      simp only [env3, env2, env1, set_ne (show ptv ≠ t + 1 by omega), set_ne (show ptv ≠ vFh by simp only [vFh]; omega),
        set_ne (show ptv ≠ t + 2 by omega)]; exact h1
    have h2' : env3 t = rN (npages xs.length) := by
      simp only [env3, env2, env1, set_ne (show t ≠ t + 1 by omega), set_ne (show t ≠ vFh by simp only [vFh]; omega),
        set_ne (show t ≠ t + 2 by omega)]; exact h2
    have h3' : env3 (t + 1) = rN (i + 1) := by
      simp only [env3, set_eq, Mach.BExp.denote, Op.eval, env2, env1, set_ne (show t + 1 ≠ vFh by simp only [vFh]; omega),
        set_ne (show t + 1 ≠ t + 2 by omega), h3, rN_add]; rfl
    have hp3 : PoolInv C env3 W2 (pt :: ((List.range (npages xs.length)).drop (i + 1)).map (ent W0 pt) ++
        owned W0 others) :=
      hp2.frame (fun j hj => by rcases hj with rfl | rfl | rfl <;> simp only [env3] <;>
        rw [set_ne (by simp only [vCap, vBump, vFh]; omega)]) rfl (fun _ _ => rfl)
    obtain ⟨env', W', e3, r1, r2, r3, r4, r5, r6⟩ := freeLoop_ok H hA hnd0 ptv t hv m (i + 1) env3 W2 (by omega)
      (by omega) hp3 (fun k hk => (hS (pt + k) (fun ⟨p, hp', a, b⟩ => by
          simp at hp'; subst hp'; exact hptk k hk ⟨a, b⟩)).trans (hpt' k hk)) (fun a h => (hko a h).1) (by rw [hko2, ho2]) h1' h2' h3' (by simp [W2, hl])
    refine ⟨env', W', .loopT hlt (.seq e1 (.seq e2 .assign)) e3, r1, r2, r3, r4, fun j a b c => ?_, r6⟩
    rw [r5 j a b c]; simp only [env3, env2, env1, set_ne a, set_ne b, set_ne c]

set_option maxHeartbeats 1000000 in
/-- **freeing**: every page of the array goes back to the free list; the other arrays stay -/
theorem freeArr_ok {C : Nat} {env : Mach.BEnv} {W : W64} {pt : Nat} {xs : W64} {others : List (Nat × W64)}
    (H : Heap) (h : Store C env W ((pt, xs) :: others)) (ptv sv t : Nat)
    (hv : 8 ≤ t ∧ 8 ≤ ptv ∧ ptv < t ∧ sv < t) (h1 : env ptv = rN pt) (h2 : env sv = rN xs.length) :
    ∃ env' W', Mach.BExec (freeArr ptv sv t) ⟨env, H, [W]⟩ ⟨env', H, [W']⟩ ∧ Store C env' W' others ∧
      (∀ j, j ≠ t → j ≠ t + 1 → j ≠ t + 2 → j ≠ vFh → env' j = env j) := by
  obtain ⟨hp, ha⟩ := h
  have hA : ArrAt W pt xs := ha (pt, xs) (List.mem_cons_self ..)
  have hW := hp.wlen
  have hnl : xs.length < 2 ^ 32 := by have := hA.len; rw [P] at this; omega
  let env1 := env.set t (rN (npages xs.length))
  have e1 : Mach.BExec (.assign t (.bin .lshr (.bin .add (.var sv) (.const (BitVec.ofNat 64 (P - 1))))
      (.const (BitVec.ofNat 64 lg)))) ⟨env, H, [W]⟩ ⟨env1, H, [W]⟩ := by
    have := Mach.BExec.assign (v := t) (e := .bin .lshr (.bin .add (.var sv) (.const (BitVec.ofNat 64 (P - 1))))
      (.const (BitVec.ofNat 64 lg))) (σ := ⟨env, H, [W]⟩)
    simp only [Mach.BExp.denote, h2] at this
    rw [show BitVec.ofNat 64 (P - 1) = rN (P - 1) from rfl, add_rN, lshr_lg (by rw [P]; omega)] at this
    exact this
  let env2 := env1.set (t + 1) (rN 0)
  have e2 : Mach.BExec (.assign (t + 1) (.const 0)) ⟨env1, H, [W]⟩ ⟨env2, H, [W]⟩ := .assign
  have hp2 : PoolInv C env2 W (pt :: ((List.range (npages xs.length)).drop 0).map (ent W pt) ++ owned W others) := by
    have := hp.frame (env' := env2) (fun j hj => by
      rcases hj with rfl | rfl | rfl <;> simp only [env2, env1] <;>
        rw [set_ne (by simp only [vCap, vBump, vFh]; omega), set_ne (by simp only [vCap, vBump, vFh]; omega)])
      rfl (fun _ _ => rfl)
    rw [owned_cons] at this; simpa [pagesOf] using this
  have hnd : (owned W ((pt, xs) :: others)).Nodup := hp.nodup
  obtain ⟨env3, W3, e3, hp3, hpt3, ho3, ho3', hk3, hl3⟩ := freeLoop_ok H hA hnd ptv t ⟨hv.1, hv.2.1, hv.2.2.1⟩ _ 0
    env2 W rfl (Nat.zero_le _) hp2 (fun _ _ => rfl) (fun a h => ha a (List.mem_cons_of_mem _ h)) rfl
    (by simp only [env2, env1, set_ne (show ptv ≠ t + 1 by omega), set_ne (show ptv ≠ t by omega)]; exact h1)
    (by simp only [env2, env1, set_ne (show t ≠ t + 1 by omega), set_eq])
    (by simp only [env2, set_eq]) rfl
  have hpv3 : env3 ptv = rN pt := by
    rw [hk3 _ (by omega) (by omega) (by simp only [vFh]; omega)]
    simp only [env2, env1, set_ne (show ptv ≠ t + 1 by omega), set_ne (show ptv ≠ t by omega)]; exact h1
  obtain ⟨e4, hp4⟩ := free_ok H hp3 (List.Perm.refl _) ptv hpv3
  have hnd3 := hp3.nodup
  obtain ⟨hko, hko2⟩ := keep_others hp3 (W' := W3.set pt (env3 vFh)) (others := others) (S := [pt])
    (by rw [ho3']; exact (List.perm_append_singleton _ _).nodup_iff.2 hnd3)
    (fun p hp' => by
      rw [ho3'] at hp'
      rcases List.mem_append.1 hp' with h | h
      · exact List.mem_cons_of_mem _ h
      · simp at h; subst h; exact List.mem_cons_self ..)
    ho3 (by simp) (fun q hq => by
      rw [List.getElem?_set_ne]; intro e; exact hq ⟨pt, by simp, by omega, by have := P_pos; omega⟩)
  refine ⟨_, _, .seq e1 (.seq e2 (.seq e3 e4)), ⟨hp4.perm (by rw [hko2, ho3']), fun a h => (hko a h).1⟩,
    fun j a b c d => ?_⟩
  rw [set_ne d, hk3 j b c d]; simp only [env2, env1, set_ne a, set_ne b]

end Proven.WP

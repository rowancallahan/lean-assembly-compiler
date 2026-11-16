/- Paged dynamic arrays (NOTES section 30), part 1: the page pool.

The work words `W` (word block 0 of the middle layer) hold, from word 0 on, `C` pages of `P = 2 ^ lg` words
each; a page is named by its first word (a multiple of `P`).  The pool state lives in four variables (machine
registers `a4 .. a7`): `vCap` = `C * P` (the end of the pool), `vBump` = the end of the pages handed out so far,
`vFh` = the first free page or `NIL`, every free page's word 0 = the next free page (a list through the free
pages themselves, no extra memory), and `vOk` (1, or 0 once a request found no page).

`PoolInv C env W used`: the pages in use `used` and the free pages are together exactly the pages below
`vBump`.  `alloc_ok`: the allocation either returns a page not in use (from the free list, else the bump) or,
exactly when all `C` pages are in use, clears `vOk`.  `free_ok`: a page in use goes back to the free list.
`alloc_spec`: a returned page, as a block of the work block, meets `AllocSpec` (`Compiler/AllocSpec.lean`). -/
import Riscv.Frontx.WaUpd
import Compiler.AllocSpec

namespace Proven.WP
open Proven Proven.WA
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj)

/-! ## Pages -/

/-- log2 of the page size in words -/
def lg : Nat := 10
/-- words per page -/
def P : Nat := 1024
theorem P_eq : P = 2 ^ lg := rfl
theorem P_pos : 0 < P := by decide

def vCap : Nat := 4
def vBump : Nat := 5
def vFh : Nat := 6
def vOk : Nat := 7

/-- the end of the free list -/
def NIL : BitVec 64 := BitVec.allOnes 64

/-- the pages below word `b` -/
def below (b : Nat) : List Nat := (List.range (b / P)).map (· * P)

theorem mem_below {b p : Nat} : p ∈ below b ↔ p % P = 0 ∧ p / P < b / P := by
  simp only [below, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Nat.mul_mod_left _ _, ?_⟩; rw [Nat.mul_div_cancel _ P_pos]; exact hi
  · rintro ⟨h1, h2⟩
    exact ⟨p / P, h2, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)⟩

theorem nodup_below (b : Nat) : (below b).Nodup :=
  List.Pairwise.map (· * P) (fun _ _ h e => h (Nat.eq_of_mul_eq_mul_right P_pos e)) List.nodup_range

theorem length_below (b : Nat) : (below b).length = b / P := by simp [below]

theorem below_succ {b : Nat} (hb : b % P = 0) : below (b + P) = below b ++ [b] := by
  simp only [below]
  rw [show (b + P) / P = b / P + 1 by rw [Nat.add_div_right _ P_pos], List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)]

/-- a page lies in `[0, b)` -/
theorem below_bound {b p : Nat} (h : p ∈ below b) : p % P = 0 ∧ p + P ≤ b := by
  obtain ⟨h1, h2⟩ := mem_below.1 h
  refine ⟨h1, ?_⟩
  have := Nat.div_add_mod p P
  have := Nat.div_add_mod b P
  have : (p / P + 1) * P ≤ b / P * P := Nat.mul_le_mul_right _ h2
  rw [P] at *; omega

/-- two different pages do not overlap -/
theorem page_apart {p q : Nat} (hp : p % P = 0) (hq : q % P = 0) (hne : p ≠ q) : p + P ≤ q ∨ q + P ≤ p := by
  rw [P] at *; omega

/-! ## The free list -/

/-- the free pages `ps`, linked through their word 0, from head `h` -/
def Chain (W : List (BitVec 64)) : List Nat → BitVec 64 → Prop
  | [], h => h = NIL
  | p :: ps, h => h = rN p ∧ ∃ nx, W[p]? = some nx ∧ Chain W ps nx

theorem Chain.frame {W W' : List (BitVec 64)} : ∀ {ps : List Nat} {h : BitVec 64}, Chain W ps h →
    (∀ p ∈ ps, W'[p]? = W[p]?) → Chain W' ps h
  | [], _, hc, _ => hc
  | p :: ps, _, ⟨h1, nx, h2, h3⟩, hf => ⟨h1, nx, by rw [hf p (by simp)]; exact h2,
      Chain.frame h3 fun q hq => hf q (by simp [hq])⟩

/-- **the pool**: `C` pages; the pages in use `used` and the free pages are the pages below the bump -/
def PoolInv (C : Nat) (env : Mach.BEnv) (W : List (BitVec 64)) (used : List Nat) : Prop :=
  ∃ bump free, env vCap = rN (C * P) ∧ env vBump = rN bump ∧ Chain W free (env vFh) ∧ bump % P = 0 ∧
    bump ≤ C * P ∧ C * P ≤ W.length ∧ W.length < 2 ^ 32 ∧ (used ++ free).Perm (below bump)

theorem PoolInv.nodup {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat}
    (h : PoolInv C env W used) : used.Nodup := by
  obtain ⟨b, fr, -, -, -, -, -, -, -, hp⟩ := h
  exact (List.nodup_append.1 (hp.nodup_iff.2 (nodup_below b))).1

theorem PoolInv.page {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat}
    (h : PoolInv C env W used) {p : Nat} (hp : p ∈ used) : p % P = 0 ∧ p + P ≤ C * P := by
  obtain ⟨b, fr, -, -, -, -, hb, -, -, hperm⟩ := h
  have := below_bound (hperm.subset (List.mem_append_left _ hp))
  exact ⟨this.1, by omega⟩

theorem PoolInv.length_le {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat}
    (h : PoolInv C env W used) : used.length ≤ C := by
  obtain ⟨b, fr, -, -, -, hb0, hb, -, -, hperm⟩ := h
  have := hperm.length_eq
  rw [List.length_append, length_below] at this
  have : b / P ≤ C * P / P := Nat.div_le_div_right hb
  rw [Nat.mul_div_cancel _ P_pos] at this
  omega

theorem PoolInv.wlen {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat}
    (h : PoolInv C env W used) : C * P ≤ W.length ∧ W.length < 2 ^ 32 := by
  obtain ⟨b, fr, -, -, -, -, -, h1, h2, -⟩ := h; exact ⟨h1, h2⟩

/-- the pool survives writes outside the free pages and changes of other variables -/
theorem PoolInv.frame {C : Nat} {env env' : Mach.BEnv} {W W' : List (BitVec 64)} {used : List Nat}
    (h : PoolInv C env W used) (he : ∀ j, j = vCap ∨ j = vBump ∨ j = vFh → env' j = env j)
    (hl : W'.length = W.length) (hw : ∀ q, (∀ p ∈ used, q < p ∨ p + P ≤ q) → W'[q]? = W[q]?) :
    PoolInv C env' W' used := by
  obtain ⟨b, fr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hnd := List.nodup_append.1 (h8.nodup_iff.2 (nodup_below b))
  refine ⟨b, fr, by rw [he _ (.inl rfl)]; exact h1, by rw [he _ (.inr (.inl rfl))]; exact h2,
    Chain.frame (by rw [he _ (.inr (.inr rfl))]; exact h3) (fun q hq => hw q fun p hp => ?_), h4, h5,
    by rw [hl]; exact h6, by rw [hl]; exact h7, h8⟩
  have hpq : p ≠ q := fun e => by subst e; exact hnd.2.2 p hp p hq rfl
  have bp := below_bound (h8.subset (List.mem_append_left _ hp))
  have bq := below_bound (h8.subset (List.mem_append_right _ hq))
  rcases page_apart bp.1 bq.1 hpq with h | h <;> omega

/-! ## Allocation -/

/-- one page into `r` (temporaries `t`, `t + 1`): pop the free list, else bump, else `vOk := 0` -/
def allocCode (r t : Nat) : MS :=
  .seq (.assign t (.bin .eq (.var vFh) (.const NIL)))
  (.seq (.assign (t + 1) (.bin .xor (.var t) (.const 1)))
  (.seq (when (t + 1) (.seq (.assign r (.var vFh)) (.load64 vFh 0 (.var vFh))))
  (when t (.seq (.assign r (.var vBump)) (.seq (.assign (t + 1) (.bin .ult (.var vBump) (.var vCap)))
    (.seq (.assign vBump (.ite (.var (t + 1)) (.bin .add (.var vBump) (.const (BitVec.ofNat 64 P))) (.var vBump)))
      (.assign vOk (.ite (.var (t + 1)) (.var vOk) (.const 0)))))))))

/-- the variables `allocCode r t` may change -/
def AllocVars (r t j : Nat) : Prop := j = r ∨ j = t ∨ j = t + 1 ∨ j = vFh ∨ j = vBump ∨ j = vOk

theorem nil_ne_rN {p : Nat} (h : p < 2 ^ 32) : rN p ≠ NIL := by
  intro e
  have := congrArg BitVec.toNat e
  rw [rN_toNat (by omega)] at this
  simp [NIL] at this; omega

set_option maxHeartbeats 1000000 in
/-- **allocation**: a page not in use, or (exactly when all `C` pages are in use) `vOk := 0` -/
theorem alloc_ok {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat} (H : Heap)
    (h : PoolInv C env W used) (r t : Nat) (hr : 8 ≤ r) (ht : 8 ≤ t) (hrt : r ≠ t ∧ r ≠ t + 1) :
    ∃ env', Mach.BExec (allocCode r t) ⟨env, H, [W]⟩ ⟨env', H, [W]⟩ ∧
      (∀ j, ¬ AllocVars r t j → env' j = env j) ∧
      ((used.length < C ∧ env' vOk = env vOk ∧ ∃ p, env' r = rN p ∧ p % P = 0 ∧ p + P ≤ C * P ∧ p ∉ used ∧
          PoolInv C env' W (p :: used)) ∨
        (used.length = C ∧ env' vOk = 0)) := by
  have hlenC := h.length_le
  obtain ⟨b, fr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hnd := List.nodup_append.1 (h8.nodup_iff.2 (nodup_below b))
  have hcnt : used.length + fr.length = b / P := by rw [← List.length_append, h8.length_eq, length_below]
  have hv : vCap = 4 ∧ vBump = 5 ∧ vFh = 6 ∧ vOk = 7 := ⟨rfl, rfl, rfl, rfl⟩
  have hP : P = 1024 := rfl
  cases fr with
  | cons p ps =>
    -- pop the free list
    obtain ⟨hfh, nx, hnx, hch⟩ := h3
    have bp := below_bound (h8.subset (List.mem_append_right _ (List.mem_cons_self ..)))
    have hpw : p < W.length := by omega
    let e1 := env.set t ((Mach.BExp.bin .eq (.var vFh) (.const NIL)).denote env)
    have he1t : e1 t = 0 := by
      simp only [e1, set_eq, Mach.BExp.denote, Op.eval, hfh]; rw [if_neg (nil_ne_rN (by omega))]
    let e2 := e1.set (t + 1) ((Mach.BExp.bin .xor (.var t) (.const 1)).denote e1)
    have he2 : e2 (t + 1) ≠ 0 := by simp only [e2, set_eq, Mach.BExp.denote, Op.eval, he1t]; decide
    have hfh2 : e2 vFh = rN p := by
      simp only [e2, e1, set_ne (show vFh ≠ t + 1 by rw [hv.2.2.1]; omega),
        set_ne (show vFh ≠ t by rw [hv.2.2.1]; omega)]; exact hfh
    let e3 := e2.set r (rN p)
    have ha : Mach.BExec (.assign r (.var vFh)) ⟨e2, H, [W]⟩ ⟨e3, H, [W]⟩ := by
      have := Mach.BExec.assign (v := r) (e := .var vFh) (σ := ⟨e2, H, [W]⟩)
      simp only [Mach.BExp.denote, hfh2] at this; exact this
    have hWp : W[p] = nx := by rw [List.getElem?_eq_getElem hpw] at hnx; exact Option.some.inj hnx
    have hld : Mach.BExec (.load64 vFh 0 (.var vFh)) ⟨e3, H, [W]⟩ ⟨e3.set vFh nx, H, [W]⟩ := by
      have := Mach.BExec.load64 (v := vFh) (b := 0) (i := .var vFh) (σ := ⟨e3, H, [W]⟩) (by simp)
        (by simp only [Mach.BExp.denote, e3, set_ne (show vFh ≠ r by rw [hv.2.2.1]; omega), hfh2,
              List.getElem_cons_zero]; rw [rN_toNat (by omega)]; exact hpw)
      simp only [Mach.BExp.denote, e3, set_ne (show vFh ≠ r by rw [hv.2.2.1]; omega), hfh2,
        List.getElem_cons_zero, rN_toNat (show p < 2 ^ 64 by omega), hWp] at this
      exact this
    have hw1 := when_true he2 (.seq ha hld)
    let e4 := (e3.set vFh nx).set (t + 1) 0
    have he4t : e4 t = 0 := by
      simp only [e4, e3, e2, set_ne (show t ≠ t + 1 by omega), set_ne (show t ≠ vFh by rw [hv.2.2.1]; omega),
        set_ne (show t ≠ r by omega)]; exact he1t
    have hbC : b / P ≤ C := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact h5)
    simp only [List.length_cons] at hcnt
    refine ⟨e4, .seq .assign (.seq .assign (.seq hw1 (when_false he4t))), ?_, .inl ⟨by omega, ?_, p, ?_, bp.1,
      by omega, (fun hp => hnd.2.2 p hp p (List.mem_cons_self ..) rfl), ?_⟩⟩
    · intro j hj
      simp only [AllocVars, not_or] at hj
      simp only [e4, e3, e2, e1, set_ne hj.2.2.1, set_ne hj.2.2.2.1, set_ne hj.1, set_ne hj.2.1]
    · simp only [e4, e3, e2, e1, set_ne (show vOk ≠ t + 1 by rw [hv.2.2.2]; omega),
        set_ne (show vOk ≠ vFh by decide), set_ne (show vOk ≠ r by rw [hv.2.2.2]; omega),
        set_ne (show vOk ≠ t by rw [hv.2.2.2]; omega)]
    · simp only [e4, e3, set_ne (show r ≠ t + 1 by omega), set_ne (show r ≠ vFh by rw [hv.2.2.1]; omega),
        set_eq]
    · refine ⟨b, ps, ?_, ?_, ?_, h4, h5, h6, h7, ?_⟩
      · simp only [e4, e3, e2, e1, set_ne (show vCap ≠ t + 1 by rw [hv.1]; omega), set_ne (show vCap ≠ vFh by decide),
          set_ne (show vCap ≠ r by rw [hv.1]; omega), set_ne (show vCap ≠ t by rw [hv.1]; omega)]; exact h1
      · simp only [e4, e3, e2, e1, set_ne (show vBump ≠ t + 1 by rw [hv.2.1]; omega),
          set_ne (show vBump ≠ vFh by decide), set_ne (show vBump ≠ r by rw [hv.2.1]; omega),
          set_ne (show vBump ≠ t by rw [hv.2.1]; omega)]; exact h2
      · simp only [e4, set_ne (show vFh ≠ t + 1 by rw [hv.2.2.1]; omega), set_eq]; exact hch
      · exact List.perm_middle.symm.trans h8
  | nil =>
    have hfh : env vFh = NIL := h3
    let e1 := env.set t ((Mach.BExp.bin .eq (.var vFh) (.const NIL)).denote env)
    have he1t : e1 t = 1 := by simp only [e1, set_eq, Mach.BExp.denote, Op.eval, hfh, if_true]
    let e2 := e1.set (t + 1) ((Mach.BExp.bin .xor (.var t) (.const 1)).denote e1)
    have he2 : e2 (t + 1) = 0 := by simp only [e2, set_eq, Mach.BExp.denote, Op.eval, he1t]; decide
    have he2t : e2 t ≠ 0 := by simp only [e2, set_ne (show t ≠ t + 1 by omega), he1t]; decide
    have hgv : ∀ j, j ≠ t → j ≠ t + 1 → e2 j = env j := fun j h1 h2 => by
      simp only [e2, e1, set_ne h1, set_ne h2]
    let e3 := e2.set r (e2 vBump)
    let c := (Mach.BExp.bin .ult (.var vBump) (.var vCap)).denote e3
    let e4 := e3.set (t + 1) c
    let e5 := e4.set vBump ((Mach.BExp.ite (.var (t + 1)) (.bin .add (.var vBump) (.const (BitVec.ofNat 64 P)))
      (.var vBump)).denote e4)
    let e6 := e5.set vOk ((Mach.BExp.ite (.var (t + 1)) (.var vOk) (.const 0)).denote e5)
    have hS : Mach.BExec (.seq (.assign r (.var vBump)) (.seq (.assign (t + 1) (.bin .ult (.var vBump) (.var vCap)))
        (.seq (.assign vBump (.ite (.var (t + 1)) (.bin .add (.var vBump) (.const (BitVec.ofNat 64 P))) (.var vBump)))
          (.assign vOk (.ite (.var (t + 1)) (.var vOk) (.const 0)))))) ⟨e2, H, [W]⟩ ⟨e6, H, [W]⟩ :=
      .seq .assign (.seq .assign (.seq .assign .assign))
    have hw := when_true he2t hS
    have hb3 : e3 vBump = rN b := by
      simp only [e3, set_ne (show vBump ≠ r by rw [hv.2.1]; omega)]
      rw [hgv _ (by rw [hv.2.1]; omega) (by rw [hv.2.1]; omega)]; exact h2
    have hc3 : e3 vCap = rN (C * P) := by
      simp only [e3, set_ne (show vCap ≠ r by rw [hv.1]; omega)]
      rw [hgv _ (by rw [hv.1]; omega) (by rw [hv.1]; omega)]; exact h1
    have hc : c = if b < C * P then 1 else 0 := by
      simp only [c, Mach.BExp.denote, Op.eval, hb3, hc3, rN_lt (show b < 2 ^ 64 by omega)
        (show C * P < 2 ^ 64 by omega)]
    let e7 := e6.set t 0
    have hfin : Mach.BExec (allocCode r t) ⟨env, H, [W]⟩ ⟨e7, H, [W]⟩ :=
      .seq .assign (.seq .assign (.seq (when_false he2) hw))
    have hkeep : ∀ j, ¬ AllocVars r t j → e7 j = env j := by
      intro j hj
      simp only [AllocVars, not_or] at hj
      simp only [e7, e6, e5, e4, e3, set_ne hj.2.1, set_ne hj.2.2.2.2.2, set_ne hj.2.2.2.2.1, set_ne hj.2.2.1,
        set_ne hj.1]
      exact hgv j hj.2.1 hj.2.2.1
    have hok6 : e7 vOk = if b < C * P then env vOk else 0 := by
      simp only [e7, e6, set_ne (show vOk ≠ t by rw [hv.2.2.2]; omega), set_eq, Mach.BExp.denote]
      simp only [e5, e4, set_ne (show vOk ≠ vBump by decide), set_ne (show t + 1 ≠ vBump by rw [hv.2.1]; omega),
        set_eq, set_ne (show vOk ≠ t + 1 by rw [hv.2.2.2]; omega), e3, set_ne (show vOk ≠ r by rw [hv.2.2.2]; omega),
        hc]
      rw [hgv _ (by rw [hv.2.2.2]; omega) (by rw [hv.2.2.2]; omega)]
      split <;> simp
    refine ⟨e7, hfin, hkeep, ?_⟩
    by_cases hbc : b < C * P
    · have hb1 : b + P ≤ C * P := by
        have hq : b / P < C := (Nat.div_lt_iff_lt_mul P_pos).2 hbc
        have e := Nat.div_add_mod b P
        rw [h4, Nat.add_zero] at e
        have : P * (b / P + 1) ≤ P * C := Nat.mul_le_mul_left _ hq
        rw [Nat.mul_comm C P]; rw [Nat.mul_add, Nat.mul_one, e] at this; exact this
      refine .inl ⟨?_, by rw [hok6, if_pos hbc], b, ?_, h4, hb1, ?_, ?_⟩
      · have : b / P < C := by
          rw [Nat.div_lt_iff_lt_mul P_pos]; exact hbc
        simp at hcnt; omega
      · simp only [e7, e6, e5, e4, e3, set_ne (show r ≠ t by omega), set_ne (show r ≠ vOk by rw [hv.2.2.2]; omega),
          set_ne (show r ≠ vBump by rw [hv.2.1]; omega), set_ne (show r ≠ t + 1 by omega), set_eq]
        rw [hgv _ (by rw [hv.2.1]; omega) (by rw [hv.2.1]; omega)]; exact h2
      · intro hu
        have := below_bound (h8.subset (List.mem_append_left _ hu)); omega
      · refine ⟨b + P, [], ?_, ?_, ?_, ?_, hb1, h6, h7, ?_⟩
        · rw [hkeep vCap (by simp only [AllocVars, vCap, vFh, vBump, vOk]; omega)]; exact h1
        · simp only [e7, e6, e5, set_ne (show vBump ≠ t by rw [hv.2.1]; omega), set_ne (show vBump ≠ vOk by decide),
            set_eq, Mach.BExp.denote, e4, set_eq, hc, if_pos hbc]
          simp only [set_ne (show vBump ≠ t + 1 by rw [hv.2.1]; omega), hb3, rN_add,
            show (1 : BitVec 64) ≠ 0 by decide, if_false, Op.eval]; rfl
        · show e7 vFh = NIL
          simp only [e7, e6, e5, e4, e3, set_ne (show vFh ≠ t by rw [hv.2.2.1]; omega), set_ne (show vFh ≠ vOk by decide),
            set_ne (show vFh ≠ vBump by decide), set_ne (show vFh ≠ t + 1 by rw [hv.2.2.1]; omega),
            set_ne (show vFh ≠ r by rw [hv.2.2.1]; omega)]
          rw [hgv _ (by rw [hv.2.2.1]; omega) (by rw [hv.2.2.1]; omega)]; exact hfh
        · rw [hP] at h4 ⊢; omega
        · rw [below_succ h4]; simp only [List.append_nil] at h8 ⊢
          exact (List.perm_append_singleton b used).symm.trans (h8.append_right [b])
    · refine .inr ⟨?_, by rw [hok6, if_neg hbc]⟩
      have : b = C * P := by omega
      subst this
      rw [Nat.mul_div_cancel _ P_pos] at hcnt; simpa using hcnt

/-! ## Freeing -/

/-- page `r` back to the free list -/
def freeCode (r : Nat) : MS := .seq (.store64 0 (.var r) (.var vFh)) (.assign vFh (.var r))

theorem free_ok {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used rest : List Nat} (H : Heap)
    (h : PoolInv C env W used) (hp : used.Perm (p :: rest)) (r : Nat) (hr : env r = rN p) :
    Mach.BExec (freeCode r) ⟨env, H, [W]⟩ ⟨env.set vFh (rN p), H, [W.set p (env vFh)]⟩ ∧
      PoolInv C (env.set vFh (rN p)) (W.set p (env vFh)) rest := by
  obtain ⟨b, fr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hnd := List.nodup_append.1 (h8.nodup_iff.2 (nodup_below b))
  have bp := below_bound (h8.subset (List.mem_append_left _ (hp.symm.subset (List.mem_cons_self ..))))
  have hpw : p < W.length := by have := P_pos; omega
  have hst := store64_at (σ := ⟨env, H, [W]⟩) rfl (.var r) (.var vFh) p (by
    simp only [Mach.BExp.denote, hr]; exact rN_toNat (by omega)) hpw
  refine ⟨.seq hst (by simp only [Mach.BExp.denote] at hst ⊢; rw [← hr]; exact .assign), ?_⟩
  have hv : vCap = 4 ∧ vBump = 5 ∧ vFh = 6 ∧ vOk = 7 := ⟨rfl, rfl, rfl, rfl⟩
  have hpf : p ∉ fr := fun hf => hnd.2.2 p (hp.symm.subset (List.mem_cons_self ..)) p hf rfl
  refine ⟨b, p :: fr, ?_, ?_, ⟨by rw [set_eq], env vFh, ?_, Chain.frame (W := W) ?_ ?_⟩, h4, h5, by simpa using h6,
    by simpa using h7, ?_⟩
  · rw [set_ne (by decide)]; exact h1
  · rw [set_ne (by decide)]; exact h2
  · rw [List.getElem?_set_self hpw]
  · exact h3
  · intro q hq; rw [List.getElem?_set_ne (fun e => hpf (by rw [e]; exact hq))]
  · exact List.perm_middle.trans ((hp.append_right fr).symm.trans h8)

/-! ## `AllocSpec` -/

open Proven.Top Proven.Top.Alloc in
/-- **A page meets the allocator specification**: page `p` of the pool, as the block of `8 P` bytes at
`work + 8 p`, lies inside the work block and apart from every page in use (and from any block above the pool,
such as the back end's frame). -/
theorem alloc_spec {C : Nat} {env : Mach.BEnv} {W : List (BitVec 64)} {used : List Nat} (work : UInt64 × Nat)
    (hwork : work.1.toNat + work.2 < 2 ^ 64) (hcap : 8 * (C * P) ≤ work.2)
    (h : PoolInv C env W used) {p : Nat} (hp : p % P = 0) (hpc : p + P ≤ C * P) (hpu : p ∉ used)
    (above : List (UInt64 × Nat)) (habove : ∀ a ∈ above, work.1.toNat + 8 * (C * P) ≤ a.1.toNat) :
    AllocSpec (8 * P) work (used.map (fun q => (work.1 + (8 * q).toUInt64, 8 * P)) ++ above) 1
      (work.1 + (8 * p).toUInt64, 8 * P) := by
  have e : ∀ q, q + P ≤ C * P → (work.1 + (8 * q).toUInt64).toNat = work.1.toNat + 8 * q := fun q hq => by
    rw [UInt64.toNat_add]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (show 8 * q < 2 ^ 64 by have := P_pos; omega)]
    exact Nat.mod_eq_of_lt (by have := P_pos; omega)
  refine ⟨by simp, ⟨by rw [e p hpc]; omega, by rw [e p hpc]; omega⟩, ?_⟩
  intro u hu
  simp only [List.mem_append, List.mem_map] at hu
  rcases hu with ⟨q, hq, rfl⟩ | hu
  · have bq := h.page hq
    have hne : q ≠ p := fun e => hpu (e ▸ hq)
    unfold Apart
    rw [e q bq.2, e p hpc]
    rcases page_apart bq.1 hp hne with h' | h'
    · left; omega
    · right; omega
  · have := habove u hu
    unfold Apart
    right; rw [e p hpc]; omega

end Proven.WP

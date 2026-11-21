/- The `XPipe` programs with their working space moved into the WORK block (the `Implements1` convention,
`Spec/Implements1.lean`: `a2` = work base, `sp` = work top), source level.

`XPipe.progB p` (`Compiler/Front/PipeStdB.lean`) works on three byte blocks: input (base `v0`), output
(`v3`, used as a buffer of `XPipe.space p n` bytes beyond the result) and scratch (`v2`, `XPipe.sspace p n`
bytes).  `progI p` runs the same program on blocks input (`v0`), WORK (`v2`) and the real output (`v3`):

    v15 := v1 + E;  relB (progB p);  for v5 < v1: out[v5] := work[v5]

`relB` (relocation) sends the old output block to `work[0, L)` and the old scratch block to `work[L, 2 L)`,
`L = n + E` held in the slot variable `v15` (`E = XPipe.extra p`, a static bound with
`XPipe.space p n ≤ n + E` and `XPipe.sspace p n ≤ n + E`), and the copy loop writes exactly the `|result|`
result bytes to the real output.  `relB_exec`: a run of `p` gives a run of `relB p` (for programs passing the
decidable check `okR`: no use of `v2`, `v3`, `v15`, blocks `< 3`).  `progI_exec`: the run of `progI p`. -/
import Nano.Base.Compiler.Front.PipeStdBMachine

set_option linter.unusedVariables false

namespace Proven

/-! ## The static bound `E` -/

def XStage.extra : XStage → Nat
  | .base (.fold ..) => 1
  | .base (.foldW ..) => 8
  | .red r => r.code.k
  | .appendC c => c.length
  | _ => 0

def XPipe.extra (p : XPipe) : Nat := (p.map XStage.extra).sum

theorem XStage.space_le (st : XStage) (cs : CS) (n : Nat) : st.space cs n ≤ n + st.extra := by
  cases st with
  | base st => cases st <;> simp only [XStage.space, Stage.space, XStage.extra] <;> (try split) <;> omega
  | _ => (try simp only [XStage.space, XStage.extra]) <;> omega

theorem XStage.len_le (st : XStage) (n : Nat) : st.len n ≤ n + st.extra := by
  cases st with
  | base st => cases st <;> simp only [XStage.len, Stage.len, XStage.extra] <;> omega
  | _ => (try simp only [XStage.len, XStage.extra]) <;> omega

theorem XPipe.need_le : ∀ (p : XPipe) (cs : CS) (n : Nat), XPipe.need p cs n ≤ n + XPipe.extra p
  | [], cs, n => by simp only [XPipe.need, XPipe.extra, List.map_nil, List.sum_nil]; split <;> omega
  | st :: r, cs, n => by
    have h1 := st.space_le cs n; have h2 := st.len_le n
    have h3 := XPipe.need_le r (xstageC st cs).2 (st.len n)
    simp only [XPipe.need, XPipe.extra, List.map_cons, List.sum_cons] at h3 ⊢
    omega

theorem XPipe.sneed_le : ∀ (p : XPipe) (cs : CS) (n : Nat), XPipe.sneed p cs n ≤ n + XPipe.extra p
  | [], cs, n => by simp only [XPipe.sneed]; omega
  | st :: r, cs, n => by
    have h2 := st.len_le n
    have h3 := XPipe.sneed_le r (xstageC st cs).2 (st.len n)
    simp only [XPipe.sneed, XPipe.extra, List.map_cons, List.sum_cons] at h3 ⊢
    split <;> omega

theorem XPipe.space_le (p : XPipe) (n : Nat) : XPipe.space p n ≤ n + XPipe.extra p := XPipe.need_le p cs0 n
theorem XPipe.sspace_le (p : XPipe) (n : Nat) : XPipe.sspace p n ≤ n + XPipe.extra p := XPipe.sneed_le p cs0 n

/-! ## The relocation -/

/-- the expression does not read `v2`, `v3`, `v15` -/
def BExp.av : BExp → Bool
  | .var i => i != 2 && i != 3 && i != 15
  | .const _ => true
  | .bin _ a b => a.av && b.av
  | .ite c a b => c.av && a.av && b.av

/-- the check for the relocation: `v2`, `v3`, `v15` neither read nor written, blocks `0, 1, 2` only -/
def okR : BStmt → Bool
  | .assign v e => v != 2 && v != 3 && v != 15 && e.av
  | .load v b i => v != 2 && v != 3 && v != 15 && i.av && decide (b < 3)
  | .store b i e => i.av && e.av && decide (b < 3)
  | .seq p q => okR p && okR q
  | .loop c b => c.av && okR b
  | .mop .. => false

/-- old block 2 (scratch) ↦ work block at offset `v15`; old block 1 (output) ↦ work block at offset 0 -/
def relB : BStmt → BStmt
  | .assign v e => .assign v e
  | .load v b i => if b = 2 then .load v 1 (.bin .add i (.var 15)) else .load v b i
  | .store b i e => if b = 2 then .store 1 (.bin .add i (.var 15)) e else .store b i e
  | .seq p q => .seq (relB p) (relB q)
  | .loop c b => .loop c (relB b)
  | .mop m v a b => .mop m v a b

/-- environments agreeing outside `v2`, `v3`, `v15` -/
def AgR (E₁ E₂ : BEnv) : Prop := ∀ v, v ≠ 2 → v ≠ 3 → v ≠ 15 → E₁ v = E₂ v

theorem BExp.denote_av : ∀ {e : BExp}, e.av = true → ∀ {E₁ E₂ : BEnv}, AgR E₁ E₂ → e.denote E₁ = e.denote E₂
  | .var i, h, _, _, ha => by
    simp only [BExp.av, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ha i h.1.1 h.1.2 h.2
  | .const _, _, _, _, _ => rfl
  | .bin _ a b, h, _, _, ha => by
    simp only [BExp.av, Bool.and_eq_true] at h
    simp only [BExp.denote, BExp.denote_av h.1 ha, BExp.denote_av h.2 ha]
  | .ite c a b, h, _, _, ha => by
    simp only [BExp.av, Bool.and_eq_true] at h
    simp only [BExp.denote, BExp.denote_av h.1.1 ha, BExp.denote_av h.1.2 ha, BExp.denote_av h.2 ha]

/-- the relation between a run of `p` (blocks `[a, o, sc]`) and of `relB p` (blocks `[a, o ++ sc ++ t, r]`) -/
structure RelR (L : Nat) (r t : List (BitVec 8)) (σ τ : BState) : Prop where
  env : AgR τ.env σ.env
  k : τ.env 15 = BitVec.ofNat 64 L
  heap : ∃ a o sc, σ.heap = [a, o, sc] ∧ τ.heap = [a, o ++ sc ++ t, r] ∧ o.length = L ∧ L + sc.length < 2 ^ 64

theorem AgR.set {E₁ E₂ : BEnv} (h : AgR E₁ E₂) (v : Nat) (x : BitVec 64) : AgR (E₁.set v x) (E₂.set v x) :=
  fun w h2 h3 h15 => by simp only [BEnv.set]; split
                        · rfl
                        · exact h w h2 h3 h15

theorem set_app3_mid {α : Type} (o sc t : List α) {j : Nat} (hj : j < sc.length) (x : α) :
    (o ++ sc ++ t).set (o.length + j) x = o ++ sc.set j x ++ t := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_left _ _ hj, List.append_assoc]

theorem set_app3_left {α : Type} (o sc t : List α) {j : Nat} (hj : j < o.length) (x : α) :
    (o ++ sc ++ t).set j x = o.set j x ++ sc ++ t := by
  rw [List.append_assoc, List.set_append_left _ _ hj, List.append_assoc]

theorem toNat_addK {i : BitVec 64} {L m : Nat} (hi : i.toNat < m) (hL : L + m < 2 ^ 64) :
    (i + BitVec.ofNat 64 L).toNat = L + i.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]; omega

theorem get3_left {α : Type} (o sc t : List α) (j : Nat) (h : j < o.length) (h' : j < (o ++ sc ++ t).length) :
    (o ++ sc ++ t)[j] = o[j] := by
  rw [List.getElem_append_left (by simp; omega)]; exact List.getElem_append_left h

theorem get3_mid {α : Type} (o sc t : List α) (j : Nat) (h : j < sc.length)
    (h' : o.length + j < (o ++ sc ++ t).length) : (o ++ sc ++ t)[o.length + j] = sc[j] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-- **a run of `p` gives a run of `relB p`** -/
theorem relB_exec {L : Nat} {r t : List (BitVec 8)} {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') :
    okR p = true → ∀ {τ : BState}, RelR L r t σ τ → ∃ τ', BExec (relB p) τ τ' ∧ RelR L r t σ' τ' := by
  induction h with
  | mop => intro hok; simp [okR] at hok
  | @assign v e σ =>
    intro hok τ hr
    simp only [okR, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨h2, h3⟩, h15⟩, he⟩ := hok
    refine ⟨_, BExec.assign, ?_⟩
    rw [BExp.denote_av he hr.env]
    exact ⟨hr.env.set v _, by simp only [BEnv.set, if_neg (Ne.symm h15)]; exact hr.k, hr.heap⟩
  | @load v b i σ hb hi =>
    intro hok τ hr
    simp only [okR, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨h2, h3⟩, h15⟩, he⟩, hb3⟩ := hok
    obtain ⟨a, o, sc, hs, ht, ho, hL⟩ := hr.heap
    rcases σ with ⟨eσ, hσ⟩; rcases τ with ⟨eτ, hτ⟩
    dsimp only at hs ht hb hi ⊢; subst hs; subst ht
    have hd : i.denote eτ = i.denote eσ := BExp.denote_av he hr.env
    have hk : eτ 15 = BitVec.ofNat 64 L := hr.k
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
    · refine ⟨_, BExec.load (by simp) (by rw [hd]; simpa using hi), ?_⟩
      refine ⟨fun w h2' h3' h15' => ?_, by simp only [BEnv.set, if_neg (Ne.symm h15)]; exact hk,
        ⟨a, o, sc, rfl, rfl, ho, hL⟩⟩
      simp only [BEnv.set]; split
      · simp only [List.getElem_cons_zero, hd]
      · exact hr.env w h2' h3' h15'
    · have hi' : (i.denote eσ).toNat < o.length := by simpa using hi
      refine ⟨_, BExec.load (by simp) (by rw [hd]; simp; omega), ?_⟩
      refine ⟨fun w h2' h3' h15' => ?_, by simp only [BEnv.set, if_neg (Ne.symm h15)]; exact hk,
        ⟨a, o, sc, rfl, rfl, ho, hL⟩⟩
      simp only [BEnv.set]; split
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hd]
        rw [get3_left o sc t _ hi']
      · exact hr.env w h2' h3' h15'
    · have hi' : (i.denote eσ).toNat < sc.length := by simpa using hi
      have hx : ((BExp.bin .add i (.var 15)).denote eτ).toNat = o.length + (i.denote eσ).toNat := by
        simp only [BExp.denote, Op.eval, hd, hk]; rw [toNat_addK hi' hL, ho]
      refine ⟨_, BExec.load (b := 1) (by simp) (by rw [hx]; simp; omega), ?_⟩
      refine ⟨fun w h2' h3' h15' => ?_, by simp only [BEnv.set, if_neg (Ne.symm h15)]; exact hk,
        ⟨a, o, sc, rfl, rfl, ho, hL⟩⟩
      simp only [BEnv.set]; split
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hx]
        rw [get3_mid o sc t _ hi']
      · exact hr.env w h2' h3' h15'
  | @store b i e σ hb hi =>
    intro hok τ hr
    simp only [okR, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hi0, he⟩, hb3⟩ := hok
    obtain ⟨a, o, sc, hs, ht, ho, hL⟩ := hr.heap
    rcases σ with ⟨eσ, hσ⟩; rcases τ with ⟨eτ, hτ⟩
    dsimp only at hs ht hb hi ⊢; subst hs; subst ht
    have hd : i.denote eτ = i.denote eσ := BExp.denote_av hi0 hr.env
    have hde : e.denote eτ = e.denote eσ := BExp.denote_av he hr.env
    have hk : eτ 15 = BitVec.ofNat 64 L := hr.k
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
    · refine ⟨_, BExec.store (by simp) (by rw [hd]; simpa using hi), hr.env, hk, ⟨_, o, sc, rfl, ?_, ho, hL⟩⟩
      simp [hd, hde]
    · have hi' : (i.denote eσ).toNat < o.length := by simpa using hi
      refine ⟨_, BExec.store (by simp) (by rw [hd]; simp; omega), hr.env, hk,
        ⟨a, _, sc, rfl, ?_, by simpa using ho, hL⟩⟩
      simp only [List.set_cons_succ, List.set_cons_zero, List.getElem_cons_succ, List.getElem_cons_zero, hd, hde]
      rw [set_app3_left _ _ _ hi']
    · have hi' : (i.denote eσ).toNat < sc.length := by simpa using hi
      have hx : ((BExp.bin .add i (.var 15)).denote eτ).toNat = o.length + (i.denote eσ).toNat := by
        simp only [BExp.denote, Op.eval, hd, hk]; rw [toNat_addK hi' hL, ho]
      refine ⟨_, BExec.store (b := 1) (by simp) (by rw [hx]; simp; omega), hr.env, hk,
        ⟨a, o, _, rfl, ?_, ho, by simpa using hL⟩⟩
      simp only [List.set_cons_succ, List.set_cons_zero, List.getElem_cons_succ, List.getElem_cons_zero, hx, hde]
      rw [set_app3_mid _ _ _ hi']
  | seq _ _ ih1 ih2 =>
    intro hok τ hr
    simp only [okR, Bool.and_eq_true] at hok
    obtain ⟨τ₁, x1, r1⟩ := ih1 hok.1 hr
    obtain ⟨τ₂, x2, r2⟩ := ih2 hok.2 r1
    exact ⟨τ₂, .seq x1 x2, r2⟩
  | @loopF c b σ hc =>
    intro hok τ hr
    simp only [okR, Bool.and_eq_true] at hok
    exact ⟨τ, .loopF (by rw [BExp.denote_av hok.1 hr.env]; exact hc), hr⟩
  | @loopT c b σ σ₁ σ₂ hc _ _ ih1 ih2 =>
    intro hok τ hr
    have hok' := hok
    simp only [okR, Bool.and_eq_true] at hok
    obtain ⟨τ₁, x1, r1⟩ := ih1 hok.2 hr
    obtain ⟨τ₂, x2, r2⟩ := ih2 hok' r1
    exact ⟨τ₂, .loopT (by rw [BExp.denote_av hok.1 hr.env]; exact hc) x1 x2, r2⟩

/-! ## The copy loop -/

/-- `v5 := 0; while v5 < v1: v6 := work[v5]; out[v5] := v6; v5 += 1` -/
def copyBody : BStmt :=
  .seq (.load 6 1 (.var 5)) (.seq (.store 2 (.var 5) (.var 6)) (.assign 5 (.bin .add (.var 5) (.const 1))))
def copyLoop : BStmt := .loop (.bin .ult (.var 5) (.var 1)) copyBody
def copyL : BStmt := .seq (.assign 5 (.const 0)) copyLoop

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem take_set_step {w r : List (BitVec 8)} {j : Nat} (hw : j < w.length) (hr : j < r.length) :
    (w.take j ++ r.drop j).set j w[j] = w.take (j + 1) ++ r.drop (j + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_set, List.length_append, List.length_take, List.length_drop] at h1
    rw [List.getElem_set]
    split
    · rename_i e; subst e
      rw [List.getElem_append_left (by simp; omega)]; simp
    · by_cases hij : i < j
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]; simp
      · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_drop, List.length_take]
        congr 1; omega

theorem copyLoop_exec (a w r : List (BitVec 8)) (m : Nat) (hm : m < 2 ^ 32) (hw : m ≤ w.length)
    (hr : m ≤ r.length) : ∀ (k j : Nat) (σ : BState), j + k = m → σ.env 5 = BitVec.ofNat 64 j →
    σ.env 1 = BitVec.ofNat 64 m → σ.heap = [a, w, w.take j ++ r.drop j] →
    ∃ σ', BExec copyLoop σ σ' ∧ σ'.heap = [a, w, w.take m ++ r.drop m] ∧ σ'.env 1 = BitVec.ofNat 64 m
  | 0, j, σ, hk, h5, h1, hh => by
    refine ⟨σ, .loopF ?_, by rw [hh, show j = m by omega], h1⟩
    simp only [BExp.denote, Op.eval, h5, h1]
    rw [if_neg (by rw [ofNat_lt_ofNat (by omega) (by omega)]; omega)]
  | k + 1, j, σ, hk, h5, h1, hh => by
    rcases σ with ⟨env, heap⟩; dsimp only at h5 h1 hh; subst hh
    have hj : j < w.length := by omega
    have e5 : (BExp.denote env (.var 5)).toNat = j := by
      simp only [BExp.denote, h5, BitVec.toNat_ofNat]; omega
    let σ₁ : BState := ⟨env.set 6 (w[j].setWidth 64), [a, w, w.take j ++ r.drop j]⟩
    have x1 : BExec (.load 6 1 (.var 5)) ⟨env, [a, w, w.take j ++ r.drop j]⟩ σ₁ := by
      have := BExec.load (v := 6) (b := 1) (i := .var 5) (σ := ⟨env, [a, w, w.take j ++ r.drop j]⟩)
        (by simp) (by simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rw [e5]; exact hj)
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, e5] at this; exact this
    have e5' : (BExp.denote σ₁.env (.var 5)).toNat = j := by
      simp only [σ₁, BExp.denote, BEnv.set, if_neg (show (5 : Nat) ≠ 6 by omega), h5, BitVec.toNat_ofNat]; omega
    let σ₂ : BState := ⟨σ₁.env, [a, w, w.take (j + 1) ++ r.drop (j + 1)]⟩
    have x2 : BExec (.store 2 (.var 5) (.var 6)) σ₁ σ₂ := by
      have := BExec.store (b := 2) (i := .var 5) (e := .var 6) (σ := σ₁) (by simp [σ₁])
        (by simp only [σ₁, List.getElem_cons_succ, List.getElem_cons_zero]; rw [e5']; simp; omega)
      simp only [σ₁, List.getElem_cons_succ, List.getElem_cons_zero, List.set_cons_succ, List.set_cons_zero] at this
      rw [e5'] at this
      simp only [BExp.denote, BEnv.set, if_pos, setWidth_setWidth8] at this
      rw [take_set_step hj (by omega)] at this; exact this
    let σ₃ : BState := ⟨σ₂.env.set 5 ((BExp.bin .add (.var 5) (.const 1)).denote σ₂.env), σ₂.heap⟩
    have h53 : σ₃.env 5 = BitVec.ofNat 64 (j + 1) := by
      simp only [σ₃, σ₂, σ₁, BEnv.set, if_pos, BExp.denote, Op.eval, if_neg (show (5 : Nat) ≠ 6 by omega), h5]
      apply BitVec.eq_of_toNat_eq; simp
    have h13 : σ₃.env 1 = BitVec.ofNat 64 m := by
      simp only [σ₃, σ₂, σ₁, BEnv.set, if_neg (show (1 : Nat) ≠ 5 by omega), if_neg (show (1 : Nat) ≠ 6 by omega), h1]
    obtain ⟨σ', x, hh', h1'⟩ := copyLoop_exec a w r m hm hw hr k (j + 1) σ₃ (by omega) h53 h13 rfl
    refine ⟨σ', .loopT ?_ (.seq x1 (.seq x2 BExec.assign)) x, hh', h1'⟩
    simp only [BExp.denote, Op.eval, h5, h1]
    rw [if_pos (by rw [ofNat_lt_ofNat (by omega) (by omega)]; omega)]; decide

theorem copyL_exec (a w r : List (BitVec 8)) (m : Nat) (hm : m < 2 ^ 32) (hw : m ≤ w.length) (hr : m ≤ r.length)
    (σ : BState) (h1 : σ.env 1 = BitVec.ofNat 64 m) (hh : σ.heap = [a, w, r]) :
    ∃ σ', BExec copyL σ σ' ∧ σ'.heap = [a, w, w.take m ++ r.drop m] ∧ σ'.env 1 = BitVec.ofNat 64 m := by
  obtain ⟨σ', x, h⟩ := copyLoop_exec a w r m hm hw hr m 0 ⟨σ.env.set 5 ((BExp.const 0).denote σ.env), σ.heap⟩
    (by omega) (by simp [BEnv.set, BExp.denote]) (by simp only [BEnv.set, if_neg (show (1 : Nat) ≠ 5 by omega)]; exact h1)
    (by simp [hh])
  exact ⟨σ', .seq BExec.assign x, h⟩

/-! ## The program -/

/-- **the pipe in the `Implements1` convention**: blocks input (`v0`), work (`v2`), output (`v3`) -/
def progI (p : XPipe) : BStmt :=
  .seq (.assign 15 (.bin .add (.var 1) (.const (BitVec.ofNat 64 (XPipe.extra p))))) (.seq (relB (XPipe.progB p)) copyL)

/-- **the run of `progI p`**: the work block (`2 (n + E)` bytes) holds anything; afterwards the first
`|result|` output bytes are the result, the other output bytes are unchanged, `v1` = the result length -/
theorem progI_exec (p : XPipe) (hc : ∀ st ∈ p, st.chk = none) (hR : okR (XPipe.progB p) = true)
    (hE : XPipe.extra p < 2 ^ 20) (xs : List UInt8) (wk out : List (BitVec 8)) (env : BEnv)
    (h1 : env 1 = .ofNat 64 xs.length) (hx : xs.length ≤ 2 ^ 20)
    (hw : wk.length = 2 * (xs.length + XPipe.extra p)) (ho : (XPipe.denote p xs).length ≤ out.length)
    (hol : out.length < 2 ^ 32) :
    ∃ σ' wk', BExec (progI p) ⟨env, [tbs xs, wk, out]⟩ σ' ∧ σ'.heap = [tbs xs, wk', tbs (XPipe.denote p xs) ++
      out.drop (XPipe.denote p xs).length] ∧ σ'.env 1 = .ofNat 64 (XPipe.denote p xs).length := by
  let L := xs.length + XPipe.extra p
  let env₁ := env.set 15 ((BExp.bin .add (.var 1) (.const (BitVec.ofNat 64 (XPipe.extra p)))).denote env)
  have e15 : env₁ 15 = BitVec.ofNat 64 L := by
    simp only [env₁, BEnv.set, if_pos, BExp.denote, Op.eval, h1]
    apply BitVec.eq_of_toNat_eq; simp [L]
  have e1 : env₁ 1 = BitVec.ofNat 64 xs.length := by simp only [env₁, BEnv.set, if_neg (show (1 : Nat) ≠ 15 by omega), h1]
  have hsp := XPipe.space_le p xs.length; have hss := XPipe.sspace_le p xs.length
  obtain ⟨τ', out', scr', xB, hhB, hlB, htB, h1B⟩ := XPipe.progB_exec p hc xs (wk.take L) (wk.drop L) env₁ e1
    (by omega) (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
  have hr0 : RelR L out [] ⟨env₁, [tbs xs, wk.take L, wk.drop L]⟩ ⟨env₁, [tbs xs, wk, out]⟩ :=
    ⟨fun _ _ _ _ => rfl, e15, ⟨_, _, _, rfl, by simp, by simp; omega, by simp; omega⟩⟩
  obtain ⟨τ₂, xR, hr⟩ := relB_exec xB hR hr0
  obtain ⟨a, o, sc, hs, ht, hoL, _⟩ := hr.heap
  rw [hhB] at hs; simp only [List.cons.injEq, and_true] at hs; obtain ⟨rfl, rfl, rfl⟩ := hs
  have hm : (XPipe.denote p xs).length ≤ out'.length := by
    have := congrArg List.length htB; simp at this; omega
  have h1₂ : τ₂.env 1 = BitVec.ofNat 64 (XPipe.denote p xs).length := by
    rw [hr.env 1 (by omega) (by omega) (by omega), h1B]
  obtain ⟨σ', xC, hhC, h1C⟩ := copyL_exec (tbs xs) (out' ++ scr' ++ []) out (XPipe.denote p xs).length
    (by have := congrArg List.length htB; simp at this; omega) (by simp; omega) ho τ₂ h1₂ ht
  have hT : (out' ++ scr' ++ []).take (XPipe.denote p xs).length = tbs (XPipe.denote p xs) := by
    rw [List.append_nil, List.take_append_of_le_length hm, htB]
  rw [hT] at hhC
  exact ⟨σ', _, .seq BExec.assign (.seq xR xC), hhC, h1C⟩

end Proven

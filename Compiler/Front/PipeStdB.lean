/- The `XPipe` program in the statement language with spill slots (`BStmt`, `Riscv/Direct/Arr2Code.lean`), so
that `List.mergeSort` can use the proved O(n log n) bottom-up merge sort (`Riscv/Direct/SortMergeSrc.lean`),
which needs a scratch block and 7 spill slots.

Blocks: 0 = input (base `v0`), 1 = output (base `v3`), 2 = scratch (base `v2`): `bv = [0, 3, 2]`.
Every `AStmt` stage of `XPipe.prog` is reused with its variables renamed (`rn`): `a2` (the loop counter)
becomes `v7`, `a7` becomes the slot `v8`, the others stay; so `v2` keeps the scratch base.
A `sort` stage is: the view materialized to `out[0..m)` (as before), copied to `scr[0..m)`, then the merge
sort `scr → out` (`msortG 2 1 2`); a sort of the input itself (`cs0`) is `msortG 0 1 2` directly. -/
import Compiler.Front.PipeStdMachine
import Riscv.Direct.SortMergeMachine
import Riscv.Direct.Arr2F
import Riscv.Direct.SortMergeGen

set_option linter.unusedVariables false

namespace Proven

/-! ## Renaming `AStmt` into `BStmt` -/

def rn (i : Fin 8) : Nat := if i.val = 2 then 7 else if i.val = 7 then 8 else i.val

@[simp] theorem rn1 : rn 1 = 1 := rfl
@[simp] theorem rn4 : rn 4 = 4 := rfl

theorem rn_inj : ∀ {i j : Fin 8}, rn i = rn j → i = j := by decide
theorem rn_ne2 : ∀ i : Fin 8, rn i ≠ 2 := by decide
theorem rn_lt : ∀ i : Fin 8, rn i < 9 := by decide

def AExp.rB : AExp → BExp
  | .var i => .var (rn i)
  | .const c => .const c
  | .bin op a b => .bin op a.rB b.rB
  | .ite c a b => .ite c.rB a.rB b.rB

def AStmt.rB : AStmt → BStmt
  | .assign v e => .assign (rn v) e.rB
  | .load v b i => .load (rn v) b i.rB
  | .store b i e => .store b i.rB e.rB
  | .seq p q => .seq p.rB q.rB
  | .loop c b => .loop c.rB b.rB

/-- `τ` holds the `AState` `σ` (renamed), with extra blocks `X` after its blocks -/
def Corr (X : Heap) (σ : AState) (τ : BState) : Prop := (∀ i, τ.env (rn i) = σ.env i) ∧ τ.heap = σ.heap ++ X

theorem AExp.denote_rB {σ : AState} {τ : BState} (h : ∀ i, τ.env (rn i) = σ.env i) :
    ∀ e : AExp, e.rB.denote τ.env = e.denote σ.env
  | .var i => h i
  | .const c => rfl
  | .bin op a b => by simp only [AExp.rB, BExp.denote, AExp.denote, AExp.denote_rB h a, AExp.denote_rB h b]
  | .ite c a b => by
    simp only [AExp.rB, BExp.denote, AExp.denote, AExp.denote_rB h c, AExp.denote_rB h a, AExp.denote_rB h b]

theorem env_set_rB {σe : AEnv} {τe : BEnv} (h : ∀ i, τe (rn i) = σe i) (v : Fin 8) (x : BitVec 64) :
    ∀ i, (τe.set (rn v) x) (rn i) = (σe.set v x) i := by
  intro i
  simp only [BEnv.set, AEnv.set]
  by_cases hv : i = v
  · subst hv; simp
  · have : rn i ≠ rn v := fun e => hv (rn_inj e)
    simp [this, hv, h i]

/-- **Embedding with renaming**: a run of an `AStmt` is a run of its renamed `BStmt`; extra blocks and the
variables outside the image of `rn` are untouched -/
theorem AExec.rB {p : AStmt} {σ σ' : AState} (h : AExec p σ σ') :
    ∀ {X : Heap} {τ : BState}, Corr X σ τ →
    ∃ τ', BExec p.rB τ τ' ∧ Corr X σ' τ' ∧ ∀ j, (∀ i, rn i ≠ j) → τ'.env j = τ.env j := by
  induction h with
  | @assign v e σ =>
    intro X τ ⟨he, hh⟩
    refine ⟨_, .assign, ⟨fun i => ?_, hh⟩, fun j hj => ?_⟩
    · dsimp only; rw [AExp.denote_rB he]; exact env_set_rB he v _ i
    · simp only [BEnv.set, if_neg (Ne.symm (hj v))]
  | @load v b i σ hb hi =>
    intro X τ ⟨he, hh⟩
    have hg : τ.heap[b]? = some σ.heap[b] := by rw [hh, List.getElem?_append_left hb, List.getElem?_eq_getElem hb]
    refine ⟨_, BExec.load' hg (by rw [AExp.denote_rB he]) (List.getElem?_eq_getElem hi), ⟨fun j => ?_, hh⟩,
      fun j hj => ?_⟩
    · exact env_set_rB he v _ j
    · simp only [BEnv.set, if_neg (Ne.symm (hj v))]
  | @store b i e σ hb hi =>
    intro X τ ⟨he, hh⟩
    have hg : τ.heap[b]? = some σ.heap[b] := by rw [hh, List.getElem?_append_left hb, List.getElem?_eq_getElem hb]
    refine ⟨_, BExec.store' (e := e.rB) hg (by rw [AExp.denote_rB he]) hi, ⟨he, ?_⟩, fun j _ => rfl⟩
    dsimp only; rw [hh, List.set_append_left _ _ hb, AExp.denote_rB he]
  | seq _ _ ih1 ih2 =>
    intro X τ hc
    obtain ⟨τ₁, x1, c1, k1⟩ := ih1 hc
    obtain ⟨τ₂, x2, c2, k2⟩ := ih2 c1
    exact ⟨τ₂, .seq x1 x2, c2, fun j hj => (k2 j hj).trans (k1 j hj)⟩
  | loopF hc =>
    intro X τ hcr
    exact ⟨τ, .loopF (by rw [AExp.denote_rB hcr.1]; exact hc), hcr, fun _ _ => rfl⟩
  | loopT hc _ _ ih1 ih2 =>
    intro X τ hcr
    obtain ⟨τ₁, x1, c1, k1⟩ := ih1 hcr
    obtain ⟨τ₂, x2, c2, k2⟩ := ih2 c1
    exact ⟨τ₂, .loopT (by rw [AExp.denote_rB hcr.1]; exact hc) x1 x2, c2, fun j hj => (k2 j hj).trans (k1 j hj)⟩

/-! ## Statement lists -/

def ExecLB : List BStmt → BState → BState → Prop
  | [], σ, σ' => σ' = σ
  | a :: r, σ, σ' => ∃ σ₁, BExec a σ σ₁ ∧ ExecLB r σ₁ σ'

theorem ExecLB.append : ∀ {a b : List BStmt} {σ σ₁ σ₂ : BState}, ExecLB a σ σ₁ → ExecLB b σ₁ σ₂ → ExecLB (a ++ b) σ σ₂
  | [], _, _, _, _, h1, h2 => by cases h1; exact h2
  | _ :: _, _, _, _, _, ⟨τ, h, h1⟩, h2 => ⟨τ, h, ExecLB.append h1 h2⟩

theorem ExecLB.foldl : ∀ {l : List BStmt} {a : BStmt} {σ σ₁ σ' : BState}, BExec a σ σ₁ → ExecLB l σ₁ σ' →
    BExec (l.foldl .seq a) σ σ'
  | [], _, _, _, _, h, h1 => by cases h1; exact h
  | b :: l, a, _, _, _, h, ⟨τ, hb, h1⟩ => ExecLB.foldl (l := l) (a := .seq a b) (.seq h hb) h1

theorem ExecL.rB : ∀ {l : List AStmt} {σ σ' : AState}, ExecL l σ σ' → ∀ {X : Heap} {τ : BState}, Corr X σ τ →
    ∃ τ', ExecLB (l.map AStmt.rB) τ τ' ∧ Corr X σ' τ' ∧ ∀ j, (∀ i, rn i ≠ j) → τ'.env j = τ.env j
  | [], _, _, h, _, τ, hc => by cases h; exact ⟨τ, rfl, hc, fun _ _ => rfl⟩
  | a :: r, _, _, ⟨σ₁, h, h1⟩, X, τ, hc => by
    obtain ⟨τ₁, x1, c1, k1⟩ := h.rB hc
    obtain ⟨τ₂, x2, c2, k2⟩ := ExecL.rB h1 c1
    exact ⟨τ₂, ⟨τ₁, x1, x2⟩, c2, fun j hj => (k2 j hj).trans (k1 j hj)⟩

/-! ## Frame for `BStmt`: a program run on longer blocks -/

theorem BExec.frame {J : Nat → List (BitVec 8)} {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') :
    ∀ {H' : Heap}, Ext J σ.heap H' → ∃ K', BExec p ⟨σ.env, H'⟩ ⟨σ'.env, K'⟩ ∧ Ext J σ'.heap K' := by
  induction h with
  | assign => intro H' hE; exact ⟨H', .assign, hE⟩
  | @load v b i σ hb hi =>
    intro H' hE
    have hb' : b < H'.length := hE.1 ▸ hb
    have e := hE.2 b hb hb'
    have hi' : (i.denote σ.env).toNat < H'[b].length := by rw [e, List.length_append]; omega
    have key : H'[b][(i.denote σ.env).toNat] = σ.heap[b][(i.denote σ.env).toNat] := by
      simp [e, List.getElem_append_left hi]
    have := BExec.load (v := v) (b := b) (i := i) (σ := ⟨σ.env, H'⟩) hb' hi'
    dsimp only at this; rw [key] at this
    exact ⟨H', this, hE⟩
  | @store b i e σ hb hi =>
    intro H' hE
    have hb' : b < H'.length := hE.1 ▸ hb
    have eb := hE.2 b hb hb'
    have hi' : (i.denote σ.env).toNat < H'[b].length := by rw [eb, List.length_append]; omega
    refine ⟨_, BExec.store (b := b) (i := i) (e := e) (σ := ⟨σ.env, H'⟩) hb' hi', by simp [hE.1], fun b' h h' => ?_⟩
    simp only [List.length_set] at h h'
    simp only [List.getElem_set]
    by_cases hbb : b = b'
    · subst hbb; simp only [if_true, eb]; exact List.set_append_left _ _ hi
    · simp only [if_neg hbb]; exact hE.2 b' h h'
  | seq _ _ ih1 ih2 =>
    intro H' hE
    obtain ⟨K₁, x1, hE₁⟩ := ih1 hE
    obtain ⟨K₂, x2, hE₂⟩ := ih2 hE₁
    exact ⟨K₂, .seq x1 x2, hE₂⟩
  | loopF hc => intro H' hE; exact ⟨H', .loopF hc, hE⟩
  | loopT hc _ _ ih1 ih2 =>
    intro H' hE
    obtain ⟨K₁, x1, hE₁⟩ := ih1 hE
    obtain ⟨K₂, x2, hE₂⟩ := ih2 hE₁
    exact ⟨K₂, .loopT hc x1 x2, hE₂⟩

/-! ## Copying `out[0..m)` to `scr[0..m)` -/

def copyC : AStmt := loopV 1 (.seq (.load 6 1 (.var 2)) (.store 2 (.var 2) (.var 6)))

theorem copy_exec {a o scr : List (BitVec 8)} {env : AEnv} {m : Nat} (h1 : env 1 = .ofNat 64 m)
    (hmo : m ≤ o.length) (hms : m ≤ scr.length) (hL : scr.length < 2 ^ 32) :
    ∃ σ' scr', AExec copyC ⟨env, [a, o, scr]⟩ σ' ∧ σ'.heap = [a, o, scr'] ∧ scr'.length = scr.length ∧
      scr'.take m = o.take m ∧ σ'.env 1 = env 1 := by
  obtain ⟨σ', hex, ⟨s, hho, hsl, hpre⟩, h1'⟩ := loopV_exec (c := 1) (by decide) (m := m) (by omega)
    (body := .seq (.load 6 1 (.var 2)) (.store 2 (.var 2) (.var 6)))
    (fun i τ => ∃ s : List (BitVec 8), τ.heap = [a, o, s] ∧ s.length = scr.length ∧ ∀ k, k < i → s[k]? = o[k]?)
    (fun i ⟨env', heap'⟩ hi ⟨s, hho, hsl, hpre⟩ h2 h1 => by
      dsimp only at hho h2 h1; subst hho
      have e2 : ((AExp.var 2).denote env').toNat = i := by
        simp only [AExp.denote, h2]; exact ofNat_toNat_lt (by omega)
      have hl := AExec.load (v := 6) (b := 1) (i := .var 2) (σ := ⟨env', [a, o, s]⟩) (by simp)
        (by rw [e2]; simp; omega)
      simp only [e2, List.getElem_cons_succ, List.getElem_cons_zero] at hl
      have e2' : ((AExp.var 2).denote (env'.set 6 (o[i].setWidth 64))).toNat = i := by
        simp only [AExp.denote, AEnv.set, Fin.reduceEq, if_false]; exact e2
      have hs := AExec.store (b := 2) (i := .var 2) (e := .var 6)
        (σ := ⟨env'.set 6 (o[i].setWidth 64), [a, o, s]⟩) (by simp) (by rw [e2']; simp; omega)
      simp only [e2', List.getElem_cons_succ, List.getElem_cons_zero] at hs
      refine ⟨_, .seq hl hs, ?_, ?_, ⟨s.set i o[i], ?_, by simpa using hsl, fun k hk => ?_⟩⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h2
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact h1
      · simp only [AExp.denote, AEnv.set, if_true, setWidth_setWidth8]; rfl
      · by_cases hki : k = i
        · subst hki; rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hpre k (by omega))
    ⟨env, [a, o, scr]⟩ h1 ⟨scr, rfl, rfl, fun k hk => absurd hk (by omega)⟩
  refine ⟨σ', s, hex, hho, hsl, ?_, by rw [h1', h1]⟩
  apply List.ext_getElem?; intro k
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact hpre k (by omega)
  · rfl

/-! ## The merge sort on the pipe's blocks -/

/-- merge sort `block s0 → out` on the heap `[A, out, scr]`, where block `s0` (0 or 2) starts with the view `cur`
(`m` bytes); the blocks may be longer than `m` -/
theorem msortB_exec (s0 : Nat) (hs0 : s0 = 0 ∨ s0 = 2) {A0 J0 out scr : List (BitVec 8)} {cur : List UInt8}
    {m : Nat} (τ : BState) (hh : τ.heap = [A0 ++ J0, out, scr]) (h1 : τ.env 1 = .ofNat 64 m)
    (hm : cur.length = m) (hout : m ≤ out.length) (hscr : m ≤ scr.length)
    (hsrc : (if s0 = 0 then A0 else scr.take m) = tbs cur) (hn : m < 2 ^ 32) :
    ∃ τ' T, BExec (msortG s0 1 2) τ τ' ∧ τ'.heap = [A0 ++ J0, tbs (cur.mergeSort leU) ++ out.drop m, T] ∧
      T.length = scr.length ∧ ∀ v, v ∉ [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] → τ'.env v = τ.env v := by
  obtain ⟨env, heap⟩ := τ
  dsimp only at hh h1; subst hh
  let H0 : Heap := [A0, out.take m, scr.take m]
  have hl : (tbs cur).length = m := by simp [hm]
  have hS : H0[s0]'(by simp [H0]; omega) = tbs cur := by
    rcases hs0 with rfl | rfl
    · simpa using hsrc
    · simpa using hsrc
  obtain ⟨σ', hex, T, hT, hh'⟩ := msortG_mergeSort s0 1 2 (by omega) (by decide) H0 (tbs cur)
    (by simp [H0]; omega) (by simp [H0]) (by simp [H0]) hS (by simp [H0, hl]; omega) (by simp [H0, hl]; omega)
    ⟨env, H0⟩ rfl (by show env 1 = _; rw [h1, hl]) (by rw [hl]; exact hn)
  let J : Nat → List (BitVec 8) := fun b => if b = 0 then J0 else if b = 1 then out.drop m else scr.drop m
  obtain ⟨K', hexK, hE⟩ := hex.frame (J := J) (H' := [A0 ++ J0, out, scr]) ⟨rfl, fun b h h' => by
      obtain _ | _ | _ | b := b
      · simp [H0, J]
      · simp [H0, J]
      · simp [H0, J]
      · simp [H0] at h; omega⟩
  have hK : K' = [A0 ++ J0, tbs (cur.mergeSort leU) ++ out.drop m, T ++ scr.drop m] := by
    obtain ⟨hl', hg⟩ := hE
    rw [hh'] at hl' hg
    obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ := K' <;> simp [H0] at hl'
    have g0 := hg 0 (by simp [H0]) (by simp); have g1 := hg 1 (by simp [H0]) (by simp)
    have g2 := hg 2 (by simp [H0]) (by simp)
    simp [H0, J, List.set] at g0 g1 g2
    rw [g0, g1, g2, tbs, ← mergeSort_toBitVec]
  subst hK
  refine ⟨_, T ++ scr.drop m, hexK, rfl, by simp [hT, hl]; omega, fun v hv => ?_⟩
  exact hex.env_keep (fun hm' => hv (msortG_assigns s0 1 2 v hm'))

/-! ## The `BStmt` program -/

def XStage.isSort : XStage → Bool
  | .base .sort => true
  | _ => false

theorem XStage.eq_of_isSort {st : XStage} (h : st.isSort = true) : st = .base .sort := by
  cases st with
  | base st => cases st <;> first | rfl | simp [XStage.isSort] at h
  | _ => simp [XStage.isSort] at h

/-- the view is the input itself, from 0, without pending maps -/
def CS.isIn (cs : CS) : Bool := !cs.onOut && !cs.rev && cs.s0 && cs.gs.isEmpty

def sortB (cs : CS) : List BStmt :=
  if cs.isIn then [msortG 0 1 2, (AStmt.assign 4 (.const 0)).rB]
  else (mat cs).map AStmt.rB ++ [copyC.rB, msortG 2 1 2, (AStmt.assign 4 (.const 0)).rB]

def xstageB (st : XStage) (cs : CS) : List BStmt × CS :=
  if st.isSort then (sortB cs, csClean) else ((xstageC st cs).1.map AStmt.rB, (xstageC st cs).2)

theorem xstageB_snd (st : XStage) (cs : CS) : (xstageB st cs).2 = (xstageC st cs).2 := by
  unfold xstageB; split
  · rename_i h; rw [XStage.eq_of_isSort h]; rfl
  · rfl

def xstmtsB : XPipe → CS → List BStmt
  | [], cs => (mat cs).map AStmt.rB
  | st :: r, cs => (xstageB st cs).1 ++ xstmtsB r (xstageB st cs).2

/-- the program with spill slots: `List.mergeSort` is the merge sort -/
def XPipe.progB (p : XPipe) : BStmt := (xstmtsB p cs0).foldl .seq (AStmt.assign 4 (.const 0)).rB

/-- scratch bytes needed: the largest view length at a sort -/
def XPipe.sneed : XPipe → CS → Nat → Nat
  | [], _, _ => 0
  | st :: r, cs, n => max (if st.isSort then n else 0) (XPipe.sneed r (xstageC st cs).2 (st.len n))

def XPipe.sspace (p : XPipe) (n : Nat) : Nat := XPipe.sneed p cs0 n

theorem XPipe.sneed_mono : ∀ (p : XPipe) (cs : CS) {n n' : Nat}, n ≤ n' → XPipe.sneed p cs n ≤ XPipe.sneed p cs n'
  | [], cs, n, n', h => Nat.le_refl _
  | st :: r, cs, n, n', h => by
    simp only [XPipe.sneed]
    have := XPipe.sneed_mono r (xstageC st cs).2 (st.len_mono h)
    split <;> omega

/-! ## Stages in the `BStmt` world -/

/-- the view invariant, through the renaming, with a scratch block of `L2` bytes -/
def InvB (L L2 : Nat) (cs : CS) (xs cur : List UInt8) (τ : BState) : Prop :=
  ∃ σ scr, InvE L cs xs cur σ ∧ Corr [scr] σ τ ∧ scr.length = L2

theorem sort_finish {L L2 : Nat} {xs cur out : List UInt8} {m : Nat} {τ : BState} {T : List (BitVec 8)}
    (hh : τ.heap = [tbs xs, tbs (cur.mergeSort leU) ++ tbs (out.drop m), T]) (hT : T.length = L2)
    (hol : out.length = L) (hm : cur.length = m) (hmL : m ≤ L) (h1 : τ.env 1 = .ofNat 64 m)
    (hn : m < 2 ^ 64) :
    InvB L L2 csClean xs (cur.mergeSort leU) ⟨τ.env.set 4 0, τ.heap⟩ := by
  refine ⟨⟨fun i => (τ.env.set 4 0) (rn i), [tbs xs, tbs (cur.mergeSort leU ++ out.drop m)]⟩, T,
    ⟨_, [], Inv.ofClean (by simp [List.length_mergeSort, hm, hol]; omega) ?_ ?_ ?_⟩,
    ⟨fun i => rfl, by rw [hh, tbs_append]; rfl⟩, hT⟩
  · show (τ.env.set 4 0) 4 = 0; simp [BEnv.set]
  · show (cur.mergeSort leU ++ out.drop m).take ((τ.env.set 4 0) 1).toNat = _
    simp only [BEnv.set, Nat.reduceEqDiff, if_false, h1, ofNat_toNat_lt hn]
    exact List.take_left' (by simp [List.length_mergeSort, hm])
  · show ((τ.env.set 4 0) 1).toNat ≤ L
    simp only [BEnv.set, Nat.reduceEqDiff, if_false, h1, ofNat_toNat_lt hn]; exact hmL

theorem keep1 {τ τ' : BState} (h : ∀ v, v ∉ [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] → τ'.env v = τ.env v) :
    τ'.env 1 = τ.env 1 := h 1 (by decide)

theorem sortB_exec {L L2 : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) (hL2 : L2 < 2 ^ 32)
    {cs : CS} {cur : List UInt8} {τ : BState} (hI : InvB L L2 cs xs cur τ)
    (hsp : Stage.space .sort cs cur.length ≤ L) (hsc : cur.length ≤ L2) :
    ∃ τ', ExecLB (sortB cs) τ τ' ∧ InvB L L2 csClean xs (cur.mergeSort leU) τ' := by
  obtain ⟨σ, scr, hIE, ⟨he, hh⟩, hsl⟩ := hI
  by_cases hin : cs.isIn = true
  · -- sort the input block directly
    obtain ⟨out, fs, hI⟩ := hIE
    obtain ⟨onOut, rev, s0, gs⟩ := cs
    simp only [CS.isIn, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hin
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hin
    have hf := hI.fsok; cases hf
    have h4 := hI.s0 rfl
    have hcur := hI.cur; have hlen := hI.len; have hbd := hI.bound; have hol := hI.olen
    simp only [h4, dirL, applyAll_nil, Bool.false_eq_true, if_false] at hcur hbd
    have hsp' : cur.length ≤ L := by simpa [Stage.space, CS.clean] using hsp
    generalize hmm : (σ.env 1).toNat = m at *
    have h1 : τ.env 1 = .ofNat 64 m := by rw [show (1 : Nat) = rn 1 from rfl, he, ← hmm]; simp
    have hσh := hI.heap
    rw [hσh] at hh
    obtain ⟨τ₁, T, hex, hh₁, hT, hk⟩ := msortB_exec 0 (.inl rfl) (A0 := tbs (xs.take m)) (J0 := tbs (xs.drop m))
      (out := tbs out) (scr := scr) (cur := cur) τ (by rw [hh, ← tbs_append, List.take_append_drop]; rfl) h1
      (by omega) (by simp; omega) (by omega) (by simp [hcur]) (by omega)
    refine ⟨_, ⟨τ₁, hex, _, BExec.assign, rfl⟩, ?_⟩
    have := sort_finish (τ := τ₁) (T := T) (L := L) (L2 := L2) (xs := xs) (cur := cur) (out := out) (m := m)
      (by rw [hh₁, ← tbs_append, List.take_append_drop]; simp only [tbs, List.map_drop]) (by rw [hT, hsl]) hol (by omega) (by omega)
      (by rw [keep1 hk, h1]) (by omega)
    exact this
  · -- materialize to out, copy to scratch, sort scratch → out
    have hsp' : cs.clean = true ∨ cur.length ≤ L := by
      by_cases hcl : cs.clean = true
      · exact .inl hcl
      · simp only [Stage.space, hcl, Bool.false_eq_true, if_false] at hsp; exact .inr hsp
    obtain ⟨σ₁, hex₁, out₁, fs₁, hI₁⟩ := mat_exec hx hL hIE hsp'
    obtain ⟨τ₁, hexB₁, ⟨he₁, hh₁⟩, -⟩ := ExecL.rB hex₁ (X := [scr]) ⟨he, hh⟩
    obtain ⟨rfl, h4, hcur, hm⟩ := hI₁.clean
    have hol := hI₁.olen; have hlen := hI₁.len; have hσh := hI₁.heap
    generalize hmm : (σ₁.env 1).toNat = m at *
    have e1 : σ₁.env 1 = .ofNat 64 m := by rw [← hmm]; simp
    obtain ⟨σ₂, scr', hcp, hh₂, hl₂, htk, k₂⟩ := copy_exec (a := tbs xs) (o := tbs out₁) (scr := scr) (env := σ₁.env)
      e1 (by simp; omega) (by omega) (by omega)
    obtain ⟨τ₂, hexB₂, ⟨he₂, hh₂'⟩, -⟩ := hcp.rB (X := []) (τ := τ₁) ⟨he₁, by rw [hh₁, hσh]; rfl⟩
    rw [hh₂, List.append_nil] at hh₂'
    have h1 : τ₂.env 1 = .ofNat 64 m := by rw [show (1 : Nat) = rn 1 from rfl, he₂, k₂, e1]
    obtain ⟨τ₃, T, hex₃, hh₃, hT, hk⟩ := msortB_exec 2 (.inr rfl) (A0 := tbs xs) (J0 := []) (out := tbs out₁)
      (scr := scr') (cur := cur) τ₂ (by rw [hh₂', List.append_nil]) h1 (by omega) (by simp; omega) (by omega)
      (by simp only [Nat.reduceEqDiff, if_false]; rw [htk, hcur]; simp [tbs, List.map_take]) (by omega)
    refine ⟨_, ?_, sort_finish (τ := τ₃) (T := T) (L := L) (L2 := L2) (xs := xs) (cur := cur) (out := out₁) (m := m)
      (by rw [hh₃, List.append_nil]; simp only [tbs, List.map_drop]) (by rw [hT, hl₂, hsl]) hol (by omega) (by omega)
      (by rw [keep1 hk, h1]) (by omega)⟩
    simp only [sortB, hin, Bool.false_eq_true, if_false]
    exact ExecLB.append hexB₁ ⟨τ₂, hexB₂, τ₃, hex₃, _, BExec.assign, rfl⟩

theorem xstageB_exec {L L2 : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) (hL2 : L2 < 2 ^ 32)
    (st : XStage) {cs : CS} {cur : List UInt8} {τ : BState} (hc : st.chk = none) (hI : InvB L L2 cs xs cur τ)
    (hsp : st.space cs cur.length ≤ L) (hsc : st.isSort = true → cur.length ≤ L2) :
    ∃ τ', ExecLB (xstageB st cs).1 τ τ' ∧ InvB L L2 (xstageB st cs).2 xs (st.denote cur) τ' := by
  by_cases hs : st.isSort = true
  · have e := XStage.eq_of_isSort hs; subst e
    simp only [xstageB, hs, if_true]
    exact sortB_exec hx hL hL2 hI hsp (hsc hs)
  · simp only [xstageB, hs, Bool.false_eq_true, if_false]
    obtain ⟨σ, scr, hIE, hcr, hsl⟩ := hI
    obtain ⟨σ', hex, hI'⟩ := xstage_exec hx hL st hc hIE hsp
    obtain ⟨τ', hexB, hcr', -⟩ := ExecL.rB hex hcr
    exact ⟨τ', hexB, σ', scr, hI', hcr', hsl⟩

theorem xstmtsB_exec {L L2 : Nat} {xs : List UInt8} (hx : xs.length < 2 ^ 32) (hL : L < 2 ^ 32) (hL2 : L2 < 2 ^ 32) :
    ∀ (p : XPipe) {cs : CS} {cur : List UInt8} {τ : BState}, (∀ st ∈ p, st.chk = none) → InvB L L2 cs xs cur τ →
    XPipe.need p cs cur.length ≤ L → XPipe.sneed p cs cur.length ≤ L2 →
    ∃ τ', ExecLB (xstmtsB p cs) τ τ' ∧ InvB L L2 csClean xs (XPipe.denote p cur) τ'
  | [], cs, cur, τ, _, ⟨σ, scr, hIE, hcr, hsl⟩, hsp, _ => by
    obtain ⟨σ', hex, hI'⟩ := mat_exec hx hL hIE (by
      simp only [XPipe.need] at hsp
      by_cases h : cs.clean = true
      · exact .inl h
      · simp only [h, Bool.false_eq_true, if_false] at hsp; exact .inr hsp)
    obtain ⟨τ', hexB, hcr', -⟩ := ExecL.rB hex hcr
    exact ⟨τ', hexB, σ', scr, hI', hcr', hsl⟩
  | st :: r, cs, cur, τ, hc, hI, hsp, hsc => by
    simp only [XPipe.need, XPipe.sneed] at hsp hsc
    have hst := hc st (List.mem_cons_self ..)
    obtain ⟨τ₁, hex₁, hI₁⟩ := xstageB_exec hx hL hL2 st hst hI (by omega) (fun h => by simp [h] at hsc; omega)
    rw [xstageB_snd] at hI₁
    obtain ⟨τ₂, hex₂, hI₂⟩ := xstmtsB_exec hx hL hL2 r (fun s hs => hc s (List.mem_cons_of_mem _ hs)) hI₁
      (Nat.le_trans (XPipe.need_mono r _ (st.denote_len hst cur)) (by omega))
      (Nat.le_trans (XPipe.sneed_mono r _ (st.denote_len hst cur)) (by omega))
    refine ⟨τ₂, ExecLB.append hex₁ ?_, hI₂⟩
    rw [xstageB_snd]; exact hex₂

/-- **Source-level correctness of the `BStmt` translation**: on the heap `[input, out, scr]` -/
theorem XPipe.progB_exec (p : XPipe) (hc : ∀ st ∈ p, st.chk = none) (xs : List UInt8) (out scr : List (BitVec 8))
    (env : BEnv) (h1 : env 1 = .ofNat 64 xs.length) (hx : xs.length < 2 ^ 32)
    (hsp : XPipe.space p xs.length ≤ out.length) (hL : out.length < 2 ^ 32)
    (hss : XPipe.sspace p xs.length ≤ scr.length) (hL2 : scr.length < 2 ^ 32) :
    ∃ τ' out' scr', BExec (XPipe.progB p) ⟨env, [tbs xs, out, scr]⟩ τ' ∧ τ'.heap = [tbs xs, out', scr'] ∧
      out'.length = out.length ∧ out'.take (XPipe.denote p xs).length = tbs (XPipe.denote p xs) ∧
      τ'.env 1 = .ofNat 64 (XPipe.denote p xs).length := by
  have ho : out = tbs (out.map fun b => ⟨b⟩) := by simp [tbs, List.map_map, Function.comp_def]
  generalize out.map (fun b => (⟨b⟩ : UInt8)) = o at ho; subst ho
  have e1 : (env 1).toNat = xs.length := by rw [h1]; exact ofNat_toNat_lt (by omega)
  let τ0 : BState := ⟨env.set 4 0, [tbs xs, tbs o, scr]⟩
  have hI0 : InvB (tbs o).length scr.length cs0 xs xs τ0 :=
    ⟨⟨fun i => τ0.env (rn i), [tbs xs, tbs o]⟩, scr,
      ⟨o, [], rfl, by simp, .nil, by simp [τ0, cs0, BEnv.set, rn1, rn4, e1],
        by simp [τ0, rn1, rn4, cs0, BEnv.set, e1, dirL, applyAll_nil], fun _ => by simp [τ0, rn4, BEnv.set]⟩,
      ⟨fun i => rfl, rfl⟩, rfl⟩
  obtain ⟨τ', hex, σ', scr', ⟨out', fs, hI⟩, ⟨he, hh⟩, hsl⟩ := xstmtsB_exec hx hL hL2 p hc hI0 hsp hss
  obtain ⟨rfl, h4, hcur, hm⟩ := hI.clean
  have hσh := hI.heap
  have : (XPipe.denote p xs).length = (σ'.env 1).toNat := hI.len
  refine ⟨τ', tbs out', scr', ExecLB.foldl (BExec.assign' rfl) hex, by rw [hh, hσh]; rfl, by simpa using hI.olen,
    ?_, ?_⟩
  · rw [this, hcur]; simp [tbs]
  · rw [show (1 : Nat) = rn 1 from rfl, he, this]; simp

end Proven

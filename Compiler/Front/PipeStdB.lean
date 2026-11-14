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

end Proven

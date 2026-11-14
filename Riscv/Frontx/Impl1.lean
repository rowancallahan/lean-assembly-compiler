/- From a generated program to `Implements1` (`Spec/Implements1.lean`), once.

A function `f : ByteArray → β` whose result is one machine value (`repr (f xs)`, `k + 1 ≤ 8` bytes).  The
program `p` (a `Proven.BStmt`: parameter initialisation, then `prog f.lay f.tree 4`) is mapped into the
middle layer (`toMS`), followed by `store8 k` (the result bytes, little-endian, to the output block) and
compiled by the standard entry point `rvF.compBF N [0, 3] [2]`.  Hypotheses: `p.wf` and "variable 2 is
never assigned" (both `decide`), and the source-level run `f.exec` on the heap `[blk xs]`.

Calling convention (that of `Implements1`): `a0` input base, `a1` input length, `a2` work base, `a3` output
base; hence generated programs keep variables 2 and 3 free and put scalars from variable 4 on. -/
import Riscv.Examples.Implements1Ex
import Riscv.Frontx.Rep

set_option linter.unusedVariables false

namespace Proven.Frontx
open Proven Proven.Mach.Riscv LeanRV64D

/-! ## `BStmt.wf` is decidable (well-formedness of a generated program is one `decide`) -/

def vltDec (m : Nat) : (e : BExp) → Decidable (e.vlt m)
  | .var i => inferInstanceAs (Decidable (i < m))
  | .const _ => isTrue trivial
  | .bin _ a b => @instDecidableAnd _ _ (vltDec m a) (vltDec m b)
  | .ite c a b => @instDecidableAnd _ _ (vltDec m c) (@instDecidableAnd _ _ (vltDec m a) (vltDec m b))

instance (m : Nat) (e : BExp) : Decidable (e.vlt m) := vltDec m e

def wfDec (N : Nat) (bv : List Nat) : (p : BStmt) → Decidable (p.wf N bv)
  | .assign v e => inferInstanceAs (Decidable (e.depth < 7 ∧ e.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv))
  | .load v b i => inferInstanceAs (Decidable (i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ b < bv.length))
  | .store b i e =>
    inferInstanceAs (Decidable (i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < bv.length))
  | .seq p q => @instDecidableAnd _ _ (wfDec N bv p) (wfDec N bv q)
  | .loop _ body =>
    @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (wfDec N bv body) inferInstance))

instance (N : Nat) (bv : List Nat) (p : BStmt) : Decidable (p.wf N bv) := wfDec N bv p

/-- a run of a `Proven.BStmt` program is a run of its image in the middle layer, with more byte blocks behind
its own and any word heap -/
theorem exec_up {p : Proven.BStmt} {σ σ' : Proven.BState} (h : Proven.BExec p σ σ') (X : Heap) (w : Mach.WHeap) :
    Mach.BExec (toMS p) ⟨σ.env, σ.heap ++ X, w⟩ ⟨σ'.env, σ'.heap ++ X, w⟩ := by
  induction h with
  | @assign v e σ =>
    have := Mach.BExec.assign (v := v) (e := toMB e) (σ := ⟨σ.env, σ.heap ++ X, w⟩)
    rw [denote_toMB] at this; exact this
  | @load v b i σ hb hi =>
    have hb' : b < (σ.heap ++ X).length := by rw [List.length_append]; omega
    have hg : (σ.heap ++ X)[b] = σ.heap[b] := List.getElem_append_left hb
    have := Mach.BExec.load (v := v) (i := toMB i) (σ := ⟨σ.env, σ.heap ++ X, w⟩) hb'
      (by show _ < _; rw [denote_toMB, hg]; exact hi)
    simp only [denote_toMB, hg] at this; exact this
  | @store b i e σ hb hi =>
    have hb' : b < (σ.heap ++ X).length := by rw [List.length_append]; omega
    have hg : (σ.heap ++ X)[b] = σ.heap[b] := List.getElem_append_left hb
    have := Mach.BExec.store (e := toMB e) (i := toMB i) (σ := ⟨σ.env, σ.heap ++ X, w⟩) hb'
      (by show _ < _; rw [denote_toMB, hg]; exact hi)
    simp only [denote_toMB, hg, List.set_append_left _ _ hb] at this; exact this
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | loopF hc => exact .loopF (by show _ = _; rw [denote_toMB]; exact hc)
  | loopT hc _ _ ih1 ih2 => exact .loopT (by show _ ≠ _; rw [denote_toMB]; exact hc) ih1 ih2

/-- the variables a program assigns -/
def avars : Proven.BStmt → List Nat
  | .assign v _ | .load v _ _ => [v]
  | .store _ _ _ => []
  | .seq p q => avars p ++ avars q
  | .loop _ b => avars b

theorem compB_wv (bv wv : List Nat) : ∀ p : Proven.BStmt, rvF.compB bv wv (toMS p) = rvF.compB bv [] (toMS p)
  | .assign _ _ | .load _ _ _ | .store _ _ _ => rfl
  | .seq p q => by simp only [toMS, MachineF.compB, compB_wv bv wv p, compB_wv bv wv q]
  | .loop c b => by simp only [toMS, MachineF.compB, compB_wv bv wv b]

/-- well-formedness with word-base variables `wv` the program never assigns -/
theorem wfB_up (N : Nat) (bv wv : List Nat) : ∀ p : Proven.BStmt, p.wf N bv → (∀ v ∈ avars p, v ∉ wv) →
    rvF.wfB N bv wv (toMS p)
  | .assign v e, hp, ha => by
    obtain ⟨h1, h2, h3, h4, _⟩ := (code_compB N bv _ hp).2
    exact ⟨h1, h2, h3, h4, ha v (by simp [avars])⟩
  | .load v b i, hp, ha => by
    obtain ⟨h1, h2, h3, h4, _, h6⟩ := (code_compB N bv _ hp).2
    exact ⟨h1, h2, h3, h4, ha v (by simp [avars]), h6⟩
  | .store b i e, hp, ha => (code_compB N bv _ hp).2
  | .seq p q, hp, ha =>
    ⟨wfB_up N bv wv p hp.1 fun v hv => ha v (by simp [avars, hv]),
      wfB_up N bv wv q hp.2 fun v hv => ha v (by simp [avars, hv])⟩
  | .loop c b, hp, ha => by
    obtain ⟨h1, h2, _, h4, h5⟩ := (code_compB N bv _ hp).2
    refine ⟨h1, h2, wfB_up N bv wv b hp.2.2.1 fun v hv => ha v (by simpa [avars] using hv), ?_, ?_⟩
    · rw [compB_wv]; exact h4
    · rw [compB_wv]; exact h5

theorem store8_wf (N : Nat) : ∀ k, k < 8 → rvF.wfB N [0, 3] [2] (store8 k)
  | 0, _ => by simp [store8, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]
  | k + 1, h => ⟨store8_wf N k (by omega), by simp [MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]⟩

/-- **Generated program ⇒ `Implements1`.** -/
theorem implements1_of_frontx {β : Type} (f : ByteArray → β) (encB : β → List UInt8) (repr : β → BitVec 64)
    (k : Nat) (hk : k < 8)
    (henc : ∀ b, (encB b).map (·.toBitVec) =
      (List.range (k + 1)).map fun j => BitVec.ofNat 8 ((repr b).toNat / 256 ^ j))
    (N : Nat) (hN : N ≤ 16) (p : Proven.BStmt) (hwf : p.wf N [0, 3]) (hnw : ∀ v ∈ avars p, v ∉ [2])
    (hex : ∀ (xs : ByteArray) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 → (∀ j, 8 ≤ j → env j = 0) →
      ∃ σ', Proven.BExec p ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = repr (f xs) ∧ σ'.heap = [blk xs]) :
    Implements1With (fun xs : ByteArray => xs.data.toList) encB
      (rvF.codeF (rvF.compBF N [0, 3] [2] (.seq (toMS p) (store8 k)))) f (fun _ => 8 * (N + 1) + 7) := by
  refine implements1_of_exec _ encB f N hN _ ⟨wfB_up N _ _ p hwf hnw, store8_wf N k hk⟩ (fun _ => 0) _
    (fun n => by dsimp only; omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := by simp [ByteArray.size]
  obtain ⟨σ', hx, h4, hh⟩ := hex a env (by rw [h1, hsz]; rfl) (by rw [← hsz]; exact hlt) h8
  have hx' := exec_up hx [out] [tbl]
  rw [hh] at hx'
  have hlen : (encB (f a)).length = k + 1 := by
    have := congrArg List.length (henc (f a)); simpa using this
  rw [hlen] at hout ⊢
  obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (repr (f a)) k hk ⟨σ'.env, [blk a, out], [tbl]⟩ _ out rfl h4
    (by omega) rfl
  refine ⟨_, out', .seq hx' hst, rfl, ?_, ?_, fun h => nomatch h⟩
  · apply List.ext_getElem?; intro i
    rw [henc]
    by_cases hi : i < k + 1
    · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)

/-! ## Result encodings -/

/-- `k` little-endian bytes of a number -/
theorem leN_bytes : ∀ (k n : Nat),
    (leN k n).map (·.toBitVec) = (List.range k).map fun j => BitVec.ofNat 8 (n / 256 ^ j)
  | 0, _ => rfl
  | k + 1, n => by
    rw [leN, List.map_cons, leN_bytes k (n / 256), List.range_succ_eq_map, List.map_cons, List.map_map, u8]
    simp [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- a result type of generated code: its machine value and its bytes (`k + 1` little-endian bytes of the value) -/
class Res (β : Type) where
  repr : β → BitVec 64
  k : Nat
  hk : k < 8
  enc : β → List UInt8
  henc : ∀ b, (enc b).map (·.toBitVec) = (List.range (k + 1)).map fun j => BitVec.ofNat 8 ((repr b).toNat / 256 ^ j)

instance : Res (BitVec 64) := ⟨id, 7, by decide, fun w => leN 8 w.toNat, fun w => leN_bytes 8 _⟩
instance : Res UInt64 := ⟨r64, 7, by decide, fun w => leN 8 w.toNat, fun w => leN_bytes 8 _⟩
/-- a `Nat` result is returned mod `2 ^ 64` -/
instance : Res Nat := ⟨rN, 7, by decide, fun n => leN 8 (n % 2 ^ 64), fun n => leN_bytes 8 _⟩
instance : Res UInt32 := ⟨r32, 3, by decide, fun w => leN 4 w.toNat, fun w => by
  rw [leN_bytes]; simp [r32]⟩
instance : Res UInt8 := ⟨r8, 0, by decide, fun w => leN 1 w.toNat, fun w => by
  rw [leN_bytes]; simp [r8]⟩
instance : Res Bool := ⟨rB, 0, by decide, fun b => [if b then 1 else 0], fun b => by cases b <;> rfl⟩

/-- the code of an entry point -/
def entryCode (β : Type) [Res β] (N : Nat) (p : Proven.BStmt) : List (BitVec 32) :=
  rvF.codeF (rvF.compBF N [0, 3] [2] (.seq (toMS p) (store8 (Res.k β))))

theorem implements1_res {β : Type} [Res β] (f : ByteArray → β) (N : Nat) (hN : N ≤ 16) (p : Proven.BStmt)
    (hwf : p.wf N [0, 3]) (hnw : ∀ v ∈ avars p, v ∉ [2])
    (hex : ∀ (xs : ByteArray) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 → (∀ j, 8 ≤ j → env j = 0) →
      ∃ σ', Proven.BExec p ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = Res.repr (f xs) ∧ σ'.heap = [blk xs]) :
    Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc (entryCode β N p) f (fun _ => 8 * (N + 1) + 7) :=
  implements1_of_frontx f Res.enc Res.repr (Res.k β) Res.hk Res.henc N hN p hwf hnw hex

/-- `frontx_implements g` (after `frontx_entry g`): `g.code` and the machine theorem `g.implements1` -/
macro "frontx_implements " g:ident : command => do
  let n := g.getId
  let prog := Lean.mkIdent (n ++ `prog); let slots := Lean.mkIdent (n ++ `slots)
  let exec := Lean.mkIdent (n ++ `exec); let code := Lean.mkIdent (n ++ `code)
  let thm := Lean.mkIdent (n ++ `implements1)
  `(def $code : List (BitVec 32) := entryCode _ $slots $prog
    theorem $thm : Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc $code $g
        (fun _ => 8 * ($slots + 1) + 7) :=
      implements1_res $g $slots (by decide) $prog (by decide +kernel) (by decide +kernel) $exec)

end Proven.Frontx

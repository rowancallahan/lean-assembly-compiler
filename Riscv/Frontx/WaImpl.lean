/- Word arrays (NOTES section 20), compiler part 5: a program over the input bytes ⇒ `Implements1`.

The entry environment is the input `xs` (block 0, its length in variable 1); the program's statements
are followed by the result bytes (`v4 := result; store8`), compiled by the optimised back end
`compBFO N [0, 3] [2]` (`Riscv/Back/Implements1Opt.lean`).  The work block holds the `wn` words of the
arrays (word block 0 = work base) below the frame of the back end: `space n = 8 wn + 8 (N + 1) + 7`. -/
import Riscv.Frontx.WaPg
import Riscv.Frontx.Impl1

namespace Proven.WA
open Proven Proven.Frontx Proven.Mach Proven.Mach.Riscv LeanRV64D

def MB.maxv : MB → Nat
  | .var i => i + 1
  | .const _ => 0
  | .bin _ a b => max (MB.maxv a) (MB.maxv b)
  | .ite c a b => max (MB.maxv c) (max (MB.maxv a) (MB.maxv b))

def MS.maxv : MS → Nat
  | .assign v e => max (v + 1) (MB.maxv e)
  | .load v _ i | .load64 v _ i => max (v + 1) (MB.maxv i)
  | .store _ i e | .store64 _ i e => max (MB.maxv i) (MB.maxv e)
  | .seq p q => max (MS.maxv p) (MS.maxv q)
  | .loop c b => max (MB.maxv c) (MS.maxv b)

/-! ## `wfB` is decidable -/

def mvltDec (m : Nat) : (e : Mach.BExp) → Decidable (e.vlt m)
  | .var i => inferInstanceAs (Decidable (i < m))
  | .const _ => isTrue trivial
  | .bin _ a b => @instDecidableAnd _ _ (mvltDec m a) (mvltDec m b)
  | .ite c a b => @instDecidableAnd _ _ (mvltDec m c) (@instDecidableAnd _ _ (mvltDec m a) (mvltDec m b))

instance (m : Nat) (e : Mach.BExp) : Decidable (e.vlt m) := mvltDec m e

def wfBDec (N : Nat) (bv wv : List Nat) : (p : Mach.BStmt) → Decidable (rvF.wfB N bv wv p)
  | .assign v e => inferInstanceAs (Decidable (e.depth < 7 ∧ e.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv))
  | .load v b i => inferInstanceAs (Decidable (i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv ∧ b < bv.length))
  | .store b i e =>
    inferInstanceAs (Decidable (i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < bv.length))
  | .seq p q => @instDecidableAnd _ _ (wfBDec N bv wv p) (wfBDec N bv wv q)
  | .loop c body =>
    @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (wfBDec N bv wv body) (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (2 * _ < 2048))) (inferInstanceAs (Decidable (0 < _ ∧ 2 * _ ≤ 2 ^ 19))))))
  | .load64 v b i =>
    inferInstanceAs (Decidable (i.depth < 6 ∧ i.vlt (8 + N) ∧ v < 8 + N ∧ v ∉ bv ∧ v ∉ wv ∧ b < wv.length))
  | .store64 b i e =>
    inferInstanceAs (Decidable (i.depth < 6 ∧ e.depth < 6 ∧ i.vlt (8 + N) ∧ e.vlt (8 + N) ∧ b < wv.length))

instance (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) : Decidable (rvF.wfB N bv wv p) := wfBDec N bv wv p

/-- the input's location: block 0, length in variable 1 -/
def inLoc : Loc := ⟨1, true, 0, none⟩

/-- the whole program: the statements, then the result's bytes -/
def wholeProg {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : MS :=
  .seq (p.comp [inLoc] 4 0).1 (.seq (.assign 4 (.var (p.comp [inLoc] 4 0).2.1.v)) (store8 k))

/-- slots of the back end: every variable from 8 on -/
def wholeN {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : Nat := (wholeProg p k).maxv - 8

/-- words of the work block the arrays need -/
def wholeW {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List Loc) : Nat := (p.comp L 4 0).2.2

def waCode {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : List (BitVec 32) :=
  compBFO (wholeN p k) [0, 3] [2] (wholeProg p k)

theorem rel_input (xs : ByteArray) (env : Mach.BEnv) (out : List (BitVec 8)) (W : List (BitVec 64))
    (h1 : env 1 = BitVec.ofNat 64 xs.data.toList.length) (h32 : xs.size < 2 ^ 32) :
    Rel [.ar .ba] [inLoc] (xs, ()) ⟨env, [xs.data.toList.map (·.toBitVec), out], [W]⟩ := by
  refine ⟨⟨?_, h32, ?_⟩, trivial⟩
  · show env 1 = _; rw [h1]; simp [AK.size, rN]
  · show AR _ _ .ba inLoc xs
    unfold AR
    rw [if_pos (show inLoc.inp = true from rfl)]
    simp only [List.getD_cons_zero, List.length_map, Array.length_toList, AK.size]
    refine ⟨Nat.le_refl _, fun j hj => ?_⟩
    simp only [List.getElem?_map, Array.getElem?_toList, Option.map_map]
    rw [show xs.data[j]? = some xs.data[j] from Array.getElem?_eq_getElem hj]
    simp only [Option.map_some, AK.w, AK.el, AK.get, Ty.rep]
    rw [getElem!_pos xs j hj]; rfl

/-- **A program with a scalar result ⇒ `Implements1`.** -/
theorem implements1_wa {t : Ty} {β : Type} [Res β] (f : ByteArray → β) (p : Pg [.ar .ba] (.sc t))
    (cv : t.T → β) (hcv : ∀ y, Res.repr (cv y) = t.rep y)
    (hk : Res.k β < 8)
    (hN : wholeN p (Res.k β) ≤ NS) (hwf : p.wf [inLoc] 4 0 = true)
    (hmwf : rvF.wfB (wholeN p (Res.k β)) [0, 3] [2] (wholeProg p (Res.k β)))
    (h32 : wholeW p [inLoc] < 2 ^ 32)
    (hgood : ∀ xs : ByteArray, xs.size < 2 ^ 32 → ∃ y, p.Good (xs, ()) y ∧ cv y = f xs) :
    Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc (waCode p (Res.k β)) f
      (fun _ => 8 * wholeW p [inLoc] + 8 * (wholeN p (Res.k β) + 1) + 7) := by
  refine implements1_of_execOW _ Res.enc f (wholeN p (Res.k β)) hN (wholeProg p (Res.k β)) hmwf
    (fun _ => wholeW p [inLoc]) _ (fun n => Nat.le_refl _) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨y, hg, hy⟩ := hgood a (by rw [← hsz]; exact hlt)
  have hR := rel_input a env out tbl h1 (by rw [← hsz]; exact hlt)
  obtain ⟨σ1, W1, e1, h1', w1, s1⟩ := Pg.comp_ok [inLoc] p (a, ()) _ 4 0 tbl y hR (by simp) (by
      intro l hl; simp [inLoc] at hl; subst hl; decide) (fun l hl => by simp [inLoc] at hl; subst hl; exact .inl rfl)
    hwf hg rfl (by rw [htl]; exact Nat.le_refl _) (by rw [htl]; exact h32)
  have hlen : (Res.enc (f a)).length = Res.k β + 1 := by
    have := congrArg List.length (Res.henc (f a)); simpa using this
  let σ2 : Mach.BState := ⟨σ1.env.set 4 (σ1.env (p.comp [inLoc] 4 0).2.1.v), σ1.heap, σ1.wheap⟩
  have h4 : σ2.env 4 = Res.repr (f a) := by
    simp only [σ2, set_eq]; rw [← hy, hcv]; exact s1
  obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (Res.repr (f a)) (Res.k β) hk σ2 _ out
    (by simp only [σ2]; rw [h1']) h4 (by omega) rfl
  refine ⟨_, out', .seq e1 (.seq .assign hst), rfl, ?_, ?_, fun h => nomatch h⟩
  · rw [hlen]
    apply List.ext_getElem?; intro i
    rw [Res.henc]
    by_cases hi : i < Res.k β + 1
    · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · rw [hlen]
    exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)

end Proven.WA

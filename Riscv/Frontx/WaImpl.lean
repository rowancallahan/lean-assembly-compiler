/- Word arrays (NOTES section 20), compiler part 5: a program over the input bytes ⇒ `Implements1`.

The entry environment is the input `xs` (block 0, its length in variable 1); the program's statements
are followed by the result bytes (`v4 := result; store8`), compiled by the optimised back end
`compBFO N [0, 3] [2]` (`Riscv/Back/Implements1Opt.lean`).  The work block holds the `wn` words of the
arrays (word block 0 = work base) below the frame of the back end: `space n = 8 wn + 8 (N + 1) + 7`. -/
import Riscv.Frontx.WaPg
import Riscv.Frontx.Impl1
import Riscv.Frontx.Bytes

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
  | .mop _ v a b => max (v + 1) (max (MB.maxv a) (MB.maxv b))

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
  | .mop _ _ _ _ => inferInstanceAs (Decidable False)

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

/-! ## Array results: the elements' bytes to the output block -/

/-- `n + 1` bytes of `v >>> s` to output bytes `q + o ..` (`q` a variable) -/
def store1 (v q o s : Nat) : MS :=
  .store 1 (.bin .add (.var q) (.const (BitVec.ofNat 64 o))) (.bin .lshr (.var v) (.const (BitVec.ofNat 64 s)))

def storeV (v q o s : Nat) : Nat → MS
  | 0 => store1 v q o s
  | n + 1 => .seq (store1 v q o s) (storeV v q (o + 1) (s + 8) n)

theorem storeV_exec (v q : Nat) (w : BitVec 64) (X : List (BitVec 8)) (W : Mach.WHeap) : ∀ (n o s : Nat)
    (O : List (BitVec 8)) (env : Mach.BEnv) (Q : Nat), env v = w → env q = rN Q → Q + o + n + 1 ≤ O.length →
    O.length < 2 ^ 32 → s + 8 * n < 64 →
    Mach.BExec (storeV v q o s n) ⟨env, [X, O], W⟩ ⟨env, [X, wrO O (Q + o) (leN (n + 1) (w.toNat / 2 ^ s))], W⟩
  | 0, o, s, O, env, Q, hv, hq, hl, hO, hs => by
    have h := Mach.BExec.store (b := 1) (i := .bin .add (.var q) (.const (BitVec.ofNat 64 o)))
      (e := .bin .lshr (.var v) (.const (BitVec.ofNat 64 s))) (σ := ⟨env, [X, O], W⟩) (by simp)
      (by simp [Mach.BExp.denote, Op.eval, hq, rN]; omega)
    have hidx : (Op.eval .add (env q) (BitVec.ofNat 64 o)).toNat = Q + o := by
      simp [Op.eval, hq, rN]; omega
    simp only [Mach.BExp.denote, hv, List.getElem_cons_succ, List.getElem_cons_zero, List.set_cons_succ,
      List.set_cons_zero] at h
    rw [hidx] at h
    rw [byte_shr w s (by omega)] at h
    rw [leN, leN, wrO_single _ _ _ (by omega), storeV]
    exact h
  | n + 1, o, s, O, env, Q, hv, hq, hl, hO, hs => by
    have h1 := storeV_exec v q w X W 0 o s O env Q hv hq (by omega) hO (by omega)
    have h2 := storeV_exec v q w X W n (o + 1) (s + 8) (wrO O (Q + o) (leN 1 (w.toNat / 2 ^ s))) env Q hv hq
      (by rw [wrO_length _ _ _ (by simp [leN_length]; omega)]; omega)
      (by rw [wrO_length _ _ _ (by simp [leN_length]; omega)]; exact hO) (by omega)
    have e : leN (n + 1 + 1) (w.toNat / 2 ^ s) = leN 1 (w.toNat / 2 ^ s) ++ leN (n + 1) (w.toNat / 2 ^ (s + 8)) := by
      rw [leN, leN, leN, Nat.pow_add, ← Nat.div_div_eq_div_mul]; rfl
    rw [e, wrO_append _ _ _ _ (by rw [leN_length]; omega), show (leN 1 (w.toNat / 2 ^ s)).length = 1 from leN_length 1 _,
      show Q + o + 1 = Q + (o + 1) by omega]
    rw [storeV]
    exact .seq h1 h2

/-- the bytes of an array result: every element `width` bytes, little-endian (`Nat` mod `2 ^ 64`) -/
def encArr (k : AK) (a : k.T) : List UInt8 :=
  (List.range (AK.size k a)).flatMap fun j => leN k.el.width (AK.w k a j).toNat

theorem encPre_succ (k : AK) (a : k.T) (j : Nat) :
    (List.range (j + 1)).flatMap (fun i => leN k.el.width (AK.w k a i).toNat) =
      (List.range j).flatMap (fun i => leN k.el.width (AK.w k a i).toNat) ++ leN k.el.width (AK.w k a j).toNat := by
  simp [List.range_succ, List.flatMap_append]

theorem encPre_length (k : AK) (a : k.T) (j : Nat) :
    ((List.range j).flatMap (fun i => leN k.el.width (AK.w k a i).toNat)).length = k.el.width * j := by
  induction j with
  | zero => simp
  | succ j ih => rw [encPre_succ, List.length_append, ih, leN_length]; simp [Nat.mul_succ]

/-- `j := 0; q := 0; while j < size { x := a[j]; out[q ..] := bytes of x; j := j + 1; q := q + width }` -/
def outLoop (l : Loc) (w d : Nat) : MS :=
  .seq (.assign d (.const 0)) (.seq (.assign (d + 1) (.const 0)) (.loop (.bin .ult (.var d) (.var l.v))
    (.seq (if l.inp then .load (d + 2) 0 (.var d) else .load64 (d + 2) 0 (.bin .add (.var d) (.const (BitVec.ofNat 64 l.off))))
      (.seq (storeV (d + 2) (d + 1) 0 0 (w - 1))
        (.seq (.assign d (.bin .add (.var d) (.const 1))) (.assign (d + 1) (.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 w)))))))))

theorem Ty.width_pos (t : Ty) : 1 ≤ t.width ∧ t.width ≤ 8 := by cases t <;> decide

set_option maxHeartbeats 1000000 in
theorem outLoop_iter {k : AK} (a : k.T) (l : Loc) (d : Nat) (X O0 : List (BitVec 8)) (W : List (BitVec 64))
    (hA : AR X W k l a) (hd : l.v < d) (hcap : k.el.width * AK.size k a ≤ O0.length) (hO : O0.length < 2 ^ 32)
    (h32 : AK.size k a < 2 ^ 32) :
    ∀ (m j : Nat) (env : Mach.BEnv), AK.size k a - j = m → j ≤ AK.size k a → env d = rN j →
      env (d + 1) = rN (k.el.width * j) → env l.v = rN (AK.size k a) →
      ∃ env', Mach.BExec (.loop (.bin .ult (.var d) (.var l.v))
        (.seq (if l.inp then .load (d + 2) 0 (.var d) else .load64 (d + 2) 0 (.bin .add (.var d) (.const (BitVec.ofNat 64 l.off))))
          (.seq (storeV (d + 2) (d + 1) 0 0 (k.el.width - 1))
            (.seq (.assign d (.bin .add (.var d) (.const 1)))
              (.assign (d + 1) (.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 k.el.width))))))))
        ⟨env, [X, wrO O0 0 ((List.range j).flatMap fun i => leN k.el.width (AK.w k a i).toNat)], [W]⟩
        ⟨env', [X, wrO O0 0 (encArr k a)], [W]⟩ ∧ env' (d + 1) = rN (encArr k a).length ∧
        ∀ i, i < d → env' i = env i
  | 0, j, env, hm, hj, h0, h1, hs => by
    have hjn : j = AK.size k a := by omega
    subst hjn
    refine ⟨env, .loopF ?_, ?_, fun _ _ => rfl⟩
    · simp only [Mach.BExp.denote, Op.eval, h0, hs]; simp
    · rw [h1]; unfold encArr; rw [encPre_length]
  | m + 1, j, env, hm, hj, h0, h1, hs => by
    have hjn : j < AK.size k a := by omega
    have hw := Ty.width_pos k.el
    let O1 := wrO O0 0 ((List.range j).flatMap fun i => leN k.el.width (AK.w k a i).toNat)
    have hpre := encPre_length k a j
    have hO1 : O1.length = O0.length := wrO_length _ _ _ (by rw [hpre]; have := Nat.mul_le_mul_left k.el.width (show j ≤ AK.size k a by omega); omega)
    have hlt : (Mach.BExp.bin .ult (.var d) (.var l.v)).denote env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, h0, hs]
      rw [if_pos (by simp only [rN_lt (by omega : j < 2 ^ 64) (by omega : AK.size k a < 2 ^ 64)]; exact hjn)]; decide
    have hl1 := load_ok (σ := ⟨env, [X, O1], [W]⟩) (by simpa using hA) d (d + 2) j hjn h0 (by omega)
    let env1 := env.set (d + 2) (AK.w k a j)
    have hst := storeV_exec (d + 2) (d + 1) (AK.w k a j) X [W] (k.el.width - 1) 0 0 O1 env1 (k.el.width * j) set_eq
      (by simp only [env1, set_ne (show d + 1 ≠ d + 2 by omega)]; exact h1)
      (by rw [hO1]; have := Nat.mul_le_mul_left k.el.width (show j + 1 ≤ AK.size k a by omega); simp [Nat.mul_succ] at this; omega)
      (by rw [hO1]; exact hO) (by omega)
    rw [show k.el.width - 1 + 1 = k.el.width by omega, Nat.pow_zero, Nat.div_one] at hst
    simp only [Nat.add_zero] at hst
    have hO2 : wrO O1 (k.el.width * j) (leN k.el.width (AK.w k a j).toNat) =
        wrO O0 0 ((List.range (j + 1)).flatMap fun i => leN k.el.width (AK.w k a i).toNat) := by
      rw [encPre_succ, wrO_append _ _ _ _ (by rw [hpre]; have := Nat.mul_le_mul_left k.el.width (show j ≤ AK.size k a by omega); omega), hpre, Nat.zero_add]
    rw [hO2] at hst
    let env2 := env1.set d ((Mach.BExp.bin .add (.var d) (.const 1)).denote env1)
    let env3 := env2.set (d + 1) ((Mach.BExp.bin .add (.var (d + 1)) (.const (BitVec.ofNat 64 k.el.width))).denote env2)
    obtain ⟨env', e', h1', k'⟩ := outLoop_iter a l d X O0 W hA hd hcap hO h32 m (j + 1) env3 (by omega) (by omega)
      (by simp only [env3, env2, env1, set_ne (show d ≠ d + 1 by omega), set_eq, Mach.BExp.denote, Op.eval,
          set_ne (show d ≠ d + 2 by omega), h0, rN_add]; rfl)
      (by simp only [env3, env2, env1, set_eq, Mach.BExp.denote, Op.eval, set_ne (show d + 1 ≠ d by omega),
          set_ne (show d + 1 ≠ d + 2 by omega), h1]
          rw [show k.el.width * (j + 1) = k.el.width * j + k.el.width from Nat.mul_succ _ _, rN_add]; rfl)
      (by simp only [env3, env2, env1, set_ne (show l.v ≠ d + 1 by omega), set_ne (show l.v ≠ d by omega),
          set_ne (show l.v ≠ d + 2 by omega)]; exact hs)
    refine ⟨env', .loopT hlt (.seq hl1 (.seq hst (.seq .assign .assign))) e', h1', fun i hi => ?_⟩
    rw [k' i hi]
    simp only [env3, env2, env1, set_ne (show i ≠ d + 1 by omega), set_ne (show i ≠ d by omega),
      set_ne (show i ≠ d + 2 by omega)]

/-- the whole program of an array result: the statements, then the elements' bytes, `a1 :=` their number -/
def outBase {Γ : List Sl} {R : Sl} (p : Pg Γ R) (L : List Loc) : Nat := max (p.comp L 4 0).1.maxv 4

def wholeProgA {k : AK} (p : Pg [.ar .ba] (.ar k)) : MS :=
  .seq (p.comp [inLoc] 4 0).1 (.seq (outLoop (p.comp [inLoc] 4 0).2.1 k.el.width (outBase p [inLoc]))
    (.assign 1 (.var (outBase p [inLoc] + 1))))

def wholeNA {k : AK} (p : Pg [.ar .ba] (.ar k)) : Nat := (wholeProgA p).maxv - 8

def waCodeA {k : AK} (p : Pg [.ar .ba] (.ar k)) : List (BitVec 32) :=
  compBFO (wholeNA p) [0, 3] [2] (wholeProgA p)

/-- **A program with an array result ⇒ `Implements1`** (the elements' bytes, their number in `a1`). -/
theorem implements1_waA {k : AK} (f : ByteArray → k.T) (p : Pg [.ar .ba] (.ar k))
    (hN : wholeNA p ≤ NS) (hwf : p.wf [inLoc] 4 0 = true)
    (hmwf : rvF.wfB (wholeNA p) [0, 3] [2] (wholeProgA p)) (h32 : wholeW p [inLoc] < 2 ^ 32)
    (hd : (p.comp [inLoc] 4 0).2.1.v < outBase p [inLoc])
    (hgood : ∀ xs : ByteArray, xs.size < 2 ^ 32 → p.Good (xs, ()) (f xs)) :
    Implements1With (fun xs : ByteArray => xs.data.toList) (encArr k) (waCodeA p) f
      (fun _ => 8 * wholeW p [inLoc] + 8 * (wholeNA p + 1) + 7) (retLen := true) := by
  refine implements1_of_execOW _ (encArr k) f (wholeNA p) hN (wholeProgA p) hmwf
    (fun _ => wholeW p [inLoc]) _ (fun n => Nat.le_refl _) _ true ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  have hR := rel_input a env out tbl h1 (by rw [← hsz]; exact hlt)
  obtain ⟨σ1, W1, e1, h1', w1, s1⟩ := Pg.comp_ok [inLoc] p (a, ()) _ 4 0 tbl (f a) hR (by simp) (by
      intro l hl; simp [inLoc] at hl; subst hl; decide) (fun l hl => by simp [inLoc] at hl; subst hl; exact .inl rfl)
    hwf (hgood a (by rw [← hsz]; exact hlt)) rfl (by rw [htl]; exact Nat.le_refl _) (by rw [htl]; exact h32)
  generalize hl : (p.comp [inLoc] 4 0).2.1 = l at s1 hd
  generalize hdd : outBase p [inLoc] = d at hd
  obtain ⟨env1, heap1, wheap1⟩ := σ1
  simp only at h1' w1; subst h1' w1
  obtain ⟨hv, hs32, hA⟩ := s1.ar
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hA
  have hcap : k.el.width * AK.size k (f a) ≤ out.length := by
    have := encPre_length k (f a) (AK.size k (f a)); unfold encArr at hout; omega
  let env2 := (env1.set d 0).set (d + 1) 0
  obtain ⟨env', e3, hq, hk⟩ := outLoop_iter (f a) l d _ out W1 hA hd hcap hol hs32 _ 0 env2 rfl (Nat.zero_le _)
    (by simp only [env2, set_ne (show d ≠ d + 1 by omega), set_eq]; rfl)
    (by simp only [env2, set_eq]; rfl)
    (by simp only [env2, set_ne (show l.v ≠ d + 1 by omega), set_ne (show l.v ≠ d by omega)]; exact hv)
  simp only [List.range_zero, List.flatMap_nil, wrO_nil] at e3
  have e2 : Mach.BExec (outLoop l k.el.width d) ⟨env1, [a.data.toList.map (·.toBitVec), out], [W1]⟩
      ⟨env', [a.data.toList.map (·.toBitVec), wrO out 0 (encArr k (f a))], [W1]⟩ :=
    .seq .assign (.seq .assign e3)
  refine ⟨_, wrO out 0 (encArr k (f a)), .seq e1 (by rw [hl, hdd]; exact .seq e2 .assign), rfl,
    wrO_take _ _ hout, wrO_drop _ _, fun _ => ?_⟩
  show (env'.set 1 _) 1 = _
  simp only [set_eq, Mach.BExp.denote]; rw [hq]; rfl

end Proven.WA

/- Route (a): the whole stack program `genR p` on the record machine (`Nano/StackRec.lean`), both outcomes.
* `genR_ok`: with `8 * depth p` bytes of (8-aligned) stack the run halts at `ret` with the result's 8 bytes at `a3`,
  `a0` and `ra` unchanged;
* `genR_oom`: with less, it halts at the `ret` of the failing push's bound check with `a0 = -1` (the oom flag).
The failure path: `push_fail`, `genE_fail`/`genA_fail` (the first push past the work block), `pro_fail`. -/
import Legacy.Nano.StackRec

namespace Nano.R
open Proven

/-- halted at a `ret` with the out-of-memory flag in `a0` and the return address `ra` -/
def Oom (P : List UInt8) (ra : BitVec 64) (s : St) : Prop :=
  step P s = .halt s ∧ s.get 10 = -1 ∧ s.get 1 = ra

/-- `push` with no room left: the bound check fails, `a0 := -1`, `ret` -/
theorem push_fail {P : List UInt8} {s : St} {rest : List UInt8} (h : CodeAt P s.pc (Nano.push ++ rest)) {t W : Nat}
    (h31 : s.get 31 = BitVec.ofNat 64 t) (h12 : s.get 12 = BitVec.ofNat 64 W) (hlt : t < W + 8) (h8 : 8 ≤ t)
    (ht : t < 2 ^ 64) (hW : W < 2 ^ 64) :
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s' := by
  simp only [Nano.push, Nano.r, Nano.sd, List.cons_append, List.nil_append] at h
  have h1 := codeAt_drop h; have h2 := codeAt_drop h1; have h3 := codeAt_drop h2
  have x1 := one h (s' := (({ s with pc := s.pc + 1 } : St).set 31 (BitVec.ofNat 64 (t - 8))))
    (by show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [h31, ofNat_sub8 (by omega) ht])
  generalize hs1 : (({ s with pc := s.pc + 1 } : St).set 31 (BitVec.ofNat 64 (t - 8))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g31 : s1.get 31 = BitVec.ofNat 64 (t - 8) := by rw [← hs1]; simp
  have g12 : s1.get 12 = BitVec.ofNat 64 W := by rw [← hs1, get_set_ne _ (by decide)]; exact h12
  have hnle : ¬ s1.get 12 ≤ s1.get 31 := by
    rw [g31, g12, BitVec.le_def]; simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have x2 := one (p1 ▸ h1) (s' := { s1 with pc := s1.pc + 1 })
    (by show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [if_neg hnle])
  have x3 := one (s := { s1 with pc := s1.pc + 1 }) (by show CodeAt P (s1.pc + 1) _; rw [p1]; exact h2)
    (s' := (({ s1 with pc := s1.pc + 1 + 1 } : St).set 10 (-1))) (by
      have e : ({ s1 with pc := s1.pc + 1 } : St).get 0 + sext8 255 = -1 := by
        rw [sext8_255]; show (0 : BitVec 64) + -1 = -1; simp
      show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [e])
  refine ⟨_, x1.trans (x2.trans x3), ?_, by simp, ?_⟩
  · rw [step_at (by show CodeAt P (s1.pc + 1 + 1) _; rw [p1]; exact h3)]; rfl
  · rw [get_set_ne _ (by decide)]; show s1.get 1 = _; rw [← hs1, get_set_ne _ (by decide)]; rfl

variable {P : List UInt8} {T W : Nat}

theorem oom_kept {ra ra' : BitVec 64} {s : St} (h : Oom P ra s) (e : ra = ra') : Oom P ra' s := e ▸ h

/-- two blocks: the first succeeds and the second fails, or the first fails -/
theorem seq_fail {X Y : List UInt8} {vals vals' : List (BitVec 64)} {d1 d2 : Nat} (hd : T < W + 8 * max d1 d2)
    (oka : W + 8 * d1 ≤ T → ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (X ++ rest) → Stk s T vals →
      s.get 12 = BitVec.ofNat 64 W → ∃ s', Star P s s' ∧ Stk s' T vals' ∧ Kept s s' ∧ CodeAt P s'.pc rest)
    (faila : T < W + 8 * d1 → ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (X ++ rest) → Stk s T vals →
      s.get 12 = BitVec.ofNat 64 W → ∃ s', Star P s s' ∧ Oom P (s.get 1) s')
    (failb : T < W + 8 * d2 → ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (Y ++ rest) → Stk s T vals' →
      s.get 12 = BitVec.ofNat 64 W → ∃ s', Star P s s' ∧ Oom P (s.get 1) s')
    {s : St} {rest : List UInt8} (h : CodeAt P s.pc (X ++ Y ++ rest)) (hs : Stk s T vals)
    (h12 : s.get 12 = BitVec.ofNat 64 W) : ∃ s', Star P s s' ∧ Oom P (s.get 1) s' := by
  rw [List.append_assoc] at h
  by_cases h1 : W + 8 * d1 ≤ T
  · obtain ⟨s1, x1, st1, k1, c1⟩ := oka h1 s _ h hs h12
    obtain ⟨s2, x2, o2⟩ := failb (by omega) s1 rest c1 st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12)
    exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide) (by decide) (by decide))⟩
  · exact faila (by omega) s _ h hs h12

theorem w_of {s : St} (h12 : s.get 12 = BitVec.ofNat 64 W) (hW : W < 2 ^ 64) : (s.get 12).toNat = W := by
  rw [h12]; simp; omega

theorem genA_cnt : ∀ (as : Ex) (env : List UInt64), Nano.cnt as = (denA as env).length
  | .acons _ r, env => by simp [Nano.cnt, denA, genA_cnt r env]
  | .num _, _ => rfl | .var _, _ => rfl | .add _ _, _ => rfl | .sub _ _, _ => rfl | .mul _ _, _ => rfl
  | .let_ _ _, _ => rfl | .call _ _, _ => rfl | .anil, _ => rfl

mutual
/-- **an expression's records run out of stack**: the first push past the work block sets the flag and returns -/
theorem genE_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW64 : W < 2 ^ 64) : ∀ (e : Ex) (sc : List Nat) (env : List UInt64)
    (vals : List (BitVec 64)) (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.genE sc vals.length e ++ rest) →
    ScE e env.length = true → ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    T < W + 8 * Nano.depE vals.length e → Nano.depE vals.length e ≤ 256 →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | .num n, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.genE, List.append_assoc] at h
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp only [Nano.depE] at hW
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
    obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * vals.length) (by rw [k1 31 (by decide)]; exact hs.top)
      (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) (by omega)
    exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
  | .var i, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.genE, List.append_assoc] at h
    simp only [ScE, decide_eq_true_eq] at hsc
    simp only [Nano.depE] at hW hd
    have := hs.lo; rw [w_of h12 (by omega)] at this
    obtain ⟨hj, hv⟩ := hok i hsc
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := ldslot_ok h hs hj (by omega) (by omega) hT2
    obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * vals.length) (by rw [k1 31 (by decide)]; exact hs.top)
      (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) (by omega)
    exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
  | .add a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.depE] at hW hd
    simp only [Nano.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.genE sc vals.length a) (Y := Nano.genE sc (vals.length + 1) b ++ Nano.binop 24) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(den a env).toBitVec]) s (Nano.binop 24 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .sub a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.depE] at hW hd
    simp only [Nano.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.genE sc vals.length a) (Y := Nano.genE sc (vals.length + 1) b ++ Nano.binop 32) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(den a env).toBitVec]) s (Nano.binop 32 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .mul a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.depE] at hW hd
    simp only [Nano.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.genE sc vals.length a) (Y := Nano.genE sc (vals.length + 1) b ++ Nano.binop 40) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(den a env).toBitVec]) s (Nano.binop 40 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .let_ v b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.depE] at hW hd
    simp only [Nano.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.genE sc vals.length v)
      (Y := Nano.genE (vals.length :: sc) (vals.length + 1) b ++ (Nano.ld 5 31 0 ++ Nano.addSp 1 ++ Nano.sd 5 31 0)) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 v sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 v sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b (vals.length :: sc) (den v env :: env) (vals ++ [(den v env).toBitVec]) s
          ((Nano.ld 5 31 0 ++ Nano.addSp 1 ++ Nano.sd 5 31 0) ++ rest)
          (by simpa using h) (by simpa using hsc.2) (hok.push _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .call b as, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true, decide_eq_true_eq] at hsc; simp only [Nano.depE] at hW hd
    obtain ⟨⟨ha, hb⟩, hc⟩ := hsc
    simp only [Nano.genE, List.append_assoc] at h
    have hcnt : Nano.cnt as = (denA as env).length := genA_cnt as env
    have hl : ((denA as env).map UInt64.toBitVec).length = Nano.cnt as := by simp [hcnt]
    exact seq_fail (X := Nano.genA sc vals.length as) (vals' := vals ++ (denA as env).map UInt64.toBitVec)
      (Y := Nano.genE (Nano.mkSc (Nano.cnt as) vals.length) (vals.length + Nano.cnt as) b ++
        (Nano.ld 5 31 0 ++ Nano.addSp (Nano.cnt as) ++ Nano.sd 5 31 0)) hW
      (fun h1 s rest h hs h12 => by
        obtain ⟨s', x, st, k, c, -⟩ := genA_ok hT2 as sc env vals s rest h ha hok hs h12 h1 (by omega)
        exact ⟨s', x, st, k, c⟩)
      (fun h1 s rest h hs h12 => genA_fail hT2 hW8 hW64 as sc env vals s rest h ha hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b (Nano.mkSc (Nano.cnt as) vals.length) (denA as env).reverse
          (vals ++ (denA as env).map UInt64.toBitVec) s
          ((Nano.ld 5 31 0 ++ Nano.addSp (Nano.cnt as) ++ Nano.sd 5 31 0) ++ rest)
          (by simpa [hl] using h) (by simpa [hcnt] using hb)
          (by rw [← hl]; exact ScOk.args _ _ _ (by simp) (fun j h => by simp)) hs h12 (by simp [hl]; omega)
          (by simp [hl]; omega)
        exact this) (by simpa using h) hs h12
  | .anil, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
  | .acons _ _, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
/-- an argument list runs out of stack -/
theorem genA_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW64 : W < 2 ^ 64) : ∀ (as : Ex) (sc : List Nat) (env : List UInt64)
    (vals : List (BitVec 64)) (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.genA sc vals.length as ++ rest) →
    ScA as env.length = true → ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    T < W + 8 * Nano.depA vals.length as → Nano.depA vals.length as ≤ 256 →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | .acons e r, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScA, Bool.and_eq_true] at hsc; simp only [Nano.depA] at hW hd
    simp only [Nano.genA, List.append_assoc] at h
    exact seq_fail (X := Nano.genE sc vals.length e) (Y := Nano.genA sc (vals.length + 1) r) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 e sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genA_fail hT2 hW8 hW64 r sc env (vals ++ [(den e env).toBitVec]) s rest
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .num _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .var _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .add _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .sub _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .mul _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .let_ _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .call _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
  | .anil, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.depA] at hW; omega
end

/-- `pro k` runs out of stack -/
theorem pro_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW64 : W < 2 ^ 64) : ∀ (k : Nat) (vals : List (BitVec 64)) (s : St)
    (rest : List UInt8) (A : Nat), CodeAt P s.pc (Nano.pro k ++ rest) → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    s.get 28 = BitVec.ofNat 64 A → T < W + 8 * (vals.length + k) → (A + 8 * k ≤ W ∨ T ≤ A) →
    A + 8 * k + 8 < 2 ^ 64 → (s.g.I ≤ A ∧ A + 8 * k ≤ s.g.I + s.g.IL) →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | 0, vals, s, rest, A, h, hs, h12, _, hW, _, _, _ => by
    have := hs.lo; rw [w_of h12 hW64] at this; omega
  | k + 1, vals, s, rest, A, h, hs, h12, h28, hW, hd, hA, hI => by
    simp only [Nano.pro, List.append_assoc] at h
    have hlo := hs.lo; rw [w_of h12 hW64] at hlo
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := rd8_ok h h28 (by omega) (by omega)
    have st1 := stk_kept hs m1 (k1 31 (by decide) (by decide)) (k1 12 (by decide) (by decide)) (k1 2 (by decide) (by decide))
    have h12' : s1.get 12 = BitVec.ofNat 64 W := by rw [k1 12 (by decide) (by decide)]; exact h12
    by_cases hfit : W + 8 * (vals.length + 1) ≤ T
    · obtain ⟨s2, x2, st2, k2, c2, -⟩ := push_stkm c1 st1 h12' hfit hT2
      have g28 : s2.get 28 = BitVec.ofNat 64 A := by
        rw [k2 28 (by decide) (by decide) (by decide), k1 28 (by decide) (by decide)]; exact h28
      obtain ⟨x3, c3⟩ := inc3_ok c2 g28 (by omega)
      generalize hs3 : ((({ s2 with pc := s2.pc + 1 } : St)).set 28 (BitVec.ofNat 64 (A + 8))) = s3 at x3
      have st3 : Stk s3 T (vals ++ [s1.get 5]) := stk_kept st2 (by rw [← hs3]; rfl)
        (by rw [← hs3, get_set_ne _ (by decide)]; rfl) (by rw [← hs3, get_set_ne _ (by decide)]; rfl)
        (by rw [← hs3, get_set_ne _ (by decide)]; rfl)
      have gg : s3.g = s.g := by rw [← hs3]; show s2.g = _; rw [x2.g, x1.g]
      obtain ⟨s4, x4, o4⟩ := pro_fail hT2 hW8 hW64 k (vals ++ [s1.get 5]) s3 rest (A + 8) (by rw [← hs3]; exact c3) st3
        (by rw [← hs3, get_set_ne _ (by decide)]; show s2.get 12 = _; rw [k2 12 (by decide) (by decide) (by decide)]; exact h12')
        (by rw [← hs3]; simp) (by simp; omega) (by omega) (by omega) (by rw [gg]; omega)
      refine ⟨s4, x1.trans (x2.trans (x3.trans x4)), oom_kept o4 ?_⟩
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 1 = _
      rw [k2 1 (by decide) (by decide) (by decide), k1 1 (by decide) (by decide)]
    · obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * vals.length) (by rw [k1 31 (by decide) (by decide)]; exact hs.top)
        h12' (by omega) (by omega) (by omega) hW64
      exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide) (by decide))⟩

end Nano.R

/-! ## the whole program -/
namespace Nano.R
open Proven

/-- the start of a run of `genR p` (what `StartCorrect` gives, on the record machine) -/
structure Init (p : Prog) (s : St) (I O W SP : Nat) (args : List UInt64) : Prop where
  pc : s.pc = 0
  r2 : s.get 2 = BitVec.ofNat 64 SP
  r10 : s.get 10 = BitVec.ofNat 64 I
  r12 : s.get 12 = BitVec.ofNat 64 W
  r13 : s.get 13 = BitVec.ofNat 64 O
  gI : s.g.I = I
  gIL : s.g.IL = 8 * p.1
  gO : s.g.O = O
  len : args.length = p.1
  inp : ∀ j (hj : j < args.length), unle (rdL s.m (I + 8 * j) 8) = args[j].toNat
  wal : W % 8 = 0
  w8 : 8 ≤ W
  wsp : W ≤ SP
  sp64 : SP < 2 ^ 63
  dis : I + 8 * p.1 ≤ W ∨ SP ≤ I
  i64 : I + 8 * p.1 + 8 < 2 ^ 63
  o64 : O + 8 < 2 ^ 63

theorem align_eq (SP : Nat) (h : SP < 2 ^ 64) :
    (BitVec.ofNat 64 SP >>> 3) <<< 3 = BitVec.ofNat 64 (SP / 8 * 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- the prologue: `t6 := sp & ~7`, `t3 := a0`; an empty stack below `T = sp & ~7` -/
theorem prologue {p : Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args) :
    ∃ s3, Star (Nano.genR p) s s3 ∧ Stk s3 (SP / 8 * 8) [] ∧ s3.get 28 = BitVec.ofNat 64 I ∧ s3.m = s.m ∧
      s3.g = s.g ∧ (∀ j, j ≠ 31 → j ≠ 28 → s3.get j = s.get j) ∧
      CodeAt (Nano.genR p) s3.pc (Nano.pro p.1 ++ Nano.genE (Nano.mkSc p.1 0) p.1 p.2 ++ Nano.ld 5 31 0 ++
        Nano.wr8 ++ Nano.r 48 0 1 0) := by
  have h0 : CodeAt (Nano.genR p) s.pc (5 :: 31 :: 2 :: 3 :: 1 :: 31 :: 31 :: 3 :: 0 :: 28 :: 10 :: 0 ::
      (Nano.pro p.1 ++ Nano.genE (Nano.mkSc p.1 0) p.1 p.2 ++ Nano.ld 5 31 0 ++ Nano.wr8 ++ Nano.r 48 0 1 0)) :=
    ⟨[], [], by simp [Nano.genR, Nano.r], by rw [hi.pc]; rfl⟩
  have c1 := codeAt_drop h0; have c2 := codeAt_drop c1; have c3 := codeAt_drop c2
  have x1 := one h0 (s' := (({ s with pc := s.pc + 1 } : St).set 31 (s.get 2 >>> 3))) rfl
  generalize hs1 : (({ s with pc := s.pc + 1 } : St).set 31 (s.get 2 >>> 3)) = s1 at x1
  have x2 := one (s := s1) (by rw [← hs1]; exact c1) (s' := (({ s1 with pc := s1.pc + 1 } : St).set 31 (s1.get 31 <<< 3))) rfl
  generalize hs2 : (({ s1 with pc := s1.pc + 1 } : St).set 31 (s1.get 31 <<< 3)) = s2 at x2
  have x3 := one (s := s2) (by rw [← hs2, ← hs1]; exact c2)
    (s' := (({ s2 with pc := s2.pc + 1 } : St).set 28 (s2.get 10 + sext8 0))) rfl
  generalize hs3 : (({ s2 with pc := s2.pc + 1 } : St).set 28 (s2.get 10 + sext8 0)) = s3 at x3
  have k3 : ∀ j, j ≠ 31 → j ≠ 28 → s3.get j = s.get j := fun j a b => by
    rw [← hs3, get_set_ne _ b]; show s2.get j = _; rw [← hs2, get_set_ne _ a]; show s1.get j = _
    rw [← hs1, get_set_ne _ a]; rfl
  have t31 : s3.get 31 = BitVec.ofNat 64 (SP / 8 * 8) := by
    rw [← hs3, get_set_ne _ (by decide)]; show s2.get 31 = _; rw [← hs2, get_set_same _ (by decide)]
    rw [← hs1, get_set_same _ (by decide), hi.r2, align_eq _ (by have := hi.sp64; omega)]
  have hsp := hi.sp64; have hw := hi.wsp; have hwal := hi.wal
  refine ⟨s3, x1.trans (x2.trans x3), ⟨by simpa using t31, fun k hk => by simp at hk, ?_, by omega, ?_⟩, ?_,
    by rw [← hs3, ← hs2, ← hs1]; rfl, by rw [← hs3, ← hs2, ← hs1]; rfl, k3, ?_⟩
  · rw [k3 12 (by decide) (by decide), hi.r12]; simp; omega
  · rw [k3 2 (by decide) (by decide), hi.r2]; simp; omega
  · rw [← hs3, get_set_same _ (by decide), show sext8 0 = 0#64 by decide, BitVec.add_zero]
    show s2.get 10 = _; rw [← hs2, get_set_ne _ (by decide)]; show s1.get 10 = _
    rw [← hs1, get_set_ne _ (by decide)]; exact hi.r10
  · rw [← hs3, ← hs2, ← hs1]; exact c3

theorem args_vals {p : Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args) :
    ([] : List (BitVec 64)) ++ (List.range p.1).map (fun i => BitVec.ofNat 64 (unle (rdL s.m (I + 8 * i) 8))) =
      args.map UInt64.toBitVec := by
  apply List.ext_getElem (by simp [hi.len])
  intro j h1 h2
  simp only [List.nil_append, List.getElem_map, List.getElem_range]
  rw [hi.inp j (by simpa using h2)]; simp

theorem ret_halt {P : List UInt8} {s : St} (h : CodeAt P s.pc (Nano.r 48 0 1 0)) : step P s = .halt s := by
  rw [step_at (rest := []) (by simpa [Nano.r] using h)]; rfl

/-- **the whole program, enough stack**: halts at `ret` with the result's bytes at `a3`; `a0`, `ra` unchanged -/
theorem genR_ok {p : Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args)
    (hsc : ScE p.2 p.1 = true) (hd : Nano.depth p ≤ 256) (hfit : W + 8 * Nano.depth p ≤ SP / 8 * 8) :
    ∃ s', Star (Nano.genR p) s s' ∧ step (Nano.genR p) s' = .halt s' ∧
      (∀ x, O ≤ x → x < O + 8 → s'.m x = byteOf (den p.2 args.reverse).toBitVec (x - O)) ∧
      s'.get 10 = s.get 10 ∧ s'.get 1 = s.get 1 := by
  obtain ⟨s3, x3, st3, g28, m3, gg3, k3, c3⟩ := prologue hi
  simp only [List.append_assoc] at c3
  have hsp := hi.sp64; have hw := hi.wsp; have hwal := hi.wal; have hdis := hi.dis; have hi64 := hi.i64
  have hdep : Nano.depth p = max p.1 (Nano.depE p.1 p.2) := rfl
  have hge := depE_ge p.2 p.1 p.1 hsc
  have h12 : s3.get 12 = BitVec.ofNat 64 W := by rw [k3 12 (by decide) (by decide)]; exact hi.r12
  obtain ⟨s4, x4, st4, k4, c4⟩ := pro_ok (W := W) (T := SP / 8 * 8) (by omega) p.1 [] s3 _ I c3 st3 h12 g28
    (by simp; omega) (by omega) (by omega) (by rw [gg3, hi.gI, hi.gIL]; omega)
  rw [m3, args_vals hi] at st4
  have hl : (args.map UInt64.toBitVec).length = p.1 := by simp [hi.len]
  obtain ⟨s5, x5, st5, k5, c5⟩ := genE_ok (W := W) (by omega) p.2 (Nano.mkSc p.1 0) args.reverse
    (args.map UInt64.toBitVec) s4 _ (by rw [hl]; exact c4) (by simp [hi.len, hsc])
    (by have := ScOk.args [] (args.map UInt64.toBitVec) args (by simp) (fun j h => by simp)
        simpa [hl] using this) st4
    (by rw [k4 12 (by decide) (by decide) (by decide) (by decide)]; exact h12) (by rw [hl]; omega) (by rw [hl]; omega)
  have hz : (args.map UInt64.toBitVec ++ [(den p.2 args.reverse).toBitVec]).length - 1 - args.length = 0 := by simp
  have hlo := st5.lo; simp [hl] at hlo
  obtain ⟨s6, x6, g6, m6, k6, c6⟩ := ldslot_ok (j := args.length) (by rw [hz]; exact c5) st5 (by simp)
    (by simp [hl]; omega) (by simp [hl]; omega) (by omega)
  have e6 : s6.get 13 = BitVec.ofNat 64 O := by
    rw [k6 13 (by decide), k5 13 (by decide) (by decide) (by decide), k4 13 (by decide) (by decide) (by decide) (by decide),
      k3 13 (by decide) (by decide)]; exact hi.r13
  have gg6 : s6.g = s.g := by rw [x6.g, x5.g, x4.g, gg3]
  have hw8 : Nano.wr8 = (List.range' 0 8).foldr wg [] := by simp only [Nano.wr8, List.range_eq_range']; rfl
  rw [hw8] at c6
  have ho := hi.o64
  obtain ⟨s7, x7, m7, k7, c7⟩ := wr_loop (O := O) (by omega) _ 8 0 (by decide) s6 _ c6 e6 rfl (by rw [gg6, hi.gO])
  refine ⟨s7, x3.trans (x4.trans (x5.trans (x6.trans x7))), ret_halt c7, fun x h1 h2 => ?_, ?_, ?_⟩
  · rw [m7 x, if_pos (by omega), g6]; simp
  · rw [k7 10 (by decide), k6 10 (by decide), k5 10 (by decide) (by decide) (by decide),
      k4 10 (by decide) (by decide) (by decide) (by decide), k3 10 (by decide) (by decide)]
  · rw [k7 1 (by decide), k6 1 (by decide), k5 1 (by decide) (by decide) (by decide),
      k4 1 (by decide) (by decide) (by decide) (by decide), k3 1 (by decide) (by decide)]

/-- **the whole program, too little stack**: halts at a `ret` with `a0 = -1` -/
theorem genR_oom {p : Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args)
    (hsc : ScE p.2 p.1 = true) (hd : Nano.depth p ≤ 256) (hover : SP / 8 * 8 < W + 8 * Nano.depth p) :
    ∃ s', Star (Nano.genR p) s s' ∧ Oom (Nano.genR p) (s.get 1) s' := by
  obtain ⟨s3, x3, st3, g28, m3, gg3, k3, c3⟩ := prologue hi
  simp only [List.append_assoc] at c3
  have hsp := hi.sp64; have hw := hi.wsp; have hwal := hi.wal; have hdis := hi.dis; have hi64 := hi.i64
  have hw8 := hi.w8
  have hdep : Nano.depth p = max p.1 (Nano.depE p.1 p.2) := rfl
  have h12 : s3.get 12 = BitVec.ofNat 64 W := by rw [k3 12 (by decide) (by decide)]; exact hi.r12
  have e1 : s3.get 1 = s.get 1 := k3 1 (by decide) (by decide)
  by_cases hp : W + 8 * p.1 ≤ SP / 8 * 8
  · obtain ⟨s4, x4, st4, k4, c4⟩ := pro_ok (W := W) (T := SP / 8 * 8) (by omega) p.1 [] s3 _ I c3 st3 h12 g28
      (by simp; omega) (by omega) (by omega) (by rw [gg3, hi.gI, hi.gIL]; omega)
    rw [m3, args_vals hi] at st4
    have hl : (args.map UInt64.toBitVec).length = p.1 := by simp [hi.len]
    obtain ⟨s5, x5, o5⟩ := genE_fail (W := W) (by omega) (by omega) (by omega) p.2 (Nano.mkSc p.1 0) args.reverse
      (args.map UInt64.toBitVec) s4 _ (by rw [hl]; exact c4) (by simp [hi.len, hsc])
      (by have := ScOk.args [] (args.map UInt64.toBitVec) args (by simp) (fun j h => by simp)
          simpa [hl] using this) st4
      (by rw [k4 12 (by decide) (by decide) (by decide) (by decide)]; exact h12) (by rw [hl]; omega) (by rw [hl]; omega)
    exact ⟨s5, x3.trans (x4.trans x5), oom_kept o5 (by rw [k4 1 (by decide) (by decide) (by decide) (by decide), e1])⟩
  · obtain ⟨s4, x4, o4⟩ := pro_fail (W := W) (T := SP / 8 * 8) (by omega) (by omega) (by omega) p.1 [] s3 _ I c3 st3 h12
      g28 (by simp; omega) (by omega) (by omega) (by rw [gg3, hi.gI, hi.gIL]; omega)
    exact ⟨s4, x3.trans x4, oom_kept o4 e1⟩

end Nano.R

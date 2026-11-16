/- Route (a): the whole stack program `genR p` on the record machine (`Nano/StackRec.lean`), both outcomes.
* `genR_ok`: with `8 * depth p` bytes of (8-aligned) stack the run halts at `ret` with the result's 8 bytes at `a3`,
  `a0` and `ra` unchanged;
* `genR_oom`: with less, it halts at the `ret` of the failing push's bound check with `a0 = -1` (the oom flag).
The failure path: `push_fail`, `genE_fail`/`genA_fail` (the first push past the work block), `pro_fail`. -/
import Nano.StackRec

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

end Nano.R

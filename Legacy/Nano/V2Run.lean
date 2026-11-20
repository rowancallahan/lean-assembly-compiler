/- nano v2, increment 1: the out-of-memory path of `Nano.V2.genE` (`genE_fail`, copy of v1's with the `if` node via
`ite_fail`), and the whole program `Nano.V2.genR` on the record machine (`genR_ok`, `genR_oom`). -/
import Legacy.Nano.V2Rec

namespace Nano.V2R
open Proven Nano.R Nano.V2

variable {P : List UInt8} {T W : Nat}

/-- an expression piece without room: the oom flag -/
def FailP (P : List UInt8) (T W : Nat) (code : List UInt8) (vals : List (BitVec 64)) : Prop :=
  ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (code ++ rest) → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'

/-- **an `if` node without room**: one of its six parts runs out -/
theorem ite_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW : W < 2 ^ 64) {X A B Y : List UInt8} {ops : List SOp}
    {vals : List (BitVec 64)} {vx va vb vy c : BitVec 64} {dX dA dB dY : Nat}
    (okX : W + 8 * dX ≤ T → Piece P T W X vals vx) (failX : T < W + 8 * dX → FailP P T W X vals)
    (okA : W + 8 * dA ≤ T → Piece P T W A (vals ++ [vx]) va) (failA : T < W + 8 * dA → FailP P T W A (vals ++ [vx]))
    (okB : W + 8 * dB ≤ T → Piece P T W B (vals ++ [vx, va]) vb)
    (failB : T < W + 8 * dB → FailP P T W B (vals ++ [vx, va]))
    (okY : W + 8 * dY ≤ T → Piece P T W Y (vals ++ [vx, c]) vy)
    (failY : T < W + 8 * dY → FailP P T W Y (vals ++ [vx, c]))
    (hops : runOps ops (vb :: va :: vx :: vals.reverse) = c :: vx :: vals.reverse)
    (hwf : wfOps (vals.length + 3) ops = true)
    (hd : T < W + 8 * max dX (max dA (max dB (max (peakOps (vals.length + 3) ops)
      (max dY (peakOps (vals.length + 3) selOps))))))
    {s : St} {rest : List UInt8} (h : CodeAt P s.pc (X ++ A ++ B ++ opsCode ops ++ Y ++ opsCode selOps ++ rest))
    (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W) :
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s' := by
  simp only [List.append_assoc] at h
  have e3 : ∀ x y z : BitVec 64, vals ++ [x, y] ++ [z] = (z :: y :: x :: vals.reverse).reverse := by intros; simp
  refine seq_fail (X := X) (Y := A ++ (B ++ (opsCode ops ++ (Y ++ opsCode selOps)))) hd okX failX ?_
    (by simpa using h) hs h12
  intro h1 s rest h hs h12
  refine seq_fail (X := A) (Y := B ++ (opsCode ops ++ (Y ++ opsCode selOps))) h1 okA failA ?_
    (by simpa using h) hs h12
  intro h1 s rest h hs h12
  refine seq_fail (X := B) (Y := opsCode ops ++ (Y ++ opsCode selOps)) (vals' := vals ++ [vx, va] ++ [vb]) h1
    (fun h2 s rest h hs h12 => by have := okB h2 s rest h (by simpa using hs) h12; simpa using this)
    (fun h2 s rest h hs h12 => failB h2 s rest h (by simpa using hs) h12) ?_ (by simpa using h) (by simpa using hs) h12
  intro h1 s rest h hs h12
  rw [e3] at hs
  refine seq_fail (X := opsCode ops) (Y := Y ++ opsCode selOps) (vals' := (c :: vx :: vals.reverse).reverse) h1
    (fun h2 s rest h hs h12 => by
      have := ops_ok hT2 hW ops _ s rest h hs h12 (by simpa using hwf) (by simpa using h2); rwa [hops] at this)
    (fun h2 s rest h hs h12 => ops_fail hT2 hW8 hW ops _ s rest h hs h12 (by simpa using hwf) (by simpa using h2))
    ?_ (by simpa using h) hs h12
  intro h1 s rest h hs h12
  refine seq_fail (X := Y) (Y := opsCode selOps) (vals' := (vy :: c :: vx :: vals.reverse).reverse) h1
    (fun h2 s rest h hs h12 => by have := okY h2 s rest h (by simpa using hs) h12; simpa using this)
    (fun h2 s rest h hs h12 => failY h2 s rest h (by simpa using hs) h12)
    (fun h2 s rest h hs h12 => ops_fail hT2 hW8 hW selOps _ s rest h hs h12
      (by simp only [List.length_cons, List.length_reverse]; exact (wf_sel _ (by omega)).1)
      (by simpa using h2)) (by simpa using h) hs h12

theorem w_of' {s : St} (h12 : s.get 12 = BitVec.ofNat 64 W) (hW : W < 2 ^ 64) : (s.get 12).toNat = W := by
  rw [h12]; simp; omega

set_option maxHeartbeats 2000000 in
mutual
/-- **an expression's records run out of stack**: the first push past the work block sets the flag and returns -/
theorem genE_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW64 : W < 2 ^ 64) : ∀ (e : E) (sc : List Nat) (env : List UInt64)
    (vals : List (BitVec 64)) (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.V2.genE sc vals.length e ++ rest) →
    ScE e env.length = true → ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    T < W + 8 * Nano.V2.depE vals.length e → Nano.V2.depE vals.length e ≤ 256 →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | .num n, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.V2.genE, List.append_assoc] at h
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp only [Nano.V2.depE] at hW
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
    obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * vals.length) (by rw [k1 31 (by decide)]; exact hs.top)
      (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) (by omega)
    exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
  | .var i, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.V2.genE, List.append_assoc] at h
    simp only [ScE, decide_eq_true_eq] at hsc
    simp only [Nano.V2.depE] at hW hd
    have := hs.lo; rw [w_of h12 (by omega)] at this
    obtain ⟨hj, hv⟩ := hok i hsc
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := ldslot_ok h hs hj (by omega) (by omega) hT2
    obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * vals.length) (by rw [k1 31 (by decide)]; exact hs.top)
      (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) (by omega)
    exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
  | .add a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length a) (Y := Nano.V2.genE sc (vals.length + 1) b ++ Nano.binop 24) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s (Nano.binop 24 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .sub a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length a) (Y := Nano.V2.genE sc (vals.length + 1) b ++ Nano.binop 32) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s (Nano.binop 32 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .mul a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length a) (Y := Nano.V2.genE sc (vals.length + 1) b ++ Nano.binop 40) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s (Nano.binop 40 ++ rest)
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .let_ v b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length v)
      (Y := Nano.V2.genE (vals.length :: sc) (vals.length + 1) b ++ (Nano.ld 5 31 0 ++ Nano.addSp 1 ++ Nano.sd 5 31 0)) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 v sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 v sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b (vals.length :: sc) (Nano.V2.den v env :: env) (vals ++ [(Nano.V2.den v env).toBitVec]) s
          ((Nano.ld 5 31 0 ++ Nano.addSp 1 ++ Nano.sd 5 31 0) ++ rest)
          (by simpa using h) (by simpa using hsc.2) (hok.push _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .call b as, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true, decide_eq_true_eq] at hsc; simp only [Nano.V2.depE] at hW hd
    obtain ⟨⟨ha, hb⟩, hc⟩ := hsc
    simp only [Nano.V2.genE, List.append_assoc] at h
    have hcnt : Nano.V2.cnt as = (Nano.V2.denA as env).length := genA_cnt as env
    have hl : ((Nano.V2.denA as env).map UInt64.toBitVec).length = Nano.V2.cnt as := by simp [hcnt]
    exact seq_fail (X := Nano.V2.genA sc vals.length as) (vals' := vals ++ (Nano.V2.denA as env).map UInt64.toBitVec)
      (Y := Nano.V2.genE (Nano.mkSc (Nano.V2.cnt as) vals.length) (vals.length + Nano.V2.cnt as) b ++
        (Nano.ld 5 31 0 ++ Nano.addSp (Nano.V2.cnt as) ++ Nano.sd 5 31 0)) hW
      (fun h1 s rest h hs h12 => by
        obtain ⟨s', x, st, k, c, -⟩ := genA_ok hT2 as sc env vals s rest h ha hok hs h12 h1 (by omega)
        exact ⟨s', x, st, k, c⟩)
      (fun h1 s rest h hs h12 => genA_fail hT2 hW8 hW64 as sc env vals s rest h ha hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genE_fail hT2 hW8 hW64 b (Nano.mkSc (Nano.V2.cnt as) vals.length) (Nano.V2.denA as env).reverse
          (vals ++ (Nano.V2.denA as env).map UInt64.toBitVec) s
          ((Nano.ld 5 31 0 ++ Nano.addSp (Nano.V2.cnt as) ++ Nano.sd 5 31 0) ++ rest)
          (by simpa [hl] using h) (by simpa [hcnt] using hb)
          (by rw [← hl]; exact ScOk.args _ _ _ (by simp) (fun j h => by simp)) hs h12 (by simp [hl]; omega)
          (by simp [hl]; omega)
        exact this) (by simpa using h) hs h12
  | .ite k a b t e, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc
    obtain ⟨⟨⟨ha, hb⟩, ht⟩, he⟩ := hsc
    have hw := wf_cmp k (vals.length + 3) (by omega)
    have hcode := h; simp only [Nano.V2.genE] at hcode
    simp only [Nano.V2.depE] at hW hd
    cases k with
    | eq =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      exact ite_fail (ops := cmpOps .eq) (vy := (Nano.V2.den t env).toBitVec) hT2 hW8 hW64
        (fun h1 s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
          hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha
          (hok.mono _) hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h)
          hb (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec = (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec = (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h)
          ht (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (eq_run _ _ _) hw.1 hW hcode hs h12
    | ltu =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      exact ite_fail (ops := cmpOps .ltu) (vy := (Nano.V2.den t env).toBitVec) hT2 hW8 hW64
        (fun h1 s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
          hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha
          (hok.mono _) hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h)
          hb (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.toNat < (Nano.V2.den b env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.toNat < (Nano.V2.den b env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h)
          ht (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (ltu_run _ _ _) hw.1 hW hcode hs h12
    | lts =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      exact ite_fail (ops := cmpOps .lts) (vy := (Nano.V2.den t env).toBitVec) hT2 hW8 hW64
        (fun h1 s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env vals s rest h he hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
          hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha
          (hok.mono _) hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h)
          hb (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.slt (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.slt (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h)
          ht (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (lts_run _ _ _) hw.1 hW hcode hs h12
    | leu =>
      simp only [Cmp.swap, if_true] at hcode hW hd
      exact ite_fail (ops := cmpOps .leu) (vy := (Nano.V2.den e env).toBitVec) hT2 hW8 hW64
        (fun h1 s rest h hs h12 => genE_ok hT2 t sc env vals s rest h ht hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 t sc env vals s rest h ht hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_ok hT2 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
          hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb
          (hok.mono _) hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h)
          ha (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.toNat < (Nano.V2.den a env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h) he (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.toNat < (Nano.V2.den a env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h)
          he (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (ltu_run _ _ _) hw.1 hW hcode hs h12
    | les =>
      simp only [Cmp.swap, if_true] at hcode hW hd
      exact ite_fail (ops := cmpOps .les) (vy := (Nano.V2.den e env).toBitVec) hT2 hW8 hW64
        (fun h1 s rest h hs h12 => genE_ok hT2 t sc env vals s rest h ht hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 t sc env vals s rest h ht hok hs h12 h1 (by omega))
        (fun h1 s rest h hs h12 => genE_ok hT2 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
          hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb
          (hok.mono _) hs h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h)
          ha (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (fun h1 s rest h hs h12 => by
          have := genE_ok hT2 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.slt (Nano.V2.den a env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) he (hok.mono _)
            (by simpa using hs) h12 (by simpa using h1) (by simp; omega)
          simpa using this)
        (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.slt (Nano.V2.den a env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h)
          he (hok.mono _) (by simpa using hs) h12 (by simpa using h1) (by simp; omega))
        (lts_run _ _ _) hw.1 hW hcode hs h12
  | .bit o a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have hw := wf_bit o (vals.length + 2) (by have := depE_ge a vals.length _ hsc.1; omega)
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length a) (Y := Nano.V2.genE sc (vals.length + 1) b ++ opsCode (bitOps o)) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 a sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        rw [List.append_assoc] at h
        exact seq_fail (X := Nano.V2.genE sc (vals.length + 1) b) (Y := opsCode (bitOps o))
          (vals' := vals ++ [(Nano.V2.den a env).toBitVec] ++ [(Nano.V2.den b env).toBitVec]) h1
          (fun h2 s rest h hs h12 => genE_ok hT2 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest
            (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h2) (by simp; omega))
          (fun h2 s rest h hs h12 => genE_fail hT2 hW8 hW64 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest
            (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h2) (by simp; omega))
          (fun h2 s rest h hs h12 => by
            have e : vals ++ [(Nano.V2.den a env).toBitVec] ++ [(Nano.V2.den b env).toBitVec] =
              ((Nano.V2.den b env).toBitVec :: (Nano.V2.den a env).toBitVec :: vals.reverse).reverse := by simp
            rw [e] at hs
            exact ops_fail hT2 hW8 hW64 _ _ s rest h hs h12 (by simpa using hw.1) (by simpa using h2))
          (by simpa using h) hs h12)
      (by simpa using h) hs h12
  | .sh l k a, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE] at hsc; simp only [Nano.V2.depE] at hW hd
    simp only [Nano.V2.genE, List.append_assoc] at h
    exact genE_fail hT2 hW8 hW64 a sc env vals s _ h hsc hok hs h12 hW hd
  | .anil, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
  | .acons _ _, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
/-- an argument list runs out of stack -/
theorem genA_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW64 : W < 2 ^ 64) : ∀ (as : E) (sc : List Nat) (env : List UInt64)
    (vals : List (BitVec 64)) (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.V2.genA sc vals.length as ++ rest) →
    ScA as env.length = true → ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    T < W + 8 * Nano.V2.depA vals.length as → Nano.V2.depA vals.length as ≤ 256 →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | .acons e r, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScA, Bool.and_eq_true] at hsc; simp only [Nano.V2.depA] at hW hd
    simp only [Nano.V2.genA, List.append_assoc] at h
    exact seq_fail (X := Nano.V2.genE sc vals.length e) (Y := Nano.V2.genA sc (vals.length + 1) r) hW
      (fun h1 s rest h hs h12 => genE_ok hT2 e sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => genE_fail hT2 hW8 hW64 e sc env vals s rest h hsc.1 hok hs h12 h1 (by omega))
      (fun h1 s rest h hs h12 => by
        have := genA_fail hT2 hW8 hW64 r sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest
          (by simpa using h) hsc.2 (hok.mono _) hs h12 (by simpa using h1) (by simp; omega)
        exact this) (by simpa using h) hs h12
  | .num _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .var _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .add _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .sub _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .mul _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .let_ _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .call _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .anil, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .ite _ _ _ _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .bit _ _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
  | .sh _ _ _, _, _, vals, s, _, _, _, _, hs, h12, hW, _ => by
    have := hs.lo; rw [w_of h12 (by omega)] at this; simp [Nano.V2.depA] at hW; omega
end


/-- the start of a run of `genR p` (what `StartCorrect` gives, on the record machine) -/
structure Init (p : Nano.V2.Prog) (s : St) (I O W SP : Nat) (args : List UInt64) : Prop where
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

/-- the prologue: `t6 := sp & ~7`, `t3 := a0`; an empty stack below `T = sp & ~7` -/
theorem prologue {p : Nano.V2.Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args) :
    ∃ s3, Star (Nano.V2.genR p) s s3 ∧ Stk s3 (SP / 8 * 8) [] ∧ s3.get 28 = BitVec.ofNat 64 I ∧ s3.m = s.m ∧
      s3.g = s.g ∧ (∀ j, j ≠ 31 → j ≠ 28 → s3.get j = s.get j) ∧
      CodeAt (Nano.V2.genR p) s3.pc (Nano.pro p.1 ++ Nano.V2.genE (Nano.mkSc p.1 0) p.1 p.2 ++ Nano.ld 5 31 0 ++
        Nano.wr8 ++ Nano.r 48 0 1 0) := by
  have h0 : CodeAt (Nano.V2.genR p) s.pc (5 :: 31 :: 2 :: 3 :: 1 :: 31 :: 31 :: 3 :: 0 :: 28 :: 10 :: 0 ::
      (Nano.pro p.1 ++ Nano.V2.genE (Nano.mkSc p.1 0) p.1 p.2 ++ Nano.ld 5 31 0 ++ Nano.wr8 ++ Nano.r 48 0 1 0)) :=
    ⟨[], [], by simp [Nano.V2.genR, Nano.r], by rw [hi.pc]; rfl⟩
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

theorem args_vals {p : Nano.V2.Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args) :
    ([] : List (BitVec 64)) ++ (List.range p.1).map (fun i => BitVec.ofNat 64 (unle (rdL s.m (I + 8 * i) 8))) =
      args.map UInt64.toBitVec := by
  apply List.ext_getElem (by simp [hi.len])
  intro j h1 h2
  simp only [List.nil_append, List.getElem_map, List.getElem_range]
  rw [hi.inp j (by simpa using h2)]; simp

/-- **the whole program, enough stack**: halts at `ret` with the result's bytes at `a3`; `a0`, `ra` unchanged -/
theorem genR_ok {p : Nano.V2.Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args)
    (hsc : ScE p.2 p.1 = true) (hd : Nano.V2.depth p ≤ 256) (hfit : W + 8 * Nano.V2.depth p ≤ SP / 8 * 8) :
    ∃ s', Star (Nano.V2.genR p) s s' ∧ step (Nano.V2.genR p) s' = .halt s' ∧
      (∀ x, O ≤ x → x < O + 8 → s'.m x = byteOf (Nano.V2.den p.2 args.reverse).toBitVec (x - O)) ∧
      s'.get 10 = s.get 10 ∧ s'.get 1 = s.get 1 := by
  obtain ⟨s3, x3, st3, g28, m3, gg3, k3, c3⟩ := prologue hi
  simp only [List.append_assoc] at c3
  have hsp := hi.sp64; have hw := hi.wsp; have hwal := hi.wal; have hdis := hi.dis; have hi64 := hi.i64
  have hdep : Nano.V2.depth p = max p.1 (Nano.V2.depE p.1 p.2) := rfl
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
  have hz : (args.map UInt64.toBitVec ++ [(Nano.V2.den p.2 args.reverse).toBitVec]).length - 1 - args.length = 0 := by simp
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
theorem genR_oom {p : Nano.V2.Prog} {s : St} {I O W SP : Nat} {args : List UInt64} (hi : Init p s I O W SP args)
    (hsc : ScE p.2 p.1 = true) (hd : Nano.V2.depth p ≤ 256) (hover : SP / 8 * 8 < W + 8 * Nano.V2.depth p) :
    ∃ s', Star (Nano.V2.genR p) s s' ∧ Oom (Nano.V2.genR p) (s.get 1) s' := by
  obtain ⟨s3, x3, st3, g28, m3, gg3, k3, c3⟩ := prologue hi
  simp only [List.append_assoc] at c3
  have hsp := hi.sp64; have hw := hi.wsp; have hwal := hi.wal; have hdis := hi.dis; have hi64 := hi.i64
  have hw8 := hi.w8
  have hdep : Nano.V2.depth p = max p.1 (Nano.V2.depE p.1 p.2) := rfl
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

end Nano.V2R

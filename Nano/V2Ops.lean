/- nano v2, increment 1: the stack operations of `Nano/V2Gen.lean` on the record machine of `Nano/StackRec.lean`
(`op_ok`/`ops_ok`: with room they transform the value stack as `runOps` says; `ops_fail`: without room the first push
past the work block sets the oom flag), and their arithmetic (`ltu_run`, `lts_run`, `eq_run`, `sel_run`). -/
import Nano.StackRun
import Nano.V2Gen

namespace Nano.V2R
open Proven Nano.R Nano.V2

/-! ## arithmetic -/

theorem low_bit (a : BitVec 64) : a - (a >>> 1) * 2#64 = BitVec.ofNat 64 (a.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (2#64).toNat = 2 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h2]
  have := a.isLt
  omega

/-- unsigned `<` with shifts and arithmetic -/
theorem ltu_bits (a b : BitVec 64) :
    ((a >>> 1) - (b >>> 1) - ((b - (b >>> 1) * 2#64) - (a - (a >>> 1) * 2#64) * (b - (b >>> 1) * 2#64))) >>> 63 =
      if a.toNat < b.toNat then 1#64 else 0#64 := by
  rw [low_bit a, low_bit b]
  have ha := a.isLt; have hb := b.isLt
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one b.toNat with h2 | h2 <;>
  · rw [h1, h2]
    apply BitVec.eq_of_toNat_eq
    split <;>
    · simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega

/-- signed `<` = unsigned `<` after adding `2^63` -/
theorem lts_bits (a b : BitVec 64) :
    a.slt b = decide ((a + 0x8000000000000000#64).toNat < (b + 0x8000000000000000#64).toNat) := by
  rw [BitVec.slt_eq_ult, BitVec.ult]
  have ha := a.isLt; have hb := b.isLt
  have hm : ∀ x : BitVec 64, x.msb = decide (2 ^ 63 ≤ x.toNat) := fun x => BitVec.msb_eq_decide x
  rw [hm a, hm b]
  have e : ∀ x : BitVec 64, (x + 0x8000000000000000#64).toNat = (x.toNat + 2 ^ 63) % 2 ^ 64 := fun x => by
    rw [BitVec.toNat_add]; rfl
  rw [e a, e b]
  by_cases p : 2 ^ 63 ≤ a.toNat <;> by_cases q : 2 ^ 63 ≤ b.toNat <;> simp [p, q]
  all_goals first | omega | (apply Bool.eq_iff_iff.mpr; simp only [Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]; omega)

theorem nat_add_or_and : ∀ (a b : Nat), a + b = (a ||| b) + (a &&& b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 := ih (a / 2) (Nat.div_lt_self ha (by decide)) (b / 2)
      have e1 : a ||| b = 2 * ((a ||| b) / 2) + (a ||| b) % 2 := (Nat.div_add_mod _ 2).symm
      have e2 : a &&& b = 2 * ((a &&& b) / 2) + (a &&& b) % 2 := (Nat.div_add_mod _ 2).symm
      rw [Nat.or_div_two] at e1; rw [Nat.and_div_two] at e2
      have ma := Nat.mod_two_eq_zero_or_one a; have mb := Nat.mod_two_eq_zero_or_one b
      have mo : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := Nat.or_mod_two_eq_one
      have mn : (a &&& b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := Nat.and_mod_two_eq_one
      have mo2 := Nat.mod_two_eq_zero_or_one (a ||| b); have mn2 := Nat.mod_two_eq_zero_or_one (a &&& b)
      have da := Nat.div_add_mod a 2; have db := Nat.div_add_mod b 2
      rw [e1, e2]
      rcases ma with ma | ma <;> rcases mb with mb | mb <;> rcases mo2 with mo2 | mo2 <;> rcases mn2 with mn2 | mn2 <;>
        simp_all <;> omega

theorem and_eq_add_sub_or (a b : BitVec 64) : a &&& b = (a + b) - (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_or]
  have h := nat_add_or_and a.toNat b.toNat
  have ha := a.isLt; have hb := b.isLt
  have h1 : a.toNat ||| b.toNat < 2 ^ 64 := Nat.or_lt_two_pow ha hb
  have h2 : a.toNat &&& b.toNat ≤ a.toNat := Nat.and_le_left
  omega

theorem nat_or_xor_and : ∀ (a b : Nat), (a ||| b) = (a ^^^ b) + (a &&& b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 := ih (a / 2) (Nat.div_lt_self ha (by decide)) (b / 2)
      have e1 : a ||| b = 2 * ((a ||| b) / 2) + (a ||| b) % 2 := (Nat.div_add_mod _ 2).symm
      have e2 : a &&& b = 2 * ((a &&& b) / 2) + (a &&& b) % 2 := (Nat.div_add_mod _ 2).symm
      have e3 : a ^^^ b = 2 * ((a ^^^ b) / 2) + (a ^^^ b) % 2 := (Nat.div_add_mod _ 2).symm
      rw [Nat.or_div_two] at e1; rw [Nat.and_div_two] at e2; rw [Nat.xor_div_two] at e3
      have ma := Nat.mod_two_eq_zero_or_one a; have mb := Nat.mod_two_eq_zero_or_one b
      have mo : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := Nat.or_mod_two_eq_one
      have mn : (a &&& b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := Nat.and_mod_two_eq_one
      have mx : (a ^^^ b) % 2 = 1 ↔ ¬ ((a % 2 = 1) ↔ (b % 2 = 1)) := Nat.xor_mod_two_eq_one
      have mo2 := Nat.mod_two_eq_zero_or_one (a ||| b); have mn2 := Nat.mod_two_eq_zero_or_one (a &&& b)
      have mx2 := Nat.mod_two_eq_zero_or_one (a ^^^ b)
      rw [e1, e2, e3]
      rcases ma with ma | ma <;> rcases mb with mb | mb <;> rcases mo2 with mo2 | mo2 <;> rcases mn2 with mn2 | mn2 <;>
        rcases mx2 with mx2 | mx2 <;> simp_all <;> omega

theorem xor_eq_or_sub_and (a b : BitVec 64) : a ^^^ b = (a ||| b) - (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or]
  have h := nat_or_xor_and a.toNat b.toNat
  have ha := a.isLt; have hb := b.isLt
  have h1 : a.toNat ||| b.toNat < 2 ^ 64 := Nat.or_lt_two_pow ha hb
  omega

/-! ## the meaning of the stack operations (value stack top first) -/

def _root_.Nano.V2.SOp.run : SOp → List (BitVec 64) → List (BitVec 64)
  | .dup j, st => st.getD j 0 :: st
  | .shr k, x :: st => (x >>> k) :: st
  | .bin k, y :: x :: st => opv k x y :: st
  | .lit n, st => n.toBitVec :: st
  | .slide k, x :: st => x :: st.drop k
  | .bor, y :: x :: st => (x ||| y) :: st
  | .shl k, x :: st => (x <<< k) :: st
  | _, st => st

def runOps : List SOp → List (BitVec 64) → List (BitVec 64)
  | [], st => st
  | o :: os, st => runOps os (o.run st)

/-- the operation fits the stack height `h` and the record fields -/
def _root_.Nano.V2.SOp.wf (h : Nat) : SOp → Bool
  | .dup j => decide (j < h) && decide (j < 256)
  | .shr k => decide (1 ≤ h) && decide (k < 64)
  | .bin k => decide (2 ≤ h) && (k == 24 || k == 32 || k == 40)
  | .lit _ => true
  | .slide k => decide (k + 1 ≤ h) && decide (k < 128)
  | .bor => decide (2 ≤ h)
  | .shl k => decide (1 ≤ h) && decide (k < 64)

def wfOps (h : Nat) : List SOp → Bool
  | [] => true
  | o :: os => o.wf h && wfOps (o.after h) os

theorem run_length (o : SOp) (st : List (BitVec 64)) (hw : o.wf st.length = true) :
    (o.run st).length = o.after st.length := by
  cases o <;> rcases st with _ | ⟨x, _ | ⟨y, st⟩⟩ <;> simp_all [SOp.run, SOp.after, SOp.wf] <;> omega

section ops
variable {P : List UInt8} {T W : Nat}

theorem stk_lo {s : St} {vals : List (BitVec 64)} (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W)
    (hW : W < 2 ^ 64) : W + 8 * vals.length ≤ T := by
  have := hs.lo; rw [h12] at this; simp at this; rw [Nat.mod_eq_of_lt hW] at this; exact this

/-- `ld t0, 8j(t6)`: the `j`-th value from the top -/
theorem dupld_ok {s : St} {j : Nat} {rest : List UInt8} {st : List (BitVec 64)}
    (h : CodeAt P s.pc (Nano.ld 5 31 j ++ rest)) (hs : Stk s T st.reverse) (hj : j < st.length) (hj2 : j < 256)
    (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ s'.get 5 = st.getD j 0 ∧ s'.m = s.m ∧ (∀ i, i ≠ 5 → s'.get i = s.get i) ∧
      CodeAt P s'.pc rest := by
  have hlo := hs.lo; have hal := hs.al; have hhi := hs.hi; have h31 := hs.top
  simp only [List.length_reverse] at hlo h31
  obtain ⟨x, c⟩ := ld_ok (rd := 5) h (by decide) hj2 h31 (by omega) (wok_of (by omega) (by omega) (by omega))
  refine ⟨_, x, ?_, rfl, fun i hi => by simp [St.get, St.set, hi], c⟩
  simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide), set_m]
  rw [show T - 8 * st.length + 8 * j = T - 8 * (st.length - 1 - j + 1) by omega]
  rw [hs.2 _ (by simp; omega), List.getElem_reverse, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]; congr 1; omega

/-- `top := top >>> k` -/
theorem shr_ok {s : St} {k : Nat} {rest : List UInt8} {x : BitVec 64} {st : List (BitVec 64)}
    (h : CodeAt P s.pc ((SOp.shr k).code ++ rest)) (hk : k < 64) (hs : Stk s T (x :: st).reverse) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ Stk s' T ((x >>> k) :: st).reverse ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv, hlo, hal, hhi⟩ := hs
  simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at h31 hv hlo
  have hx : rd64 s.m (T - 8 * (st.length + 1)) = x := by
    have := hv st.length (by simp); simpa using this
  simp only [SOp.code, List.append_assoc] at h
  obtain ⟨x1, c1⟩ := ld_ok (rd := 5) (k := 0) h (by decide) (by decide) h31 (by omega)
    (wok_of (by omega) (by omega) (by omega))
  generalize hs1 : ((({ s with pc := s.pc + 1 } : St)).set 5 (rd64 s.m (T - 8 * (st.length + 1) + 8 * 0))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have v1 : s1.get 5 = x := by rw [← hs1, get_set_same _ (by decide)]; simpa using hx
  simp only [Nano.r, List.cons_append, List.nil_append] at c1
  rw [← p1] at c1
  have x2 := one c1 (s' := (({ s1 with pc := s1.pc + 1 } : St).set 6 (s1.get 5 >>> k))) (by
    show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [toU8 (by omega)])
  generalize hs2 : (({ s1 with pc := s1.pc + 1 } : St).set 6 (s1.get 5 >>> k)) = s2 at x2
  have c2 := codeAt_drop c1; rw [show s1.pc + 1 = s2.pc by rw [← hs2]; rfl] at c2
  have x3 := one c2 (s' := (({ s2 with pc := s2.pc + 1 } : St).set 5 (s2.get 0 + sext8 0))) rfl
  generalize hs3 : (({ s2 with pc := s2.pc + 1 } : St).set 5 (s2.get 0 + sext8 0)) = s3 at x3
  have c3 := codeAt_drop c2; rw [show s2.pc + 1 = s3.pc by rw [← hs3]; rfl] at c3
  have x4 := one c3 (s' := (({ s3 with pc := s3.pc + 1 } : St).set 5 (s3.get 5 + s3.get 6))) rfl
  generalize hs4 : (({ s3 with pc := s3.pc + 1 } : St).set 5 (s3.get 5 + s3.get 6)) = s4 at x4
  have c4 := codeAt_drop c3; rw [show s3.pc + 1 = s4.pc by rw [← hs4]; rfl] at c4
  have k4 : ∀ j, j ≠ 5 → j ≠ 6 → s4.get j = s.get j := fun j a b => by
    rw [← hs4, get_set_ne _ a]; show s3.get j = _; rw [← hs3, get_set_ne _ a]; show s2.get j = _
    rw [← hs2, get_set_ne _ b]; show s1.get j = _; rw [← hs1, get_set_ne _ a]; rfl
  have v4 : s4.get 5 = x >>> k := by
    rw [← hs4, get_set_same _ (by decide)]
    have e5 : s3.get 5 = 0 := by rw [← hs3, get_set_same _ (by decide)]; rfl
    have e6 : s3.get 6 = x >>> k := by
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 6 = _; rw [← hs2, get_set_same _ (by decide), v1]
    rw [e5, e6]; simp
  have m4 : s4.m = s.m := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have g31 : s4.get 31 = BitVec.ofNat 64 (T - 8 * (st.length + 1)) := by rw [k4 31 (by decide) (by decide)]; exact h31
  have r12 : s4.get 12 = s.get 12 := k4 12 (by decide) (by decide)
  have r2 : s4.get 2 = s.get 2 := k4 2 (by decide) (by decide)
  obtain ⟨x5, c5⟩ := sd0_ok (s := s4) c4 g31 (by omega) (wok_of (by rw [r12]; omega) (by rw [r2]; omega) (by omega))
  refine ⟨_, x1.trans (x2.trans (x3.trans (x4.trans x5))), ⟨?_, fun j hj => ?_, ?_, hal, ?_⟩,
    fun j a b c => ?_, c5⟩
  · show s4.get 31 = _; rw [g31]; simp
  · simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at hj
    show rd64 (wr64 s4.m _ (s4.get 5)) _ = _
    by_cases hjn : j = st.length
    · subst hjn; rw [rd64_wr64_same, v4]; simp
    · rw [rd64_wr64_out _ _ _ _ (by omega), m4]
      have := hv j (by omega); simp only [List.reverse_cons] at this ⊢
      rwa [List.getElem_append_left (by simp; omega)] at this ⊢
  · show (s4.get 12).toNat + _ ≤ _; rw [r12]; simp; omega
  · show _ ≤ (s4.get 2).toNat; rw [r2]; exact hhi
  · show s4.get j = s.get j; exact k4 j a b

/-- `binop 14`: pop `b`, `a`; push `a ||| b` -/
theorem bor_ok {s : St} {rest : List UInt8}
    (h : CodeAt P s.pc (Nano.binop 14 ++ rest)) {vals : List (BitVec 64)} {va vb : BitVec 64}
    (hs : Stk s T (vals ++ [va, vb])) (hT : 8 * (vals.length + 2) ≤ T) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ s'.pc = s.pc + 5 ∧ Stk s' T (vals ++ [va ||| vb]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv, hlo, hal, hhi⟩ := hs
  simp only [List.length_append, List.length_cons, List.length_nil] at h31 hv hlo
  obtain ⟨n, hn⟩ : ∃ n, vals.length = n := ⟨_, rfl⟩
  rw [hn] at h31 hT hlo
  have hva : rd64 s.m (T - 8 * (n + 1)) = va := by
    have := hv n (by omega); rw [List.getElem_append_right (by omega)] at this; simpa [hn] using this
  have hvb : rd64 s.m (T - 8 * (n + 2)) = vb := by
    have := hv (n + 1) (by omega); rw [List.getElem_append_right (by omega)] at this; simpa [hn] using this
  simp only [Nano.binop, List.append_assoc] at h
  generalize ht : T - 8 * (n + 2) = t at h31 hvb
  obtain ⟨x1, c1⟩ := ld_ok (rd := 6) (k := 0) h (by decide) (by decide) h31 (by omega)
    (wok_of (by omega) (by omega) (by omega))
  generalize hs1 : ((({ s with pc := s.pc + 1 } : St)).set 6 (rd64 s.m (t + 8 * 0))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have g31 : s1.get 31 = BitVec.ofNat 64 t := by rw [← hs1, get_set_ne _ (by decide)]; exact h31
  have r12 : s1.get 12 = s.get 12 := by rw [← hs1, get_set_ne _ (by decide)]; rfl
  have r2 : s1.get 2 = s.get 2 := by rw [← hs1, get_set_ne _ (by decide)]; rfl
  obtain ⟨x2, c2⟩ := ld_ok (s := s1) (rd := 5) (k := 1) (p1 ▸ c1) (by decide) (by decide) g31 (by omega)
    (wok_of (by rw [r12]; omega) (by rw [r2]; omega) (by omega))
  generalize hs2 : ((({ s1 with pc := s1.pc + 1 } : St)).set 5 (rd64 s1.m (t + 8 * 1))) = s2 at x2
  have p2 : s2.pc = s.pc + 2 := by rw [← hs2]; simp [p1]
  have g31' : s2.get 31 = BitVec.ofNat 64 t := by rw [← hs2, get_set_ne _ (by decide)]; exact g31
  have r12' : s2.get 12 = s.get 12 := by rw [← hs2, get_set_ne _ (by decide)]; exact r12
  have r2' : s2.get 2 = s.get 2 := by rw [← hs2, get_set_ne _ (by decide)]; exact r2
  obtain ⟨x3, c3⟩ := addSp_ok (s := s2) (k := 1) (by rw [p2]; rw [p1] at c2; exact c2) (by decide) g31' (by omega)
  generalize hs3 : ((({ s2 with pc := s2.pc + 1 } : St)).set 31 (BitVec.ofNat 64 (t + 8 * 1))) = s3 at x3
  have p3 : s3.pc = s.pc + 3 := by rw [← hs3]; simp [p2]
  have c3' : CodeAt P s3.pc (Nano.r 14 5 5 6 ++ (Nano.sd 5 31 0 ++ rest)) := by rw [p3]; rw [p2] at c3; exact c3
  simp only [Nano.r, List.cons_append, List.nil_append] at c3'
  have x4 := one c3' (s' := ((({ s3 with pc := s3.pc + 1 } : St)).set 5 (s3.get 5 ||| s3.get 6))) rfl
  have c4 := codeAt_drop c3'
  generalize hs4 : ((({ s3 with pc := s3.pc + 1 } : St)).set 5 (s3.get 5 ||| s3.get 6)) = s4 at x4
  have p4 : s4.pc = s.pc + 4 := by rw [← hs4]; simp [p3]
  have g31'' : s4.get 31 = BitVec.ofNat 64 (t + 8) := by
    rw [← hs4, get_set_ne _ (by decide)]; show s3.get 31 = _; rw [← hs3]; simp
  have r12'' : s4.get 12 = s.get 12 := by
    rw [← hs4, get_set_ne _ (by decide)]; show s3.get 12 = _; rw [← hs3, get_set_ne _ (by decide)]; exact r12'
  have r2'' : s4.get 2 = s.get 2 := by
    rw [← hs4, get_set_ne _ (by decide)]; show s3.get 2 = _; rw [← hs3, get_set_ne _ (by decide)]; exact r2'
  obtain ⟨x5, c5⟩ := sd0_ok (s := s4) (by rw [p4]; rw [p3] at c4; exact c4) g31'' (by omega)
    (wok_of (by rw [r12'']; omega) (by rw [r2'']; omega) (by omega))
  have m4 : s4.m = s.m := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have v5 : s4.get 5 = va ||| vb := by
    rw [← hs4]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]
    have e5 : s3.get 5 = va := by
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 5 = _
      rw [← hs2]; simp only [get_set_same _ (show (5 : Nat) ≠ 0 by decide)]
      rw [show s1.m = s.m by rw [← hs1]; rfl, ← hva]; congr 1; omega
    have e6 : s3.get 6 = vb := by
      rw [← hs3, get_set_ne _ (by decide)]; show s2.get 6 = _
      rw [← hs2, get_set_ne _ (by decide)]; show s1.get 6 = _
      rw [← hs1]; simp only [get_set_same _ (show (6 : Nat) ≠ 0 by decide)]; rw [← hvb]; congr 1
    rw [e5, e6]
  refine ⟨_, x1.trans (x2.trans (x3.trans (x4.trans x5))), by simp [p4], ⟨?_, fun j hj => ?_, ?_, hal, ?_⟩,
    fun j a b c => ?_, ?_⟩
  · show s4.get 31 = _; rw [g31'']; congr 1; simp; omega
  · simp only [List.length_append, List.length_singleton] at hj
    show rd64 (wr64 s4.m (t + 8) (s4.get 5)) _ = _
    by_cases hjn : j = n
    · subst hjn
      rw [show T - 8 * (j + 1) = t + 8 by omega, rd64_wr64_same, v5]; simp [hn]
    · rw [rd64_wr64_out _ _ _ _ (by omega), m4, List.getElem_append_left (by omega)]
      have := hv j (by omega); rwa [List.getElem_append_left (by omega)] at this
  · show (s4.get 12).toNat + _ ≤ _; rw [r12'']; simp; omega
  · show _ ≤ (s4.get 2).toNat; rw [r2'']; exact hhi
  · show s4.get j = s.get j
    rw [← hs4, ← hs3, ← hs2, ← hs1]; simp [St.get, St.set, a, b, c]
  · show CodeAt P (s4.pc + 1) rest; rw [p4]; rw [p4] at c5; exact c5

/-- `top := top <<< k` -/
theorem shl_ok {s : St} {k : Nat} {rest : List UInt8} {x : BitVec 64} {st : List (BitVec 64)}
    (h : CodeAt P s.pc ((SOp.shl k).code ++ rest)) (hk : k < 64) (hs : Stk s T (x :: st).reverse) (hT2 : T < 2 ^ 64) :
    ∃ s', Star P s s' ∧ Stk s' T ((x <<< k) :: st).reverse ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  obtain ⟨h31, hv, hlo, hal, hhi⟩ := hs
  simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at h31 hv hlo
  have hx : rd64 s.m (T - 8 * (st.length + 1)) = x := by
    have := hv st.length (by simp); simpa using this
  simp only [SOp.code, List.append_assoc] at h
  obtain ⟨x1, c1⟩ := ld_ok (rd := 5) (k := 0) h (by decide) (by decide) h31 (by omega)
    (wok_of (by omega) (by omega) (by omega))
  generalize hs1 : ((({ s with pc := s.pc + 1 } : St)).set 5 (rd64 s.m (T - 8 * (st.length + 1) + 8 * 0))) = s1 at x1
  have p1 : s1.pc = s.pc + 1 := by rw [← hs1]; rfl
  have v1 : s1.get 5 = x := by rw [← hs1, get_set_same _ (by decide)]; simpa using hx
  simp only [Nano.r, List.cons_append, List.nil_append] at c1
  rw [← p1] at c1
  have x2 := one c1 (s' := (({ s1 with pc := s1.pc + 1 } : St).set 5 (s1.get 5 <<< k))) (by
    show Out.next _ = _; simp only [UInt8.reduceToNat]; rw [toU8 (by omega)])
  generalize hs2 : (({ s1 with pc := s1.pc + 1 } : St).set 5 (s1.get 5 <<< k)) = s2 at x2
  have c2 := codeAt_drop c1; rw [show s1.pc + 1 = s2.pc by rw [← hs2]; rfl] at c2
  have k2 : ∀ j, j ≠ 5 → s2.get j = s.get j := fun j a => by
    rw [← hs2, get_set_ne _ a]; show s1.get j = _; rw [← hs1, get_set_ne _ a]; rfl
  have v2 : s2.get 5 = x <<< k := by rw [← hs2, get_set_same _ (by decide), v1]
  have m2 : s2.m = s.m := by rw [← hs2, ← hs1]; rfl
  have g31 : s2.get 31 = BitVec.ofNat 64 (T - 8 * (st.length + 1)) := by rw [k2 31 (by decide)]; exact h31
  have r12 : s2.get 12 = s.get 12 := k2 12 (by decide)
  have r2 : s2.get 2 = s.get 2 := k2 2 (by decide)
  obtain ⟨x3, c3⟩ := sd0_ok (s := s2) c2 g31 (by omega) (wok_of (by rw [r12]; omega) (by rw [r2]; omega) (by omega))
  refine ⟨_, x1.trans (x2.trans x3), ⟨?_, fun j hj => ?_, ?_, hal, ?_⟩, fun j a b c => ?_, c3⟩
  · show s2.get 31 = _; rw [g31]; simp
  · simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at hj
    show rd64 (wr64 s2.m _ (s2.get 5)) _ = _
    by_cases hjn : j = st.length
    · subst hjn; rw [rd64_wr64_same, v2]; simp
    · rw [rd64_wr64_out _ _ _ _ (by omega), m2]
      have := hv j (by omega); simp only [List.reverse_cons] at this ⊢
      rwa [List.getElem_append_left (by simp; omega)] at this ⊢
  · show (s2.get 12).toNat + _ ≤ _; rw [r12]; simp; omega
  · show _ ≤ (s2.get 2).toNat; rw [r2]; exact hhi
  · show s2.get j = s.get j; exact k2 j a

/-- **one stack operation** (room for its push) -/
theorem op_ok (hT2 : T < 2 ^ 64) (hW : W < 2 ^ 64) (o : SOp) (st : List (BitVec 64)) (s : St) (rest : List UInt8)
    (h : CodeAt P s.pc (o.code ++ rest)) (hs : Stk s T st.reverse) (h12 : s.get 12 = BitVec.ofNat 64 W)
    (hw : o.wf st.length = true) (hfit : W + 8 * o.peak st.length ≤ T) :
    ∃ s', Star P s s' ∧ Stk s' T (o.run st).reverse ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  have hlo := stk_lo hs h12 hW; simp only [List.length_reverse] at hlo
  cases o with
  | dup j =>
    simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [SOp.code, List.append_assoc] at h
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := dupld_ok h hs hw.1 hw.2 hT2
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)) (k1 12 (by decide)) (k1 2 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by simp only [SOp.peak] at hfit; simp; omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1] at st2; simpa [SOp.run] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | lit n =>
    simp only [SOp.code, List.append_assoc] at h
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)) (k1 12 (by decide)) (k1 2 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by simp only [SOp.peak] at hfit; simp; omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1] at st2; simpa [SOp.run] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | shr k =>
    simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    match st, hs, hw with
    | x :: st, hs, hw => exact shr_ok h hw.2 hs hT2
  | bin k =>
    simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hw
    match st, hs, hw with
    | y :: x :: st, hs, hw =>
      simp only [SOp.code] at h
      have hs' : Stk s T (st.reverse ++ [x, y]) := by simpa using hs
      obtain ⟨s', x', -, st', k', c'⟩ := binop_ok (by rcases hw.2 with (e | e) | e <;> simp [e]) h hs' (by simp at hlo ⊢; omega) hT2
      exact ⟨s', x', by simpa [SOp.run] using st', k', c'⟩
  | slide k =>
    simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    match st, hs, hw with
    | x :: st, hs, hw =>
      simp only [SOp.code] at h
      have hlo' := stk_lo hs h12 hW; simp only [List.length_reverse, List.length_cons] at hlo' hw
      have e : (x :: st).reverse = (st.drop k).reverse ++ (st.take k).reverse ++ [x] := by
        rw [List.reverse_cons, ← List.reverse_append, List.take_append_drop]
      rw [e] at hs
      obtain ⟨s', x', st', k', c'⟩ := tail_ok h hs (by simp; omega) hw.2 (by simp; omega) hT2
      exact ⟨s', x', by simpa [SOp.run] using st', k', c'⟩
  | bor =>
    simp only [SOp.wf, decide_eq_true_eq] at hw
    match st, hs, hw with
    | y :: x :: st, hs, hw =>
      simp only [SOp.code] at h
      have hs' : Stk s T (st.reverse ++ [x, y]) := by simpa using hs
      obtain ⟨s', x', -, st', k', c'⟩ := bor_ok h hs' (by simp at hlo ⊢; omega) hT2
      exact ⟨s', x', by simpa [SOp.run] using st', k', c'⟩
  | shl k =>
    simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    match st, hs, hw with
    | x :: st, hs, hw => exact shl_ok h hw.2 hs hT2

/-- **a list of stack operations** (room for its peak) -/
theorem ops_ok (hT2 : T < 2 ^ 64) (hW : W < 2 ^ 64) : ∀ (ops : List SOp) (st : List (BitVec 64)) (s : St)
    (rest : List UInt8), CodeAt P s.pc (opsCode ops ++ rest) → Stk s T st.reverse → s.get 12 = BitVec.ofNat 64 W →
    wfOps st.length ops = true → W + 8 * peakOps st.length ops ≤ T →
    ∃ s', Star P s s' ∧ Stk s' T (runOps ops st).reverse ∧ Kept s s' ∧ CodeAt P s'.pc rest
  | [], st, s, rest, h, hs, _, _, _ => ⟨s, .refl _, hs, fun _ _ _ _ => rfl, by simpa [opsCode] using h⟩
  | o :: os, st, s, rest, h, hs, h12, hw, hfit => by
    simp only [wfOps, Bool.and_eq_true] at hw; simp only [peakOps] at hfit
    simp only [opsCode, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1⟩ := op_ok hT2 hW o st s _ h hs h12 hw.1 (by omega)
    obtain ⟨s2, x2, st2, k2, c2⟩ := ops_ok hT2 hW os (o.run st) s1 rest c1 st1
      (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by rw [run_length o st hw.1]; exact hw.2)
      (by rw [run_length o st hw.1]; omega)
    exact ⟨s2, x1.trans x2, st2, k1.trans k2, c2⟩

theorem peak_ge : ∀ (h : Nat) (ops : List SOp), h ≤ peakOps h ops
  | h, [] => Nat.le_refl _
  | h, o :: os => by
    simp only [peakOps]; have : h ≤ o.peak h := by cases o <;> simp [SOp.peak]
    omega

/-- **a list of stack operations without room**: the first push past the work block sets the flag -/
theorem ops_fail (hT2 : T < 2 ^ 64) (hW8 : 8 ≤ W) (hW : W < 2 ^ 64) : ∀ (ops : List SOp) (st : List (BitVec 64))
    (s : St) (rest : List UInt8), CodeAt P s.pc (opsCode ops ++ rest) → Stk s T st.reverse →
    s.get 12 = BitVec.ofNat 64 W → wfOps st.length ops = true → T < W + 8 * peakOps st.length ops →
    ∃ s', Star P s s' ∧ Oom P (s.get 1) s'
  | [], st, s, rest, h, hs, h12, _, hfit => by
    have := stk_lo hs h12 hW; simp [peakOps] at hfit this; omega
  | o :: os, st, s, rest, h, hs, h12, hw, hfit => by
    simp only [wfOps, Bool.and_eq_true] at hw; simp only [peakOps] at hfit
    simp only [opsCode, List.append_assoc] at h
    have hlo := stk_lo hs h12 hW; simp only [List.length_reverse] at hlo
    by_cases h1 : W + 8 * o.peak st.length ≤ T
    · obtain ⟨s1, x1, st1, k1, c1⟩ := op_ok hT2 hW o st s _ h hs h12 hw.1 h1
      obtain ⟨s2, x2, o2⟩ := ops_fail hT2 hW8 hW os (o.run st) s1 rest c1 st1
        (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by rw [run_length o st hw.1]; exact hw.2)
        (by rw [run_length o st hw.1]; omega)
      exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide) (by decide) (by decide))⟩
    · cases o with
      | dup j =>
        simp only [SOp.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
        simp only [SOp.code, List.append_assoc] at h
        simp only [SOp.peak] at h1
        obtain ⟨s1, x1, g1, m1, k1, c1⟩ := dupld_ok h hs hw.1.1 hw.1.2 hT2
        obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * st.length) (by rw [k1 31 (by decide)]; simpa using hs.top)
          (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) hW
        exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
      | lit n =>
        simp only [SOp.code, List.append_assoc] at h
        simp only [SOp.peak] at h1
        obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
        obtain ⟨s2, x2, o2⟩ := push_fail c1 (t := T - 8 * st.length) (by rw [k1 31 (by decide)]; simpa using hs.top)
          (by rw [k1 12 (by decide)]; exact h12) (by omega) (by omega) (by omega) hW
        exact ⟨s2, x1.trans x2, oom_kept o2 (k1 1 (by decide))⟩
      | shr k => simp only [SOp.peak] at h1; omega
      | bin k => simp only [SOp.peak] at h1; omega
      | slide k => simp only [SOp.peak] at h1; omega
      | bor => simp only [SOp.peak] at h1; omega
      | shl k => simp only [SOp.peak] at h1; omega

end ops

/-! ## what the comparison and selection operations compute -/

theorem runOps_append : ∀ (o1 o2 : List SOp) (st : List (BitVec 64)), runOps (o1 ++ o2) st = runOps o2 (runOps o1 st)
  | [], _, _ => rfl
  | o :: os, o2, st => runOps_append os o2 (o.run st)

theorem two_bv : (2 : UInt64).toBitVec = 2#64 := rfl
theorem one_bv : (1 : UInt64).toBitVec = 1#64 := rfl
theorem h63_bv : (0x8000000000000000 : UInt64).toBitVec = 0x8000000000000000#64 := rfl
theorem opv24 (a b : BitVec 64) : opv 24 a b = a + b := rfl
theorem opv32 (a b : BitVec 64) : opv 32 a b = a - b := rfl
theorem opv40 (a b : BitVec 64) : opv 40 a b = a * b := rfl

theorem ltu_run (a b : BitVec 64) (st : List (BitVec 64)) :
    runOps ltuOps (b :: a :: st) = (if a.toNat < b.toNat then 1#64 else 0#64) :: st := by
  rw [← ltu_bits]
  simp only [runOps, ltuOps, SOp.run, opv24, opv32, opv40, List.getD_cons_zero, List.getD_cons_succ, two_bv,
    List.drop_succ_cons, List.drop_zero]

theorem lts_pre (a b : BitVec 64) (st : List (BitVec 64)) :
    runOps [.dup 1, .lit 0x8000000000000000, .bin 24, .dup 1, .lit 0x8000000000000000, .bin 24] (b :: a :: st) =
      (b + 0x8000000000000000#64) :: (a + 0x8000000000000000#64) :: b :: a :: st := by
  simp only [runOps, SOp.run, opv24, List.getD_cons_zero, List.getD_cons_succ, h63_bv]

theorem lts_run (a b : BitVec 64) (st : List (BitVec 64)) :
    runOps ltsOps (b :: a :: st) = (if a.slt b then 1#64 else 0#64) :: st := by
  rw [ltsOps, runOps_append, runOps_append, lts_pre, ltu_run, lts_bits]
  by_cases h : (a + 0x8000000000000000#64).toNat < (b + 0x8000000000000000#64).toNat
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem eq_run (a b : BitVec 64) (st : List (BitVec 64)) :
    runOps eqOps (b :: a :: st) = (if a = b then 1#64 else 0#64) :: st := by
  have e : runOps eqOps (b :: a :: st) = runOps ltuOps (1#64 :: (a - b) :: st) := by
    simp only [eqOps, List.cons_append, List.nil_append, runOps, SOp.run, opv32, one_bv]
  rw [e, ltu_run]
  have : (a - b).toNat < (1#64).toNat ↔ a = b := by
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [show (1#64).toNat = 1 from rfl, BitVec.toNat_sub] at h
      have := a.isLt; have := b.isLt; omega
    · rintro rfl; simp
  by_cases h : a = b
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun e => h (this.mp e)), if_neg h]

theorem sel_run (x c y : BitVec 64) (st : List (BitVec 64)) :
    runOps selOps (y :: c :: x :: st) = (x + c * (y - x)) :: st := by
  simp only [selOps, runOps, SOp.run, opv24, opv32, opv40, List.getD_cons_zero, List.getD_cons_succ]

theorem sel_one (x y : BitVec 64) : x + 1#64 * (y - x) = y := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub]
  have := x.isLt; have := y.isLt; rw [show (1#64).toNat = 1 from rfl]; omega
theorem sel_zero (x y : BitVec 64) : x + 0#64 * (y - x) = x := by simp

theorem wf_ltu (h : Nat) (hh : 2 ≤ h) : wfOps h ltuOps = true ∧ peakOps h ltuOps = h + 5 := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
  simp [wfOps, ltuOps, SOp.wf, SOp.after, peakOps, SOp.peak]
  try omega

theorem and_run (a b : BitVec 64) (st : List (BitVec 64)) : runOps andOps (b :: a :: st) = (a &&& b) :: st := by
  rw [and_eq_add_sub_or]
  simp only [andOps, runOps, SOp.run, opv24, opv32, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
    List.drop_zero]

theorem xor_run (a b : BitVec 64) (st : List (BitVec 64)) : runOps xorOps (b :: a :: st) = (a ^^^ b) :: st := by
  have e : runOps [.dup 1, .dup 1, .bor, .dup 2, .dup 2] (b :: a :: st) = b :: a :: (a ||| b) :: b :: a :: st := by
    simp only [runOps, SOp.run, List.getD_cons_zero, List.getD_cons_succ]
  rw [xorOps, runOps_append, runOps_append, e, and_run, xor_eq_or_sub_and]
  simp only [runOps, SOp.run, opv32, List.drop_succ_cons, List.drop_zero]

theorem or_run (a b : BitVec 64) (st : List (BitVec 64)) : runOps [.bor] (b :: a :: st) = (a ||| b) :: st := rfl

theorem bit_run (o : BOp) (a b : UInt64) (st : List (BitVec 64)) :
    runOps (bitOps o) (b.toBitVec :: a.toBitVec :: st) = (o.app a b).toBitVec :: st := by
  cases o
  · rw [bitOps, and_run]; rfl
  · rw [bitOps, or_run]; rfl
  · rw [bitOps, xor_run]; rfl

theorem sh_run (l : Bool) (k : Nat) (a : UInt64) (st : List (BitVec 64)) :
    runOps [shOp l (k % 64)] (a.toBitVec :: st) =
      (if l then a <<< k.toUInt64 else a >>> k.toUInt64).toBitVec :: st := by
  have hm : (k.toUInt64.toBitVec % 64#64).toNat = k % 64 := by
    rw [BitVec.toNat_umod]; simp [Nat.toUInt64]
  cases l
  · simp only [shOp, runOps, SOp.run, Bool.false_eq_true, if_false]
    rw [UInt64.toBitVec_shiftRight]; congr 2; exact hm.symm
  · simp only [shOp, runOps, SOp.run, if_true]
    rw [UInt64.toBitVec_shiftLeft]; congr 2; exact hm.symm

end Nano.V2R

/- Gen's expression templates on the abstract machine `CallProbe.J` (Proof/Call.lean; definitions reused, J gained alu/slli/lbu).
Templates exactly as Nano/V2Self/C/Gen.lean emits them (g21/g22 push, g23 li, g25 LOCAL, g30/g31 BIN, g32 prims).
Every lemma is stated for an ARBITRARY live stack prefix: cells at or above the pre-op sp are untouched (except the result
cell), registers outside the written set are unchanged (s0 = x8, the heap top t5 = x30 included), and the push-type
templates take the capacity exit when t6 − 8 < t5. -/
import Nano.V2Self.Proof.Call
namespace CallProbe

theorem upd_upd {α} (f : Nat → α) (k : Nat) (a b : α) : upd (upd f k a) k b = upd f k b := by
  funext i; by_cases h : i = k <;> simp [upd, h]

/-- push to the capacity exit: t6 − 8 < t5 ⇒ the third instruction (`jal x0 oom`) transfers to the stub -/
theorem push_oom {C pc s r oom} (hC : At C pc (push r oom)) (h8 : 8 ≤ (s.x 31).toNat)
    (hh : (s.x 31).toNat < (s.x 30).toNat + 8) :
    run C 3 (pc, s) = some (((pc : Int) + 2 + oom).toNat, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), s.m⟩) := by
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e : ea (s.x 31) (-8) = (s.x 31).toNat - 8 := by simp [ea]; omega
  have t6' : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by
    simp [UInt64.toNat_ofNat]; omega
  have h0 := hC.at 0 (by simp [push]); have h1 := hC.at 1 (by simp [push]); have h2 := hC.at 2 (by simp [push])
  simp only [push, Nat.add_zero] at h0 h1 h2
  simp at h0 h1 h2
  have c1 : ¬ (s.x 30).toNat ≤ (UInt64.ofNat ((s.x 31).toNat - 8)).toNat := by rw [t6']; omega
  have c2 : ¬ (s.x 30).toNat ≤ (s.x 31).toNat - 8 := by omega
  simp [run, step, h0, h1, h2, e, wr, upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), c2, t6',
    show pc + 1 + 1 = pc + 2 by omega]

/-! ## li (g23): `addi d x0 v` if v < 2048, else `addi d x0 0` then 8 × (`slli d d 8`, `addi d d byte`) from the top byte -/
def liJ (d : Nat) (v : Nat) (j : Nat) : List J := [.slli d d 8, .addi d d (((v / 2 ^ (56 - 8 * j)) % 256 : Nat) : Int)]
def liB (d v : Nat) : Nat → List J
  | 0 => []
  | k + 1 => liB d v k ++ liJ d v k
def liT (d : Nat) (v : UInt64) : List J :=
  if v.toNat < 2048 then [.addi d 0 (v.toNat : Int)] else .addi d 0 0 :: liB d v.toNat 8

theorem liB_len (d v) : ∀ k, (liB d v k).length = 2 * k
  | 0 => rfl
  | k + 1 => by simp [liB, liJ, liB_len d v k]; omega
theorem liT_len_small (d v) (h : v.toNat < 2048) : (liT d v).length = 1 := by simp [liT, h]
theorem liT_len_big (d v) (h : ¬ v.toNat < 2048) : (liT d v).length = 17 := by simp [liT, h, liB_len]

theorem liB_prefix (d v : Nat) : ∀ n k, k ≤ n → ∃ l, liB d v n = liB d v k ++ l
  | 0, k, h => ⟨[], by rw [show k = 0 by omega]; simp [liB]⟩
  | n + 1, k, h => by
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · obtain ⟨l, hl⟩ := liB_prefix d v n k (by omega); exact ⟨l ++ liJ d v n, by simp [liB, hl]⟩
    · exact ⟨[], by rw [show k = n + 1 by omega]; simp⟩

theorem liB_at {C pc d v n k} (h : At C pc (liB d v n)) (hk : k ≤ n) : At C pc (liB d v k) := by
  obtain ⟨l, hl⟩ := liB_prefix d v n k hk; rw [hl] at h; exact h.left

theorem At.cons_tail {C pc a l} (h : At C pc (a :: l)) : At C (pc + 1) l := by
  have := h.right (l1 := [a]); simpa using this

/-- the loop of the big case: after `1 + 2j` instructions, d holds the top j bytes -/
theorem li_loop {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hx0 : s.x 0 = 0) (hv : ¬ v.toNat < 2048)
    (hC : At C pc (liT d v)) :
    ∀ j, j ≤ 8 → ∃ sj, run C (1 + 2 * j) (pc, s) = some (pc + 1 + 2 * j, sj) ∧
      sj.x = upd s.x d (UInt64.ofNat (v.toNat / 2 ^ (64 - 8 * j))) ∧ sj.m = s.m
  | 0, _ => by
      have h0 := hC.at 0 (by simp [liT_len_big d v hv])
      simp [liT, hv] at h0
      refine ⟨⟨upd s.x d 0, s.m⟩, ?_, ?_, rfl⟩
      · simp [run, step, h0, wr, hd, ea, hx0]
      · have : v.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt v.toNat_lt
        simp [this]
  | j + 1, hj => by
      obtain ⟨sj, hr, hx, hm⟩ := li_loop s hd hx0 hv hC j (by omega)
      have hC' : At C pc (.addi d 0 0 :: liB d v.toNat 8) := by simpa [liT, hv] using hC
      have hT : At C (pc + 1) (liB d v.toNat 8) := hC'.cons_tail
      have hA := liB_at hT (show j + 1 ≤ 8 by omega)
      have h0 : C[pc + 1 + 2 * j]? = some (.slli d d 8) := by
        have := hA.at (2 * j) (by simp [liB_len] <;> omega); simp [liB, liJ, liB_len] at this; exact this
      have h1 : C[pc + 1 + 2 * j + 1]? = some (.addi d d (((v.toNat / 2 ^ (56 - 8 * j)) % 256 : Nat) : Int)) := by
        have := hA.at (2 * j + 1) (by simp [liB_len] <;> omega)
        simp [liB, liJ, liB_len] at this; rw [← Nat.add_assoc] at this; exact this
      have hj7 : j ≤ 7 := by omega
      have hP : 2 ^ (64 - 8 * j) = 2 ^ (56 - 8 * j) * 256 := by
        rw [show 64 - 8 * j = (56 - 8 * j) + 8 by omega, Nat.pow_add]
      have hP2 : 2 ^ (64 - 8 * (j + 1)) = 2 ^ (56 - 8 * j) := by congr 1; omega
      obtain ⟨A, hA'⟩ : ∃ A, A = v.toNat / 2 ^ (64 - 8 * j) := ⟨_, rfl⟩
      rw [← hA'] at hx
      have hApos : 0 < 2 ^ (56 - 8 * j) := Nat.two_pow_pos _
      have hAlt : A < 2 ^ (8 * j) := by
        rw [hA', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        have := v.toNat_lt
        calc v.toNat < 2 ^ 64 := this
          _ = 2 ^ (8 * j) * 2 ^ (64 - 8 * j) := by rw [← Nat.pow_add]; congr 1; omega
      have hA56 : A < 2 ^ 56 := Nat.lt_of_lt_of_le hAlt (Nat.pow_le_pow_right (by decide) (by omega))
      have hdiv : v.toNat / 2 ^ (56 - 8 * j) = A * 256 + (v.toNat / 2 ^ (56 - 8 * j)) % 256 := by
        rw [hA', hP, ← Nat.div_div_eq_div_mul]
        have := Nat.div_add_mod (v.toNat / 2 ^ (56 - 8 * j)) 256
        omega
      have hb : (v.toNat / 2 ^ (56 - 8 * j)) % 256 < 256 := Nat.mod_lt _ (by decide)
      have hshift : (UInt64.ofNat A <<< Nat.toUInt64 8) = UInt64.ofNat (A * 256) := by
        apply UInt64.toNat.inj
        simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
      have hxd : sj.x d = UInt64.ofNat A := by rw [hx, upd_same]
      have hT : v.toNat / 2 ^ (64 - 8 * (j + 1)) = A * 256 + (v.toNat / 2 ^ (56 - 8 * j)) % 256 := by
        rw [hP2]; exact hdiv
      generalize (v.toNat / 2 ^ (56 - 8 * j)) % 256 = b at h1 hb hT
      have e256 : UInt64.ofNat A * 256 = UInt64.ofNat (A * 256) := by
        apply UInt64.toNat.inj; simp [UInt64.toNat_mul]
      have t : (UInt64.ofNat (A * 256)).toNat = A * 256 := by simp; omega
      have eb : ea (UInt64.ofNat (A * 256)) (b : Int) = A * 256 + b := by simp only [ea, t]; omega
      have eb2 : UInt64.ofNat (ea (UInt64.ofNat (A * 256)) (b : Int)) = UInt64.ofNat (A * 256 + b) := by rw [eb]
      refine ⟨⟨upd s.x d (UInt64.ofNat (A * 256 + b)), s.m⟩, ?_, ?_, rfl⟩
      · rw [show 1 + 2 * (j + 1) = (1 + 2 * j) + 2 by omega, run_add hr]
        simp only [run, step, h0, h1, wr, if_neg hd, Option.bind_some, hxd, hm, hshift, eb2, show pc + 1 + 2 * j + 1 + 1 = pc + 1 + 2 * (j + 1) by omega]
        rw [upd_same, eb2]
        congr 3
        funext i
        by_cases h : i = d <;> simp [upd, h, hx]
      · rw [hT]

theorem li_run {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hx0 : s.x 0 = 0) (hC : At C pc (liT d v)) :
    ∃ s', run C (liT d v).length (pc, s) = some (pc + (liT d v).length, s') ∧ s'.x = upd s.x d v ∧ s'.m = s.m := by
  by_cases hv : v.toNat < 2048
  · have h0 := hC.at 0 (by simp [liT_len_small d v hv])
    simp [liT, hv] at h0
    refine ⟨⟨upd s.x d v, s.m⟩, ?_, rfl, rfl⟩
    rw [liT_len_small d v hv]
    simp [run, step, h0, wr, hd, ea, hx0]
  · obtain ⟨s', hr, hx, hm⟩ := li_loop s hd hx0 hv hC 8 (by omega)
    refine ⟨s', ?_, ?_, hm⟩
    · rw [liT_len_big d v hv]; simpa using hr
    · rw [hx]; simp

/-- push at an absolute position: the capacity stub is word `tgt` -/
def pushA (tgt q r : Nat) : List J := push r ((tgt : Int) - ((q : Int) + 2))

theorem pushA_oom_target (tgt q : Nat) : ((q : Int) + 2 + ((tgt : Int) - ((q : Int) + 2))).toNat = tgt := by omega

/-- CONST v (g21 (g23 o 5 v)) -/
def constT (tgt q : Nat) (v : UInt64) : List J := liT 5 v ++ pushA tgt (q + (liT 5 v).length) 5

theorem const_run {C pc tgt} {v : UInt64} (s : St) (hx0 : s.x 0 = 0) (hC : At C pc (constT tgt pc v))
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) :
    ∃ s', run C ((liT 5 v).length + 3) (pc, s) = some (pc + (liT 5 v).length + 4, s') ∧
      s'.x = upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)) ∧
      s'.m = upd s.m ((s.x 31).toNat - 8) v := by
  obtain ⟨s1, hr1, hx1, hm1⟩ := li_run (d := 5) s (by decide) hx0 hC.left
  have hP : At C (pc + (liT 5 v).length) (push 5 ((tgt : Int) - ((pc + (liT 5 v).length : Nat) + 2))) := by
    simpa [constT, pushA] using hC.right
  have hh1 : (s1.x 30).toNat + 8 ≤ (s1.x 31).toNat := by
    rw [hx1]; simpa [upd, show (30 : Nat) ≠ 5 by decide, show (31 : Nat) ≠ 5 by decide] using hh
  have r2 := push_run (s := s1) hP (by decide) (by decide) hh1
  have e31 : s1.x 31 = s.x 31 := by rw [hx1]; exact upd_other _ _ (by decide)
  have e5 : s1.x 5 = v := by rw [hx1]; exact upd_same _ _ _
  refine ⟨⟨upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) v⟩, ?_, rfl, rfl⟩
  rw [run_add hr1, r2, e31, e5, hx1, hm1]

/-- CONST at the capacity exit: t6 − 8 < t5 ⇒ control reaches the stub `tgt`, nothing at or above sp changed -/
theorem const_oom {C pc tgt} {v : UInt64} (s : St) (hx0 : s.x 0 = 0) (hC : At C pc (constT tgt pc v))
    (h8 : 8 ≤ (s.x 31).toNat) (hh : (s.x 31).toNat < (s.x 30).toNat + 8) :
    ∃ s', run C ((liT 5 v).length + 3) (pc, s) = some (tgt, s') ∧
      s'.x = upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)) ∧ s'.m = s.m := by
  obtain ⟨s1, hr1, hx1, hm1⟩ := li_run (d := 5) s (by decide) hx0 hC.left
  have hP : At C (pc + (liT 5 v).length) (push 5 ((tgt : Int) - ((pc + (liT 5 v).length : Nat) + 2))) := by
    simpa [constT, pushA] using hC.right
  have e31 : s1.x 31 = s.x 31 := by rw [hx1]; exact upd_other _ _ (by decide)
  have e30 : s1.x 30 = s.x 30 := by rw [hx1]; exact upd_other _ _ (by decide)
  have r2 := push_oom (s := s1) hP (by rw [e31]; exact h8) (by rw [e31, e30]; exact hh)
  refine ⟨⟨upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)), s.m⟩, ?_, rfl, rfl⟩
  rw [run_add hr1, r2, e31, hx1, hm1]
  have : (((pc + (liT 5 v).length : Nat) : Int) + 2 + ((tgt : Int) - (((pc + (liT 5 v).length : Nat) : Int) + 2))).toNat = tgt := by omega
  rw [this]

/-! ## BIN (g30 + g31): pop two (t1 := top, t0 := below), t6 += 8, t0 := t0 op t1, store over the new top -/
def binT (op : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 8, .alu op 5 5 6, .sd 5 31 0]

theorem bin_run {C pc op} (s : St) (hC : At C pc (binT op)) (hlt : (s.x 31).toNat + 16 < 2 ^ 63) :
    run C 5 (pc, s) = some (pc + 5,
      ⟨upd (upd (upd (upd s.x 6 (s.m (s.x 31).toNat)) 5 (s.m ((s.x 31).toNat + 8))) 31 (UInt64.ofNat ((s.x 31).toNat + 8))) 5
          (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)),
       upd s.m ((s.x 31).toNat + 8) (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat))⟩) := by
  have h0 := hC.at 0 (by simp [binT]); have h1 := hC.at 1 (by simp [binT]); have h2 := hC.at 2 (by simp [binT])
  have h3 := hC.at 3 (by simp [binT]); have h4 := hC.at 4 (by simp [binT])
  simp [binT] at h0 h1 h2 h3 h4
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8 : (UInt64.ofNat ((s.x 31).toNat + 8)).toNat = (s.x 31).toNat + 8 := by simp only [UInt64.toNat_ofNat']; omega
  have e8' : ea (UInt64.ofNat ((s.x 31).toNat + 8)) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8]; omega
  have t8' : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e8'' : ea (s.x 31 + 8) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8']; omega
  simp [run, step, h0, h1, h2, h3, h4, wr, e0, e8, e8'', upd_same, upd_other _ _ (show (6:Nat) ≠ 31 by decide),
    upd_other _ _ (show (5:Nat) ≠ 31 by decide), upd_other _ _ (show (5:Nat) ≠ 6 by decide), e8', t8,
    upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide),
    upd_other _ _ (show (6:Nat) ≠ 5 by decide)]

/-- ISIZE / LEN (g32 p = 1, 3): push t4 (the input length) -/
def lenT (tgt q : Nat) : List J := pushA tgt q 29

theorem len_run {C pc tgt} (s : St) (hC : At C pc (lenT tgt pc)) (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) :
    run C 3 (pc, s) = some (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 29)⟩) :=
  push_run (by simpa [lenT, pushA] using hC) (by decide) (by decide) hh

theorem len_oom {C pc tgt} (s : St) (hC : At C pc (lenT tgt pc)) (h8 : 8 ≤ (s.x 31).toNat)
    (hh : (s.x 31).toNat < (s.x 30).toNat + 8) :
    run C 3 (pc, s) = some (tgt, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), s.m⟩) := by
  have := push_oom (s := s) (by simpa [lenT, pushA] using hC) h8 hh
  rw [this]; simp only [pushA_oom_target]

/-! ## BSIZE (g32 p = 6): top := header length word of the buffer on top -/
def bsizeT : List J := [.ld 5 31 0, .ld 5 5 0, .sd 5 31 0]

theorem bsize_run {C pc} (s : St) (hC : At C pc bsizeT) :
    run C 3 (pc, s) = some (pc + 3, ⟨upd s.x 5 (s.m (s.m (s.x 31).toNat).toNat), upd s.m (s.x 31).toNat (s.m (s.m (s.x 31).toNat).toNat)⟩) := by
  have h0 := hC.at 0 (by simp [bsizeT]); have h1 := hC.at 1 (by simp [bsizeT]); have h2 := hC.at 2 (by simp [bsizeT])
  simp [bsizeT] at h0 h1 h2
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  simp [run, step, h0, h1, h2, wr, e0, e1, upd_same, upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_upd]

/-! ## RD (g32 p = 2): top := the input byte at index top (0 if out of range); t3 = input base, t4 = input length -/
def rdT : List J := [.ld 6 31 0, .addi 5 0 0, .bgeu 6 29 3, .alu 1 5 28 6, .lbu 5 5 0, .sd 5 31 0]

theorem rd_run {C pc} (s : St) (hC : At C pc rdT) (hx0 : s.x 0 = 0) (hb : (s.x 28).toNat + (s.x 29).toNat < 2 ^ 63) :
    ∃ k, run C k (pc, s) = some (pc + 6,
      ⟨upd (upd s.x 6 (s.m (s.x 31).toNat)) 5
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0),
       upd s.m (s.x 31).toNat
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0)⟩) := by
  have h0 := hC.at 0 (by simp [rdT]); have h1 := hC.at 1 (by simp [rdT]); have h2 := hC.at 2 (by simp [rdT])
  have h3 := hC.at 3 (by simp [rdT]); have h4 := hC.at 4 (by simp [rdT]); have h5 := hC.at 5 (by simp [rdT])
  simp [rdT] at h0 h1 h2 h3 h4 h5
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  by_cases hi : (s.m (s.x 31).toNat).toNat < (s.x 29).toNat
  · refine ⟨6, ?_⟩
    have hs : (s.x 28 + s.m (s.x 31).toNat).toNat = (s.x 28).toNat + (s.m (s.x 31).toNat).toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hc : ¬ (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide),
      upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide),
      upd_other _ _ (show (29:Nat) ≠ 6 by decide)]
  · refine ⟨4, ?_⟩
    have hc : (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    simp [run, step, h0, h1, h2, h5, wr, e0, e1, hc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega]

end CallProbe

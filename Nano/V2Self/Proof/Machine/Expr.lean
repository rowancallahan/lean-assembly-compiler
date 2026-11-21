/- Gen's expression templates on the abstract machine `CallProbe.J` (Proof/Call.lean; definitions reused, J gained alu/slli/lbu).
Templates exactly as Nano/V2Self/C/Gen.lean emits them (g21/g22 push, g23 li, g25 LOCAL, g30/g31 BIN, g32 prims).
Every lemma is stated for an ARBITRARY live stack prefix: cells at or above the pre-op sp are untouched (except the result
cell), registers outside the written set are unchanged (s0 = x8, the heap top t5 = x30 included), and the push-type
templates take the capacity exit when t6 − 8 < t5. -/
import Nano.V2Self.Proof.Machine.Call
namespace CallProbe

theorem upd_ne {α} (f : Nat → α) {k i : Nat} (v : α) (h : i ≠ k) : upd f k v i = f i := upd_other f v h

theorem upd_upd {α} (f : Nat → α) (k : Nat) (a b : α) : upd (upd f k a) k b = upd f k b := by
  funext i; by_cases h : i = k <;> simp [upd, h]

/-- push to the capacity exit: t6 − 8 < t5 ⇒ the third instruction (`jal x0 oom`) transfers to the stub -/
theorem push_oom {C pc s r oom} (hC : At C pc (push r oom)) (h8 : 8 ≤ (s.x 31).toNat)
    (hh : (s.x 31).toNat < (s.x 30).toNat + 8) :
    run C 3 (pc, s) = some (((pc : Int) + 2 + oom).toNat, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), s.m, s.b, s.ly⟩) := by
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
      sj.x = upd s.x d (UInt64.ofNat (v.toNat / 2 ^ (64 - 8 * j))) ∧ sj.m = s.m ∧ sj.b = s.b
  | 0, _ => by
      have h0 := hC.at 0 (by simp [liT_len_big d v hv])
      simp [liT, hv] at h0
      refine ⟨⟨upd s.x d 0, s.m, s.b, s.ly⟩, ?_, ?_, rfl, rfl⟩
      · simp [run, step, h0, wr, hd, ea, hx0]
      · have : v.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt v.toNat_lt
        simp [this]
  | j + 1, hj => by
      obtain ⟨sj, hr, hx, hm, hbb⟩ := li_loop s hd hx0 hv hC j (by omega)
      have hww : sj.ly = s.ly := (run_star hr).w
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
      refine ⟨⟨upd s.x d (UInt64.ofNat (A * 256 + b)), s.m, s.b, s.ly⟩, ?_, ?_, rfl, rfl⟩
      · rw [show 1 + 2 * (j + 1) = (1 + 2 * j) + 2 by omega, run_add hr]
        simp only [run, step, h0, h1, wr, if_neg hd, Option.bind_some, hxd, hm, hshift, eb2, show pc + 1 + 2 * j + 1 + 1 = pc + 1 + 2 * (j + 1) by omega]
        rw [upd_same, eb2]
        congr 3
        all_goals try exact hww
        funext i
        by_cases h : i = d <;> simp [upd, h, hx]
      · rw [hT]

theorem li_run {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hx0 : s.x 0 = 0) (hC : At C pc (liT d v)) :
    ∃ s', run C (liT d v).length (pc, s) = some (pc + (liT d v).length, s') ∧ s'.x = upd s.x d v ∧ s'.m = s.m ∧ s'.b = s.b := by
  by_cases hv : v.toNat < 2048
  · have h0 := hC.at 0 (by simp [liT_len_small d v hv])
    simp [liT, hv] at h0
    refine ⟨⟨upd s.x d v, s.m, s.b, s.ly⟩, ?_, rfl, rfl, rfl⟩
    rw [liT_len_small d v hv]
    simp [run, step, h0, wr, hd, ea, hx0]
  · obtain ⟨s', hr, hx, hm, hbb⟩ := li_loop s hd hx0 hv hC 8 (by omega)
    refine ⟨s', ?_, ?_, hm, hbb⟩
    · rw [liT_len_big d v hv]; simpa using hr
    · rw [hx]; simp

/-- push at an absolute position: the capacity stub is word `tgt` -/
def pushA (tgt q r : Nat) : List J := push r ((tgt : Int) - ((q : Int) + 2))

/-- CONST v (g21 (g23 o 5 v)) -/
def constT (tgt q : Nat) (v : UInt64) : List J := liT 5 v ++ pushA tgt (q + (liT 5 v).length) 5

/-! ## BIN (g30 + g31): pop two (t1 := top, t0 := below), t6 += 8, t0 := t0 op t1, store over the new top -/
def binT (op : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 8, .alu op 5 5 6, .sd 5 31 0]

theorem bin_run {C pc op} (s : St) (hC : At C pc (binT op)) (hlt : (s.x 31).toNat + 16 < 2 ^ 63) :
    run C 5 (pc, s) = some (pc + 5,
      ⟨upd (upd (upd (upd s.x 6 (s.m (s.x 31).toNat)) 5 (s.m ((s.x 31).toNat + 8))) 31 (UInt64.ofNat ((s.x 31).toNat + 8))) 5
          (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)),
       upd s.m ((s.x 31).toNat + 8) (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)), s.b, s.ly⟩) := by
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

/-! ## BSIZE (g32 p = 6): top := header length word of the buffer on top -/
def bsizeT : List J := [.ld 5 31 0, .ld 5 5 0, .sd 5 31 0]

theorem bsize_run {C pc} (s : St) (hC : At C pc bsizeT) :
    run C 3 (pc, s) = some (pc + 3, ⟨upd s.x 5 (s.m (s.m (s.x 31).toNat).toNat), upd s.m (s.x 31).toNat (s.m (s.m (s.x 31).toNat).toNat), s.b, s.ly⟩) := by
  have h0 := hC.at 0 (by simp [bsizeT]); have h1 := hC.at 1 (by simp [bsizeT]); have h2 := hC.at 2 (by simp [bsizeT])
  simp [bsizeT] at h0 h1 h2
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  simp [run, step, h0, h1, h2, wr, e0, e1, upd_same, upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_upd]

/-! ## RD (g32 p = 2): top := the input byte at index top (0 if out of range); t3 = input base, t4 = input length -/
def rdT : List J := [.ld 6 31 0, .addi 5 0 0, .bgeu 6 29 3, .alu 1 5 28 6, .lbu 5 5 0, .sd 5 31 0]

/-- RD with its exact step count (6 in range, 4 out of range) -/
theorem rd_runK {C pc} (s : St) (hC : At C pc rdT) (hx0 : s.x 0 = 0) (hb : (s.x 28).toNat + (s.x 29).toNat < 2 ^ 63) :
    run C (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then 6 else 4) (pc, s) = some (pc + 6,
      ⟨upd (upd s.x 6 (s.m (s.x 31).toNat)) 5
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0),
       upd s.m (s.x 31).toNat
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0), s.b, s.ly⟩) := by
  have h0 := hC.at 0 (by simp [rdT]); have h1 := hC.at 1 (by simp [rdT]); have h2 := hC.at 2 (by simp [rdT])
  have h3 := hC.at 3 (by simp [rdT]); have h4 := hC.at 4 (by simp [rdT]); have h5 := hC.at 5 (by simp [rdT])
  simp [rdT] at h0 h1 h2 h3 h4 h5
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  by_cases hi : (s.m (s.x 31).toNat).toNat < (s.x 29).toNat
  · rw [if_pos hi]
    have hs : (s.x 28 + s.m (s.x 31).toNat).toNat = (s.x 28).toNat + (s.m (s.x 31).toNat).toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hc : ¬ (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide),
      upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide),
      upd_other _ _ (show (29:Nat) ≠ 6 by decide)]
  · rw [if_neg hi]
    have hc : (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    simp [run, step, h0, h1, h2, h5, wr, e0, e1, hc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega]

/-! ## BGET (g32 p = 7): top = index, below = buffer (layout [len][cap][words…]); result over the new top -/
def bgetT : List J :=
  [.ld 6 31 0, .ld 5 31 8, .addi 31 31 8, .ld 7 5 0, .addi 14 0 0, .bgeu 6 7 4, .slli 6 6 3, .alu 1 5 5 6, .ld 14 5 16, .sd 14 31 0]

/-- BGET with its exact step count (10 in range, 7 out of range) -/
theorem bget_runK {C pc} (s : St) (hC : At C pc bgetT) (hx0 : s.x 0 = 0) (hlt : (s.x 31).toNat + 16 < 2 ^ 63)
    (hb : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat > (s.m (s.x 31).toNat).toNat →
      (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat < 2 ^ 63) :
    ∃ s', run C (if (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat then 10 else 7) (pc, s)
      = some (pc + 10, s') ∧
      s'.m = upd s.m ((s.x 31).toNat + 8)
        (if (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat
         then s.m ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat) else 0) ∧
      s'.x 31 = UInt64.ofNat ((s.x 31).toNat + 8) ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
  have h0 := hC.at 0 (by simp [bgetT]); have h1 := hC.at 1 (by simp [bgetT]); have h2 := hC.at 2 (by simp [bgetT])
  have h3 := hC.at 3 (by simp [bgetT]); have h4 := hC.at 4 (by simp [bgetT]); have h5 := hC.at 5 (by simp [bgetT])
  have h6 := hC.at 6 (by simp [bgetT]); have h7 := hC.at 7 (by simp [bgetT]); have h8 := hC.at 8 (by simp [bgetT])
  have h9 := hC.at 9 (by simp [bgetT])
  simp [bgetT] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8 : (UInt64.ofNat ((s.x 31).toNat + 8)).toNat = (s.x 31).toNat + 8 := by simp only [UInt64.toNat_ofNat']; omega
  have t8' : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e8'' : ea (s.x 31 + 8) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8']; omega
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  by_cases hi : (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat
  · have hb' := hb hi
    simp only [if_pos hi]
    have s3 : (s.m (s.x 31).toNat <<< 3).toNat = 8 * (s.m (s.x 31).toNat).toNat := by
      simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hc : ¬ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    have sa : (s.m ((s.x 31).toNat + 8) + s.m (s.x 31).toNat <<< 3).toNat
        = (s.m ((s.x 31).toNat + 8)).toNat + 8 * (s.m (s.x 31).toNat).toNat := by
      rw [UInt64.toNat_add, s3]; simp; omega
    have ea16 : ea (s.m ((s.x 31).toNat + 8) + s.m (s.x 31).toNat <<< 3) 16
        = (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat := by
      simp only [ea, sa]; omega
    simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hc, t8, t8', s3, ea16]
    intro r h5' h6' h7' h14' h31'
    simp [upd, h5', h6', h7', h14', h31']
  · simp only [if_neg hi]
    have hc : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hc, t8, t8',
      show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega]
    intro r h5' h6' h7' h14' h31'
    simp [upd, h5', h6', h7', h14', h31']

/-! ## LOCAL (g25 + g24): for each word, `ld t0, off(s0)` then the checked push.  Slot k < p (an argument slot) at
s0 + 16 + 8(p−1−k), slot k ≥ p at s0 − 8(k−p+1). -/
def offOf (p k : Nat) : Int := if k < p then ((8 * (p - 1 - k) + 16 : Nat) : Int) else -((8 * (k - p + 1) : Nat) : Int)
def slotAddr (p k s0 : Nat) : Nat := if k < p then s0 + 16 + 8 * (p - 1 - k) else s0 - 8 * (k - p + 1)

def localT (tgt p : Nat) : Nat → Nat → Nat → List J
  | _, _, 0 => []
  | k, q, w + 1 => [.ld 5 8 (offOf p k)] ++ pushA tgt (q + 1) 5 ++ localT tgt p (k + 1) (q + 5) w

theorem localT_len (tgt p : Nat) : ∀ w k q, (localT tgt p k q w).length = 5 * w
  | 0, _, _ => rfl
  | w + 1, k, q => by simp [localT, pushA, push, localT_len tgt p w]; omega

theorem ea_slot (p k s0 : Nat) (hs : s0 < 2 ^ 62) (hp : p < 2 ^ 20) (hk : k < p ∨ 8 * (k - p + 1) ≤ s0) (u : UInt64)
    (hu : u.toNat = s0) : ea u (offOf p k) = slotAddr p k s0 := by
  unfold ea offOf slotAddr; rw [hu]; split <;> omega

end CallProbe

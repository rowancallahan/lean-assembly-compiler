/- `Implements1` (ONE resource bound, `Spec/Implements1.lean`) for: `List.take k`, `List.map (· + 1)`,
the byte sum (as a 64-bit word), both sorts (insertion sort `sortCode`: `space n = 0`; merge sort
`msortCode`: `space n = n + 71`).  `take`/`map`/`sum` are new `Mach.BStmt` programs compiled by the
middle layer (`compBF`, no slots: `space n = 15`, the frame cell that saves `gp` plus alignment); the
sorts reuse their region-form theorems (`sortCode_ok_m`, `msortCode_ok_m`, both through the middle layer). -/
import Riscv.Back.Implements1
import Riscv.Back.SortMerge
import Riscv.Back.Arr

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

open Proven (ult_ne toNat_inc toNat_ofNat_lt map_take_set setWidth_setWidth8)

theorem BExec.loop_inv {c : Mach.BExp} {b : Mach.BStmt} (I Q : Mach.BState → Prop) (μ : Mach.BState → Nat)
    (hstep : ∀ σ, I σ → c.denote σ.env ≠ 0 → ∃ σ₁, Mach.BExec b σ σ₁ ∧ I σ₁ ∧ μ σ₁ < μ σ)
    (hexit : ∀ σ, I σ → c.denote σ.env = 0 → Q σ) : ∀ σ, I σ → ∃ σ', Mach.BExec (.loop c b) σ σ' ∧ Q σ' := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    intro hI
    by_cases hc : c.denote σ.env = 0
    · exact ⟨σ, .loopF hc, hexit σ hI hc⟩
    · obtain ⟨σ₁, hb, hI₁, hlt⟩ := hstep σ hI hc
      obtain ⟨σ', hl, hQ⟩ := ih _ (h ▸ hlt) σ₁ rfl hI₁
      exact ⟨σ', .loopT hc hb hl, hQ⟩

theorem BExec.assign' {v : Nat} {e : Mach.BExp} {σ σ' : Mach.BState}
    (h : σ' = ⟨σ.env.set v (e.denote σ.env), σ.heap, σ.wheap⟩) : Mach.BExec (.assign v e) σ σ' := h ▸ .assign

/-! ## `(xs.take K).map f` into the output block -/

/-- `v4 := min K v1; v5 := 0; while v5 < v4 { v6 := in[v5]; out[v5] := g; v5 := v5 + 1 }` (`K` may not
read `v4`, `v5`; `g` reads the byte in `v6`) -/
def mapK (K g : Mach.BExp) : Mach.BStmt :=
  .seq (.assign 4 (.ite (.bin .ult K (.var 1)) K (.var 1)))
  (.seq (.assign 5 (.const 0))
   (.loop (.bin .ult (.var 5) (.var 4))
     (.seq (.load 6 0 (.var 5)) (.seq (.store 1 (.var 5) g) (.assign 5 (.bin .add (.var 5) (.const 1)))))))

theorem mapK_exec (K g : Mach.BExp) (f : BitVec 8 → BitVec 8)
    (hg : ∀ (env : Mach.BEnv) (x : BitVec 8), env 6 = x.setWidth 64 → (g.denote env).setWidth 8 = f x)
    (σ : Mach.BState) (xs out : List (BitVec 8)) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 64)
    (hout : min (K.denote σ.env).toNat xs.length ≤ out.length) :
    ∃ σ', Mach.BExec (mapK K g) σ σ' ∧
      σ'.heap = [xs, (xs.take (K.denote σ.env).toNat).map f ++ out.drop (min (K.denote σ.env).toNat xs.length)] := by
  let m := min (K.denote σ.env).toNat xs.length
  let v4 := (Mach.BExp.ite (.bin .ult K (.var 1)) K (.var 1)).denote σ.env
  have hm : v4.toNat = m := by
    simp only [v4, m, Mach.BExp.denote, Op.eval, h1]
    by_cases hlt : K.denote σ.env < BitVec.ofNat 64 xs.length
    · rw [if_pos hlt]; simp only [BitVec.lt_def, toNat_ofNat_lt hn] at hlt; simp; omega
    · rw [if_neg hlt]; simp only [BitVec.lt_def, toNat_ofNat_lt hn] at hlt; simp; omega
  obtain ⟨σ₁, hl, hq⟩ := BExec.loop_inv (c := .bin .ult (.var 5) (.var 4))
    (b := .seq (.load 6 0 (.var 5)) (.seq (.store 1 (.var 5) g) (.assign 5 (.bin .add (.var 5) (.const 1)))))
    (fun τ => τ.heap = [xs, (xs.take (τ.env 5).toNat).map f ++ out.drop (τ.env 5).toNat] ∧
      (τ.env 4).toNat = m ∧ (τ.env 5).toNat ≤ m)
    (fun τ => τ.heap = [xs, (xs.take m).map f ++ out.drop m])
    (fun τ => m - (τ.env 5).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨hh, h4, hle⟩ hc => by
      dsimp only at hh h4 hle; subst hh
      simp only [Mach.BExp.denote, ult_ne, h4] at hc
      have hx : (env 5).toNat < xs.length := by omega
      have ho : (env 5).toNat < out.length := by omega
      have e5 := toNat_inc (show (env 5).toNat < m by omega) (show m < 2 ^ 64 by omega)
      refine ⟨_, .seq (.load (by simp) (by simpa using hx))
        (.seq (.store (by simp) (by simp [Mach.BEnv.set, Mach.BExp.denote]; omega)) .assign), ⟨?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [Mach.BEnv.set, Mach.BExp.denote, Op.eval]
      all_goals simp only [show (5 : Nat) ≠ 6 by decide, show (4 : Nat) ≠ 5 by decide,
        show (4 : Nat) ≠ 6 by decide, if_false, if_true]
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set_cons_succ, List.set_cons_zero]
        rw [hg _ xs[(env 5).toNat] (by simp [Mach.BEnv.set]), map_take_set f hx ho, e5]
      · exact h4
      · rw [e5]; omega
      · rw [e5]; omega)
    (fun ⟨env, heap, wheap⟩ ⟨hh, h4, hle⟩ hc => by
      dsimp only at hh h4 hle ⊢
      have : ¬ (env 5).toNat < m := fun hlt => (ult_ne (a := env 5) (b := env 4)).2 (by rw [h4]; exact hlt) hc
      rw [hh, show (env 5).toNat = m by omega])
    ⟨(σ.env.set 4 v4).set 5 0, σ.heap, σ.wheap⟩
    ⟨by simpa [Mach.BEnv.set] using hh, by simpa [Mach.BEnv.set] using hm, by simp [Mach.BEnv.set]⟩
  refine ⟨σ₁, .seq (BExec.assign' rfl) (.seq (BExec.assign' rfl) hl), ?_⟩
  have : xs.take m = xs.take (K.denote σ.env).toNat := by
    simp only [m]; by_cases hle : (K.denote σ.env).toNat ≤ xs.length
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (Nat.le_refl _),
        List.take_of_length_le (by omega)]
  rw [hq, this]

/-! ## The byte sum, stored as 8 little-endian bytes -/

def sumLoop : Mach.BStmt :=
  .loop (.bin .ult (.var 5) (.var 1))
    (.seq (.load 6 0 (.var 5)) (.seq (.assign 4 (.bin .add (.var 4) (.var 6)))
      (.assign 5 (.bin .add (.var 5) (.const 1)))))

/-- `out[j] := v4 >> 8 j` for `j < 8` -/
def store8 : Nat → Mach.BStmt
  | 0 => .store 1 (.const 0) (.var 4)
  | j + 1 => .seq (store8 j) (.store 1 (.const (BitVec.ofNat 64 (j + 1)))
      (.bin .lshr (.var 4) (.const (BitVec.ofNat 64 (8 * (j + 1))))))

/-- `v4 := 0; v5 := 0; while v5 < v1 { v6 := in[v5]; v4 := v4 + v6; v5 := v5 + 1 }; out[0..8) := v4` -/
def sumP : Mach.BStmt := .seq (.assign 4 (.const 0)) (.seq (.assign 5 (.const 0)) (.seq sumLoop (store8 7)))

theorem byteJ (w : BitVec 64) (j : Nat) (hj : j < 8) :
    (Op.eval .lshr w (BitVec.ofNat 64 (8 * j))).setWidth 8 = BitVec.ofNat 8 (w.toNat / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  have : 8 * j % 2 ^ 64 % 64 = 8 * j := by omega
  simp only [Op.eval, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, this,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem u8 (k : Nat) : (UInt8.ofNat (k % 256)).toBitVec = BitVec.ofNat 8 k := by
  apply BitVec.eq_of_toNat_eq; simp

theorem enc64 (w : BitVec 64) :
    (Proven.enc w).map (·.toBitVec) = (List.range 8).map fun j => BitVec.ofNat 8 (w.toNat / 256 ^ j) := by
  show (leN 8 w.toNat).map _ = _
  simp only [leN, List.range, List.range.loop, Nat.div_div_eq_div_mul, List.map, u8]
  simp

/-- the stores: the first `j + 1` output bytes are the bytes of `v4` -/
theorem store8_exec (w : BitVec 64) : ∀ (j : Nat), j < 8 → ∀ (σ : Mach.BState) (xs out : List (BitVec 8)),
    σ.heap = [xs, out] → σ.env 4 = w → 8 ≤ out.length → σ.env 3 = σ.env 3 →
    ∃ out', Mach.BExec (store8 j) σ ⟨σ.env, [xs, out'], σ.wheap⟩ ∧ out'.length = out.length ∧
      ∀ i (hi : i ≤ j), out'[i]? = some (BitVec.ofNat 8 (w.toNat / 256 ^ i))
  | 0, _, σ, xs, out, hh, h4, hl, _ => by
    refine ⟨out.set 0 (w.setWidth 8), ?_, by simp, fun i hi => ?_⟩
    · have := Mach.BExec.store (b := 1) (i := .const 0) (e := .var 4) (σ := σ) (by simp [hh])
        (by simp [hh, Mach.BExp.denote]; omega)
      simp only [hh, Mach.BExp.denote, h4] at this
      exact this
    · obtain rfl : i = 0 := by omega
      rw [List.getElem?_set_self (by omega)]; congr 1
      apply BitVec.eq_of_toNat_eq; simp
  | j + 1, hj, σ, xs, out, hh, h4, hl, _ => by
    obtain ⟨out₁, he, hl₁, hb⟩ := store8_exec w j (by omega) σ xs out hh h4 hl rfl
    refine ⟨out₁.set (j + 1) ((Op.eval .lshr w (BitVec.ofNat 64 (8 * (j + 1)))).setWidth 8), .seq he ?_,
      by simp [hl₁], fun i hi => ?_⟩
    · have := Mach.BExec.store (b := 1) (i := .const (BitVec.ofNat 64 (j + 1)))
        (e := .bin .lshr (.var 4) (.const (BitVec.ofNat 64 (8 * (j + 1))))) (σ := ⟨σ.env, [xs, out₁], σ.wheap⟩)
        (by simp) (by simp [Mach.BExp.denote]; omega)
      simp only [Mach.BExp.denote, h4] at this
      rw [show (BitVec.ofNat 64 (j + 1)).toNat = j + 1 by simp; omega] at this
      exact this
    · by_cases hij : i = j + 1
      · subst hij; rw [List.getElem?_set_self (by omega), byteJ w _ hj]
      · rw [List.getElem?_set_ne (Ne.symm hij)]; exact hb i (by omega)

def sumBytesU (xs : List UInt8) : BitVec 64 := xs.foldl (fun acc x => acc + x.toBitVec.setWidth 64) 0

theorem sumBytesU_eq (xs : List UInt8) : sumBytesU xs = sumBytes (xs.map (·.toBitVec)) := by
  unfold sumBytesU sumBytes; rw [List.foldl_map]

theorem sumP_exec (σ : Mach.BState) (xs out : List (BitVec 8)) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 64) (hl : 8 ≤ out.length) :
    ∃ σ' out', Mach.BExec sumP σ σ' ∧ σ'.heap = [xs, out'] ∧
      out'.take 8 = (List.range 8).map fun j => BitVec.ofNat 8 ((sumBytes xs).toNat / 256 ^ j) := by
  obtain ⟨σ₁, hlp, hq⟩ := BExec.loop_inv (c := .bin .ult (.var 5) (.var 1))
    (b := .seq (.load 6 0 (.var 5)) (.seq (.assign 4 (.bin .add (.var 4) (.var 6)))
      (.assign 5 (.bin .add (.var 5) (.const 1)))))
    (fun τ => τ.heap = [xs, out] ∧ τ.env 1 = BitVec.ofNat 64 xs.length ∧ (τ.env 5).toNat ≤ xs.length ∧
      τ.env 4 = sumBytes (xs.take (τ.env 5).toNat))
    (fun τ => τ.heap = [xs, out] ∧ τ.env 4 = sumBytes xs)
    (fun τ => xs.length - (τ.env 5).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨hh, h1, hle, hs⟩ hc => by
      dsimp only at hh h1 hle hs; subst hh
      simp only [Mach.BExp.denote, ult_ne, h1, toNat_ofNat_lt hn] at hc
      refine ⟨_, .seq (.load (by simp) (by simpa using hc)) (.seq .assign .assign), ?_⟩
      have e5 := toNat_inc hc hn
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [Mach.BEnv.set, Mach.BExp.denote, Op.eval]
      all_goals simp only [show (5 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 5 by decide,
        show (1 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 6 by decide, show (4 : Nat) ≠ 6 by decide,
        show (5 : Nat) ≠ 6 by decide, show (4 : Nat) ≠ 5 by decide, if_false, if_true]
      · exact h1
      · rw [e5]; omega
      · rw [e5, sumBytes_take_succ hc, hs]; rfl
      · rw [e5]; omega)
    (fun ⟨env, heap, wheap⟩ ⟨hh, h1, hle, hs⟩ hc => by
      dsimp only at hh h1 hle hs ⊢
      have : ¬ (env 5).toNat < xs.length := fun hlt =>
        (ult_ne (a := env 5) (b := env 1)).2 (by rw [h1, toNat_ofNat_lt hn]; exact hlt) hc
      refine ⟨hh, ?_⟩
      rw [hs, List.take_of_length_le (by omega)])
    ⟨(σ.env.set 4 0).set 5 0, σ.heap, σ.wheap⟩
    ⟨hh, by simpa [Mach.BEnv.set] using h1, by simp [Mach.BEnv.set], by simp [Mach.BEnv.set, sumBytes]⟩
  obtain ⟨out', hst, hl', hb⟩ := store8_exec (sumBytes xs) 7 (by omega) σ₁ xs out hq.1 hq.2 hl rfl
  refine ⟨_, out', .seq (BExec.assign' rfl) (.seq (BExec.assign' rfl) (.seq hlp hst)), rfl, ?_⟩
  apply List.ext_getElem? ; intro i
  by_cases hi : i < 8
  · rw [List.getElem?_take_of_lt hi, hb i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ## Machine theorems -/

theorem bzOK_iff {n : Nat} : rvF.bzOK n ↔ 2 * n < 2048 := Iff.rfl
theorem jmpOK_iff {n : Nat} : rvF.jmpOK n ↔ 0 < n ∧ 2 * n ≤ 2 ^ 19 := Iff.rfl

def takeCode1 (k : Nat) : List (BitVec 32) :=
  rvF.codeF (rvF.compBF 0 [0, 3] [2] (mapK (.const (BitVec.ofNat 64 k)) (.var 6)))
def incCode1 : List (BitVec 32) := rvF.codeF (rvF.compBF 0 [0, 3] [2] (mapK (.var 1) (.bin .add (.var 6) (.const 1))))
def sumCode1 : List (BitVec 32) := rvF.codeF (rvF.compBF 0 [0, 3] [2] sumP)

theorem take_wf (k : Nat) : rvF.wfB 0 [0, 3] [2] (mapK (.const (BitVec.ofNat 64 k)) (.var 6)) := by
  simp [mapK, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, bzOK_iff, jmpOK_iff]
  decide +kernel

theorem inc_wf : rvF.wfB 0 [0, 3] [2] (mapK (.var 1) (.bin .add (.var 6) (.const 1))) := by
  simp [mapK, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, bzOK_iff, jmpOK_iff]
  decide +kernel

theorem sum_wf : rvF.wfB 0 [0, 3] [2] sumP := by
  simp [sumP, sumLoop, store8, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, bzOK_iff, jmpOK_iff]
  decide +kernel

/-- **`List.take k`** in `Implements1` form: 15 bytes of work space (the frame cell saving `gp`, plus
alignment). -/
theorem take_implements1 (k : Nat) (hk : k < 2 ^ 64) :
    Implements1Raw (takeCode1 k) (fun xs => xs.take k) (fun _ => 15) := by
  refine implements1_of_exec encRaw encRaw _ 0 (by omega) _ (take_wf k) (fun _ => 0) _ (fun n => by dsimp only; omega) _ ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hK : (Mach.BExp.denote env (.const (BitVec.ofNat 64 k))).toNat = k := by
    simp [Mach.BExp.denote]; omega
  obtain ⟨σ', hex, hh⟩ := mapK_exec (.const (BitVec.ofNat 64 k)) (.var 6) id
    (fun env x he => by simp [Mach.BExp.denote, he, setWidth_setWidth8]) ⟨env, [a.map (·.toBitVec), out], [tbl]⟩
    (a.map (·.toBitVec)) out rfl (by simpa [encRaw] using h1) (by simp [encRaw] at hlt ⊢; omega)
    (by rw [hK]; simp [encRaw] at hout ⊢; omega)
  refine ⟨σ', _, hex, hh, ?_⟩
  rw [hK]
  simp only [encRaw, List.map_id]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), List.map_take]

/-- **`List.map (· + 1)`** in `Implements1` form -/
theorem inc_implements1 : Implements1Raw incCode1 (List.map (· + 1)) (fun _ => 15) := by
  refine implements1_of_exec encRaw encRaw _ 0 (by omega) _ inc_wf (fun _ => 0) _ (fun n => by dsimp only; omega) _ ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw] at h1 hlt hout ⊢
  have hK : (Mach.BExp.denote env (.var 1)).toNat = a.length := by
    simp only [Mach.BExp.denote, h1, BitVec.toNat_ofNat]; omega
  obtain ⟨σ', hex, hh⟩ := mapK_exec (.var 1) (.bin .add (.var 6) (.const 1)) (· + 1)
    (fun env x he => by simp only [Mach.BExp.denote, Op.eval, he]; exact Proven.setWidth_inc x)
    ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ (a.map (·.toBitVec)) out rfl (by simpa using h1) (by simp; omega)
    (by rw [hK]; simp at hout ⊢; omega)
  refine ⟨σ', _, hex, hh, ?_⟩
  rw [hK]
  simp only [List.length_map] at hout ⊢
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    List.take_of_length_le (by simp), List.map_map, List.map_map]
  apply List.map_congr_left; intro u _; simp

theorem length_enc64 (w : BitVec 64) : (Proven.enc w).length = 8 := leN_length 8 w.toNat

/-- **The byte sum** (a 64-bit word, `enc` = 8 little-endian bytes) in `Implements1` form -/
theorem sum_implements1 : Implements1With encRaw Proven.enc sumCode1 sumBytesU (fun _ => 15) := by
  refine implements1_of_exec encRaw Proven.enc _ 0 (by omega) _ sum_wf (fun _ => 0) _ (fun n => by dsimp only; omega) _ ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw, length_enc64] at h1 hlt hout ⊢
  obtain ⟨σ', out', hex, hh, ht⟩ := sumP_exec ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ (a.map (·.toBitVec)) out rfl
    (by simpa using h1) (by simp; omega) hout
  exact ⟨σ', out', hex, hh, by rw [ht, enc64, sumBytesU_eq]⟩

end Proven.Mach.Riscv

namespace Proven

/-- **Insertion sort** in `Implements1` form: no work space (`space n = 0`) -/
theorem sortCode_implements1 : Implements1Raw sortCode (fun x => x.mergeSort leU) (fun _ => 0) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  simp only [List.length_mergeSort] at hol ⊢
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * sortCode.length⟩ : Region)], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d12 d14 d24
  dsimp only at d12 d14 d24 ri ro rc
  have hxl : (a.map (·.toBitVec)).length = a.length := by simp
  have hil' : input.len = a.length := hil
  have hol' : a.length ≤ output.len := hol
  have hR : RegOK [⟨input.base, (a.map (·.toBitVec)).length⟩, ⟨output.base, (a.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry sortCode.length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, (a.map (·.toBitVec)).length⟩ : Region), ⟨output.base, (a.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * sortCode.length⟩ r := by
    rw [hxl]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (sortCode_ok_m h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hcd
    (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x13.symm.trans h13) rfl) (by simpa [List.map_map, Function.comp_def] using hx)
    (bytesAt_hosted (fun i hi => hmapO i (by rw [hxl] at hi; omega)))) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro q hq
    apply p4 q
    intro r hr
    have a2 := hq output (by simp)
    simp only [List.mem_singleton] at hr; subst hr; dsimp only; rw [hxl]; omega

/-- **Merge sort** in `Implements1` form: `space n = n + 71` (an `n`-byte scratch block at the bottom of the
work block, the 64-byte frame below `sp` at its top, up to 7 bytes of alignment) -/
theorem msortCode_implements1 : Implements1Raw msortCode (fun x => x.mergeSort leU) (fun n => n + 71) := by
  intro a s entry ra input output work
  dsimp only [encRaw]
  intro hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx hil hol hws hwal hram hdis hmapO hmapW
  simp only [List.length_mergeSort] at hol ⊢
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * msortCode.length⟩ : Region)], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold disjoint at d12 d13 d14 d23 d24 d34
  dsimp only at d12 d13 d14 d23 d24 d34 ri ro rw' rc
  have hxl : (a.map (·.toBitVec)).length = a.length := by simp
  have hil' : input.len = a.length := hil
  have hol' : a.length ≤ output.len := hol
  have hws' : a.length + 71 ≤ work.len := hws
  have hsp : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 7 (getX s 2) = (work.base + work.len) / 8 * 8 - 64 := by unfold frameBase; rw [hspn]
  have hf : FrOK 7 (frameBase 7 (getX s 2)) := ⟨by rw [hfb]; omega, by rw [hfb]; omega, by rw [hfb]; omega, by decide⟩
  have hR : RegOK [⟨input.base, (a.map (·.toBitVec)).length⟩, ⟨work.base, (a.map (·.toBitVec)).length⟩,
      ⟨output.base, (a.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (unfold Region.inRAM; dsimp only; omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; omega
  have hok : codeOK entry msortCode.length := ⟨hal, rc.1, rc.2⟩
  have hfd : ∀ r ∈ [(⟨input.base, (a.map (·.toBitVec)).length⟩ : Region), ⟨work.base, (a.map (·.toBitVec)).length⟩,
      ⟨output.base, (a.map (·.toBitVec)).length⟩], disjoint ⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hcd : ∀ r ∈ [(⟨frameBase 7 (getX s 2), 8 * (7 + 1)⟩ : Region), ⟨input.base, (a.map (·.toBitVec)).length⟩,
      ⟨work.base, (a.map (·.toBitVec)).length⟩, ⟨output.base, (a.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * msortCode.length⟩ r := by
    rw [hxl, hfb]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold disjoint; dsimp only; omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (msortCode_ok_m h hpc (codeAt_of_codeBytes hok hcode) hok (by rw [hra']; omega) hR hf hfd hcd
    (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x12.symm.trans h12) rfl) (getX_of (h.x13.symm.trans h13) rfl)
    (by simpa [List.map_map, Function.comp_def] using hx)
    (bytesAt_hosted (fun i hi => hmapW i (by rw [hxl] at hi; omega)))
    (bytesAt_hosted (fun i hi => hmapO i (by rw [hxl] at hi; omega)))) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro q hq
    apply p4 q
    intro r hr
    have a2 := hq output (by simp); have a3 := hq work (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hxl, hfb] at hr
    rcases hr with rfl | rfl | rfl <;> (dsimp only; omega)

end Proven

/- T01 round 2: the atoms `li d v` and `addi d 0 imm` (J: `liT d v` / one `addi`; A64: `liL`, run by `n_li`). -/
import Nano.Run.NatA.Base
import Nano.Run.NatT.Li
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

private theorem srunN_run {K : LayW} {C : List J} {n : Nat} {a b : Nat × CallProbe.St} (h : SRunN K C n a b) :
    run C n a = some b := by
  induction h with
  | refl => simp [run]
  | head hS hs _ ih => simp [run, hs, ih]

theorem srunN_split {K : LayW} {C : List J} : ∀ (a : Nat) {b : Nat} {x z : Nat × CallProbe.St},
    SRunN K C (a + b) x z → ∃ y, SRunN K C a x y ∧ SRunN K C b y z
  | 0, b, x, z, h => ⟨x, .refl _, by simpa using h⟩
  | a + 1, b, x, z, h => by
    rw [show a + 1 + b = a + b + 1 by omega] at h
    cases h with
    | head hS hs hr =>
      obtain ⟨y, h1, h2⟩ := srunN_split a hr
      exact ⟨y, .head hS hs h1, h2⟩

private theorem wr_ly (s : CallProbe.St) (r : Nat) (v : UInt64) : (CallProbe.wr s r v).ly = s.ly := by
  unfold CallProbe.wr; split <;> rfl

/-- a run along `addi` / `slli` instructions advances the pc by one per step and keeps the link layout -/
private theorem run_adv {C : List J} : ∀ (j : Nat) {pc : Nat} {s : CallProbe.St} {l : List J}, At C pc l →
    (∀ x ∈ l, (∃ rd rs imm, x = .addi rd rs imm) ∨ ∃ rd rs sh, x = .slli rd rs sh) → j ≤ l.length →
    ∀ c, run C j (pc, s) = some c → c.1 = pc + j ∧ c.2.ly = s.ly := by
  intro j
  induction j with
  | zero => intro pc s l _ _ _ c h; simp [run] at h; subst h; simp
  | succ j ih =>
    intro pc s l hC hl hj c h
    cases l with
    | nil => simp at hj
    | cons a l' =>
      have h0 : C[pc]? = some a := by simpa using hC 0 (by simp)
      have hC' : At C (pc + 1) l' := fun i hi => by
        have := hC (i + 1) (by simp; omega)
        rw [show pc + 1 + i = pc + (i + 1) by omega]; simpa using this
      have hl' : ∀ x ∈ l', (∃ rd rs imm, x = .addi rd rs imm) ∨ ∃ rd rs sh, x = .slli rd rs sh :=
        fun x hx => hl x (by simp [hx])
      rcases hl a (by simp) with ⟨rd, rs, imm, rfl⟩ | ⟨rd, rs, sh, rfl⟩
      · simp only [run, step, h0, Option.bind_some] at h
        have := ih hC' hl' (by simp at hj; omega) c h
        exact ⟨by rw [this.1]; omega, by rw [this.2, wr_ly]⟩
      · simp only [run, step, h0, Option.bind_some] at h
        have := ih hC' hl' (by simp at hj; omega) c h
        exact ⟨by rw [this.1]; omega, by rw [this.2, wr_ly]⟩

private theorem liB_kind (d v : Nat) : ∀ k, ∀ x ∈ liB d v k,
    (∃ rd rs imm, x = .addi rd rs imm) ∨ ∃ rd rs sh, x = .slli rd rs sh := by
  intro k
  induction k with
  | zero => simp [liB]
  | succ k ih =>
    intro x hx
    simp only [liB, liJ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact ih x hx
    · right; exact ⟨_, _, _, rfl⟩
    · left; exact ⟨_, _, _, rfl⟩

private theorem liT_kind (d : Nat) (v : UInt64) : ∀ x ∈ liT d v,
    (∃ rd rs imm, x = .addi rd rs imm) ∨ ∃ rd rs sh, x = .slli rd rs sh := by
  intro x hx
  unfold liT at hx
  split at hx
  · simp at hx; left; exact ⟨_, _, _, hx⟩
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · left; exact ⟨_, _, _, rfl⟩
    · exact liB_kind d _ 8 x hx

private theorem liT_pos (d : Nat) (v : UInt64) : 1 ≤ (liT d v).length := by
  by_cases h : v.toNat < 2048
  · rw [liT_len_small d v h]; omega
  · rw [liT_len_big d v h]; omega

/-- **atom `li d v`** (J: `liT d v`, 1 or 17 steps; A64: `liL`, by `n_li`) -/
theorem asim_li (S : A64SemN M X W) {d : Nat} {val : UInt64} (hok : (NTm.li d val).ok = true) :
    ASim M X W (NTm.li d val) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨hd, hd0⟩, -⟩ := hok
  have hC : At C q (liT d val) := fun i hi => by simpa [NTm.j] using hJ i (by simpa [NTm.j] using hi)
  obtain ⟨s1, hr, hx, hm, hbb⟩ := li_run st hd0 hag.x0 hC
  have hpos := liT_pos d val
  have hkind := liT_kind d val
  by_cases hlt : n + 1 < (liT d val).length
  · have hr' := srunN_run hrun
    have := (run_adv (n + 1) hC hkind (by omega) z hr').1
    exact absurd this (hz (n + 1) (by omega) (by simpa [NTm.j] using hlt))
  · have hge : (liT d val).length ≤ n + 1 := by omega
    obtain ⟨y, h1, h2⟩ := srunN_split (liT d val).length (b := n + 1 - (liT d val).length)
      (by rw [show (liT d val).length + (n + 1 - (liT d val).length) = n + 1 by omega]; exact hrun)
    have hy : y = (q + (liT d val).length, s1) := by
      have := srunN_run h1
      rw [hr] at this; exact (Option.some.inj this).symm
    subst hy
    have hly := (run_adv (liT d val).length hC hkind (Nat.le_refl _) _ hr).2
    have es : s1 = CallProbe.wr st d val := by
      unfold CallProbe.wr; simp only [hd0, ite_false]
      cases s1; cases st; simp_all
    have hW : LiWords A h (armReg d) val (NTm.li d val).alen :=
      ⟨by simp [NTm.alen, NTm.a], fun i hi => by simpa [NTm.a] using hA i hi⟩
    obtain ⟨s', R, N⟩ := n_li S hM hB hW hd (by omega)
    refine ⟨(liT d val).length - 1, (q + (liT d val).length, s1), CallProbe.wr v d val, s', by omega, ?_, R, ?_, ?_, ?_, ?_, Or.inl rfl⟩
    · rw [show n - ((liT d val).length - 1) = n + 1 - (liT d val).length by omega]; exact h2
    · have : π (q + (liT d val).length) = h + (NTm.li d val).alen := hft
      show NMid X W K A s0 _ (π (q + (liT d val).length)) s'
      rw [this]; exact N
    · show Agree _ _ s1
      rw [es]
      exact (agree_wr hag d val).mono (fun r hr => Or.inl ⟨hr.1, by simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩)
    · exact hbb
    · exact hly

/-- **atom `addi d 0 imm`** (a constant): J one `addi`, A64 `liL` of the immediate -/
theorem asim_addi_z (S : A64SemN M X W) {d : Nat} {imm : Int} (hok : (NTm.addi d 0 imm).ok = true) :
    ASim M X W (NTm.addi d 0 imm) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨⟨⟨hd, hd0⟩, -⟩, -⟩, -⟩ := hok
  have c0 : C[q]? = some (.addi d 0 imm) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, -, -, h1, -⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have hx0 := hag.x0
  rw [hx0] at h1
  have h1 : 0 ≤ imm := by simpa using h1
  have hea : CallProbe.ea (st.x 0) imm = imm.toNat := by simp [CallProbe.ea, hx0]
  have hv : UInt64.ofNat imm.toNat = UInt64.ofInt imm := ofNat_imm h1
  have hW : LiWords A h (armReg d) (UInt64.ofInt imm) (NTm.addi d 0 imm).alen :=
    ⟨by simp [NTm.alen, NTm.a], fun i hi => by simpa [NTm.a] using hA i hi⟩
  obtain ⟨s', R, N⟩ := n_li S hM hB hW hd (by omega)
  refine ⟨0, _, CallProbe.wr v d (UInt64.ofInt imm), s', Nat.zero_le _, by simpa using hrest, R, ?_, ?_, ?_, ?_, Or.inl rfl⟩
  · have : π (q + 1) = h + (NTm.addi d 0 imm).alen := hft
    show NMid X W K A s0 _ (π (q + 1)) s'
    rw [this]; exact N
  · show Agree _ _ (CallProbe.wr st d (UInt64.ofNat (CallProbe.ea (st.x 0) imm)))
    rw [hea, hv]
    exact (agree_wr hag d _).mono (fun r hr => Or.inl ⟨hr.1, by simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩)
  · exact CallProbe.wr_b _ _ _
  · exact wr_ly _ _ _

end JT

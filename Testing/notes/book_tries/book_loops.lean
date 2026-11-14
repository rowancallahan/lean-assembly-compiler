import Riscv.Examples.LoopExamples
open LeanRV64D
namespace Proven
/-- book `times n k` (recursion on k) as tail recursion over 64-bit words -/
def timesDown (n k acc : BitVec 64) : BitVec 64 := if k = 0 then acc else timesDown n (k - 1) (acc + n)
termination_by k.toNat
decreasing_by exact sub_one_lt ‹_›

open Exp in
/-- `while a1 ≠ 0 do (a2 := a2 + a0; a1 := a1 - 1); a0 := a2` -/
def timesProg : Stmt :=
  .seq (.loop (var 1) (.seq (.assign 2 (bin .add (var 2) (var 0))) (.assign 1 (bin .sub (var 1) (const 1)))))
    (.assign 0 (var 2))

theorem timesProg_exec (σ : Env) : ∃ σ', Exec timesProg σ σ' ∧ σ' 0 = timesDown (σ 0) (σ 1) (σ 2) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv (c := .var 1)
    (b := .seq (.assign 2 (.bin .add (.var 2) (.var 0))) (.assign 1 (.bin .sub (.var 1) (.const 1))))
    (fun τ => τ 0 = σ 0 ∧ timesDown (τ 0) (τ 1) (τ 2) = timesDown (σ 0) (σ 1) (σ 2)) (fun τ => τ 2 = timesDown (σ 0) (σ 1) (σ 2))
    (fun τ => (τ 1).toNat)
    (fun τ hI hc => ⟨_, .seq .assign .assign, by
      simp only [Exp.denote] at hc
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [Env.set] using hI.1
      · rw [← hI.2, timesDown.eq_def (τ 0), if_neg hc]; simp [Env.set, Exp.denote, Op.eval]
      · simp [Env.set, Exp.denote, Op.eval]; exact sub_one_lt hc⟩)
    (fun τ hI hc => by
      simp only [Exp.denote] at hc
      rw [← hI.2, timesDown.eq_def, if_pos hc])
    σ ⟨rfl, rfl⟩
  exact ⟨_, .seq hl .assign, by simp [Env.set, Exp.denote, hq]⟩

/-- the 64-bit loop computes the product mod 2^64 (so the book's `times` while n*k < 2^64) -/
theorem timesDown_eq' : ∀ (m : Nat) (n k acc : BitVec 64), k.toNat = m → timesDown n k acc = acc + n * k := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n k acc h
    rw [timesDown.eq_def]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, ih (k - 1).toNat (by rw [← h]; exact sub_one_lt hk) n (k - 1) (acc + n) rfl]
      have h1 : n * k = n * (k - 1 + 1) := by rw [BitVec.sub_add_cancel]
      rw [h1, BitVec.mul_add, show n * (1 : BitVec 64) = n from by simp, BitVec.add_assoc, BitVec.add_comm n]

theorem timesDown_eq (n k acc : BitVec 64) : timesDown n k acc = acc + n * k := timesDown_eq' _ n k acc rfl

theorem timesProg_wf : timesProg.wf := by simp only [timesProg, Stmt.wf]; decide +kernel

theorem times_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF timesProg)) (hok : codeOK pc (compileF timesProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = timesDown (getX s 10) (getX s 11) (getX s 12) ∧ Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := timesProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok timesProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩
end Proven
namespace Proven
/-- book `div n k` (repeated subtraction) over 64-bit words; k = 0 returns q (the book's version needs k>0) -/
def divSub (n k q : BitVec 64) : BitVec 64 :=
  if k = 0 then q else if n < k then q else divSub (n - k) k (q + 1)
termination_by n.toNat
decreasing_by
  have hk : k.toNat ≠ 0 := fun e => ‹¬k = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  have := ‹¬n < k›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega

open Exp in
/-- a3 := n <u k; while (k ≠ 0 ∧ a3 = 0) do (n := n - k; q := q + 1; a3 := n <u k); a0 := q -/
def divProg : Stmt :=
  .seq (.assign 3 (bin .ult (var 0) (var 1)))
  (.seq (.loop (ite (var 1) (bin .xor (var 3) (const 1)) (const 0))
      (.seq (.assign 0 (bin .sub (var 0) (var 1)))
        (.seq (.assign 2 (bin .add (var 2) (const 1))) (.assign 3 (bin .ult (var 0) (var 1))))))
    (.assign 0 (var 2)))




theorem divProg_exec (σ : Env) : ∃ σ', Exec divProg σ σ' ∧ σ' 0 = divSub (σ 0) (σ 1) (σ 2) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv
    (c := Exp.ite (.var 1) (.bin .xor (.var 3) (.const 1)) (.const 0))
    (b := .seq (.assign 0 (.bin .sub (.var 0) (.var 1)))
        (.seq (.assign 2 (.bin .add (.var 2) (.const 1))) (.assign 3 (.bin .ult (.var 0) (.var 1)))))
    (fun τ => τ 3 = (if τ 0 < τ 1 then 1 else 0) ∧ divSub (τ 0) (τ 1) (τ 2) = divSub (σ 0) (σ 1) (σ 2))
    (fun τ => τ 2 = divSub (σ 0) (σ 1) (σ 2))
    (fun τ => (τ 0).toNat)
    (fun τ hI hc => ⟨_, .seq .assign (.seq .assign .assign), by
      simp only [Exp.denote] at hc
      by_cases h1 : τ 1 = 0
      · simp [h1] at hc
      by_cases hlt : τ 0 < τ 1
      · simp [h1, hI.1, hlt, Op.eval] at hc
      have hk : (τ 1).toNat ≠ 0 := fun e => h1 (BitVec.eq_of_toNat_eq (by simpa using e))
      have hn : ¬ (τ 0).toNat < (τ 1).toNat := fun e => hlt (by rw [BitVec.lt_def]; exact e)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [Env.set, Exp.denote, Op.eval]
      · rw [← hI.2, divSub.eq_def (τ 0), if_neg h1, if_neg hlt]
        simp [Env.set, Exp.denote, Op.eval]
      · simp [Env.set, Exp.denote, Op.eval, BitVec.toNat_sub]; omega⟩)
    (fun τ hI hc => by
      simp only [Exp.denote] at hc
      rw [← hI.2, divSub.eq_def]
      by_cases h1 : τ 1 = 0
      · simp [h1]
      · by_cases hlt : τ 0 < τ 1
        · simp [h1, hlt]
        · exact absurd (by simpa [hI.1, hlt, Op.eval] using hc) h1)
    (σ.set 3 (if σ 0 < σ 1 then 1 else 0)) ⟨by simp [Env.set], by simp [Env.set]⟩
  refine ⟨_, .seq .assign (.seq hl .assign), ?_⟩
  simp [Env.set, Exp.denote, hq]
end Proven
namespace Proven
/- three-way inputs: ORIGINAL book-style Nat definitions vs `compileF` code (RISC-V only: no AArch64 generator for loops) -/
def bplus (n : Nat) : Nat → Nat | 0 => n | k + 1 => bplus n k + 1
def btimes (n : Nat) : Nat → Nat | 0 => 0 | k + 1 => btimes n k + n   -- recursion on k, Nat.add for the step (book plus would recurse n deep)
partial def bdiv (n k : Nat) : Nat := if n < k then 0 else 1 + bdiv (n - k) k   -- ProgramsProofs/Div.lean (k > 0)
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)
def hexs (ws : List (BitVec 32)) : String := " ".intercalate (ws.map (hex ·.toNat))
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
#eval show IO Unit from do
  IO.println "case times_vs_book_times"
  IO.println s!"rv {hexs (compileF timesProg)}"
  let ks : List Nat := [0, 1, 2, 3, 7, 100, 255, 256, 299]
  for n in ([0, 1, 2, 3, 255, 2^32, 2^40 + 5, 2^64 / 300 - 1] ++ (List.range 40).map (fun i => rnd i 1 % (2^64 / 300)) : List Nat) do
    for k in (ks ++ (List.range 5).map (fun j => rnd n j % 300) : List Nat) do
      IO.println s!"t {hex n} {hex k} 0 {hex (rnd n k)} {hex (btimes n k)}"
  IO.println "case div_vs_book_div"
  IO.println s!"rv {hexs (compileF divProg)}"
  for n in ([0, 1, 2, 3, 255, 1000, 2^20] ++ (List.range 60).map (fun i => rnd i 2 % 2^20) : List Nat) do
    for k in ([1, 2, 3, 7, 255, 1000, 2^20 + 1] ++ (List.range 5).map (fun j => rnd n j % 5000 + 1) : List Nat) do
      if n / k ≤ 5000 then IO.println s!"t {hex n} {hex k} 0 {hex (rnd k n)} {hex (bdiv n k)}"
end Proven

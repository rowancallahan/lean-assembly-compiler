/- Compile-time constants emitted as data (round 1, feature A; NOTES section 36).

A 0-ary definition `c : β` whose encoding `encB c` the KERNEL computes (`decide +kernel` under a fixed heartbeat
budget) to a byte list `ys` of at most `capBytes` bytes is compiled as the straight-line program `dataB ys`: one byte
store per byte into the output block, then `a1 := |ys|`.  Its machine theorem is `data_implements1` (proved once
here, for every byte list), specialised per constant by the equation `encB c = ys` (the per-constant kernel check).

Nothing is folded with arguments: the input (any type, any encoding) is ignored.  A value the kernel does not
compute within the budget (well-founded recursion that does not reduce, a huge value) is rejected by the command
`frontx_const` (`ConstCmd.lean`), never compiled. -/
import Riscv.Back.Implements1
import Compiler.Ind

set_option linter.unusedVariables false

namespace Proven.Frontx.Const
open Proven Proven.Mach Proven.Mach.Riscv

/-- the output-size cap of a folded constant (bytes) -/
def capBytes : Nat := 4096

/-- stores of the bytes `bs` at output positions `i, i+1, …`, then `v1 := n` -/
def dataGo (n : Nat) : Nat → List UInt8 → Mach.BStmt
  | _, [] => .assign 1 (.const (BitVec.ofNat 64 n))
  | i, b :: bs => .seq (.store 1 (.const (BitVec.ofNat 64 i)) (.const (BitVec.ofNat 64 b.toNat))) (dataGo n (i + 1) bs)

/-- the program of a constant with encoding `ys` -/
def dataB (ys : List UInt8) : Mach.BStmt := dataGo ys.length 0 ys

theorem wf_dataGo (n : Nat) : ∀ (i : Nat) (bs : List UInt8), rvF.wfB 0 [0, 3] [2] (dataGo n i bs)
  | i, [] => by simp [dataGo, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]
  | i, b :: bs => by
    refine ⟨?_, wf_dataGo n (i + 1) bs⟩
    simp [MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]

theorem wf_dataB (ys : List UInt8) : rvF.wfB 0 [0, 3] [2] (dataB ys) := wf_dataGo _ _ _

theorem setWidth8_ofNat (b : UInt8) : (BitVec.ofNat 64 b.toNat).setWidth 8 = b.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- the run of `dataGo n i bs`: the output's bytes `i .. i + |bs| - 1` become `bs`, the rest stays, `v1 := n` -/
theorem exec_dataGo (n : Nat) (inp : List (BitVec 8)) (tbl : Mach.WHeap) :
    ∀ (bs : List UInt8) (i : Nat) (o : List (BitVec 8)) (env : Mach.BEnv), i + bs.length ≤ o.length → o.length < 2 ^ 32 →
      ∃ σ' o', Mach.BExec (dataGo n i bs) (⟨env, [inp, o], tbl⟩ : Mach.BState) σ' ∧ σ'.heap = [inp, o'] ∧ σ'.env 1 = BitVec.ofNat 64 n ∧
        o'.length = o.length ∧ ∀ j, o'[j]? = if i ≤ j ∧ j < i + bs.length then (bs[j - i]?).map (·.toBitVec) else o[j]?
  | [], i, o, env, h, h32 => by
    refine ⟨_, o, Mach.BExec.assign, rfl, by simp [Mach.BEnv.set, Mach.BExp.denote], rfl, fun j => ?_⟩
    simp only [List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | b :: bs, i, o, env, h, h32 => by
    simp only [List.length_cons] at h
    have hi : (BitVec.ofNat 64 i).toNat < o.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    have hst := @Mach.BExec.store 1 (.const (BitVec.ofNat 64 i)) (.const (BitVec.ofNat 64 b.toNat))
      (⟨env, [inp, o], tbl⟩ : Mach.BState) (by simp) (by simpa [Mach.BExp.denote] using hi)
    simp only [Mach.BExp.denote, List.getElem_cons_succ, List.getElem_cons_zero, setWidth8_ofNat] at hst
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hst
    obtain ⟨σ', o', hx, hh, he, hl, hg⟩ :=
      exec_dataGo n inp tbl bs (i + 1) (o.set i b.toBitVec) env (by simp; omega) (by simpa using h32)
    refine ⟨σ', o', Mach.BExec.seq hst hx, hh, he, by simpa using hl, fun j => ?_⟩
    rw [hg j]
    simp only [List.length_cons]
    by_cases hj : j = i
    · subst hj; rw [if_neg (by omega), List.getElem?_set_self (by omega), if_pos (by omega)]; simp
    · rw [List.getElem?_set_ne (Ne.symm hj)]
      by_cases hr : i + 1 ≤ j ∧ j < i + 1 + bs.length
      · rw [if_pos hr, if_pos (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
        rw [show i + 1 + k - i = k + 1 by omega, show i + 1 + k - (i + 1) = k by omega]
        simp
      · rw [if_neg hr, if_neg (by omega)]

/-- **A constant as data**: the code of `dataB ys` implements every constant function whose result encodes to
`ys` (any input encoding, work space 15 bytes, the result length in `a1`). -/
theorem data_implements1 {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (c : β) (ys : List UInt8)
    (hys : encB c = ys) (maxLen : Nat) (retLen : Bool) :
    Implements1With encA encB (rvF.codeF (rvF.compBF 0 [0, 3] [2] (dataB ys))) (fun _ => c) (fun _ => 15)
      maxLen retLen := by
  subst hys
  refine implements1_of_exec encA encB (fun _ => c) 0 (by omega) (dataB (encB c)) (wf_dataB _) (fun _ => 0)
    (fun _ => 15) (fun n => Nat.le_refl _) maxLen retLen ?_
  intro a out tbl env h1 h8 hmax h32 hout hout32 htbl
  obtain ⟨σ', o', hx, hh, he, hl, hg⟩ :=
    exec_dataGo (encB c).length ((encA a).map (·.toBitVec)) [tbl] (encB c) 0 out env (by simpa using hout) hout32
  refine ⟨σ', o', hx, hh, ?_, ?_, fun _ => he⟩
  · apply List.ext_getElem? ; intro j
    rw [List.getElem?_take, hg j]
    by_cases hj : j < (encB c).length
    · simp [hj]
    · simp [hj]
  · apply List.ext_getElem? ; intro j
    rw [List.getElem?_drop, List.getElem?_drop, hg]
    simp only [Nat.zero_le, true_and, Nat.zero_add]
    rw [if_neg (by simp)]


/-! ## A kernel-reducible form of the inductive byte format

`C.sb` (the bytes of a string) is defined by well-founded recursion, which the kernel does not reduce; `sbS` is the
same function by structural recursion, `encS` the byte format through it (`enc_eq_encS`).  A constant of a type
declared by `frontx_ind_type` is checked as `encS sh (emb c) = ys` by the kernel and turned into `enc` here. -/

open Proven.Mach.Ind in
def sbS : C → List UInt8
  | .z => []
  | .c _ x l _ => match l with
    | .z => []
    | .c .. => UInt8.ofNat x.toNat :: sbS l

open Proven.Mach.Ind in
def encS (sh : Shape) : C → List UInt8
  | .z => [255]
  | .c t x l r => UInt8.ofNat t :: (sh.getD t []).flatMap
      (encF x (encS sh l) (encS sh r) (leN 8 (sbS l).length ++ sbS l) (leN 8 (sbS r).length ++ sbS r))

open Proven.Mach.Ind in
theorem sb_eq_sbS : ∀ v : C, v.sb = sbS v
  | .z => by unfold C.sb; rfl
  | .c t x .z r => by unfold C.sb; rfl
  | .c t x (.c t' x' l' r') r => by
    unfold C.sb; rw [sbS, sb_eq_sbS (.c t' x' l' r')]

open Proven.Mach.Ind in
theorem enc_eq_encS (sh : Shape) : ∀ v : C, v.enc sh = encS sh v
  | .z => by rw [C.enc, encS]
  | .c t x l r => by
    rw [C.enc, encS, enc_eq_encS sh l, enc_eq_encS sh r, C.senc, C.senc, sb_eq_sbS l, sb_eq_sbS r]

open Proven.Mach.Ind in
theorem enc_of_encS {sh : Shape} {v : C} {ys : List UInt8} (h : encS sh v = ys) : v.enc sh = ys :=
  (enc_eq_encS sh v).trans h

/-! ## Encodings for result types without a `Bytes` instance -/

/-- a `Nat` constant as a 64-bit word (little-endian); the command proves the value is `< 2^64` -/
def encWord (n : Nat) : List UInt8 := Bytes.enc (BitVec.ofNat 64 n)

/-- an element of `Fin k` (`k ≤ 256`) as one byte -/
def encFin {k : Nat} (x : Fin k) : List UInt8 := [UInt8.ofNat x.val]

/-- the raw input (ignored by a constant) -/
def encIn (bs : List UInt8) : List UInt8 := bs

end Proven.Frontx.Const

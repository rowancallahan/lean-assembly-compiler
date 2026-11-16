/- Target operations under the relation: register operations, slot loads and stores, jumps, branches. -/
import Compiler.Ir.EmitRel

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem next_back (pc : BitVec 64) {q t : Nat} (h : t ≤ q) : next pc q - BitVec.ofNat 64 (4 * (q - t)) = next pc t := by
  rw [show q = t + (q - t) by omega, ← next_add, Nat.add_sub_cancel_left, next_jmp]

theorem tgt_fwd (pc : BitVec 64) {q t : Nat} (h : q ≤ t) : tgt (next pc q) false (t - q) = next pc t := by
  simp only [tgt, Bool.false_eq_true, if_false]; rw [next_add]; congr 1; omega

theorem tgt_back (pc : BitVec 64) {q t : Nat} (h : t ≤ q) : tgt (next pc q) true (q - t) = next pc t := by
  simp only [tgt, if_true]; exact next_back pc h

theorem Target.len_brO (T : Target) (c : Cond) (a : Reg) (b : Option Reg) (k : Bool) (n : Nat) :
    (T.encO (.w (.br c a b k n))).length = T.lenBr := T.len_br c a b k n

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- a register operation (`d` a scratch or argument register) -/
theorem reg_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {o : EOp} {rest : List (BitVec 32)} {d : Reg}
    {v : BitVec 64} (hA : C.AtQ s q) (hR : C.MR m regs s) (hin : InW C.W q (T.encO o ++ rest)) (hd : d.val < 10)
    (law : T.At s (next C.pc0 q) (T.encO o) → T.runsTo s fun s' =>
      T.Done s s' (next (next C.pc0 q) (T.encO o).length) ∧ T.Set1 s s' d v ∧ T.mem s' = T.mem s) :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO o).length) ∧ C.MR m regs s' ∧ T.Set1 s s' d v :=
  T.toCore.runsTo_mono (C.op hA hin fun hA' => T.toCore.runsTo_mono (law hA') fun _ ⟨d', st, hm⟩ => ⟨d', hm, st⟩)
    fun _ ⟨hA', hk, hm, st⟩ => ⟨hA', hR.Set1 hA'.1 hk hm st hd, st⟩

theorem ldS_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Reg} {j : Nat}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hin : InW C.W q (T.encO (.w (.ldS d j)) ++ rest)) (hd : d.val < 10)
    (hj : j < C.nS) :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO (.w (.ldS d j))).length) ∧ C.MR m regs s' ∧
      T.Set1 s s' d (C.repr m.blks (regs j)) := by
  obtain ⟨e, hr, hal, -, -⟩ := hR.slot hj
  exact C.reg_ok hA hR hin hd fun hA' => T.w_ldS (Nat.lt_of_lt_of_le hj hR.nsl) hA' (by rw [e]; exact hr)
    (by rw [e]; exact hal) (by rw [e]; exact hR.slots j hj)

theorem ldArg_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Reg}
    {a : Arg Nat} (hA : C.AtQ s q) (hR : C.MR m regs s) (hin : InW C.W q (T.encO (ldArg d a) ++ rest))
    (hd : d.val < 10) (ha : okA C.nS a = true) :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO (ldArg d a)).length) ∧ C.MR m regs s' ∧
      T.Set1 s s' d (C.repr m.blks (a.eval regs)) := by
  cases a with
  | r x => exact C.ldS_ok hA hR hin hd (by simpa [okA] using ha)
  | i c => exact C.reg_ok hA hR hin hd fun hA' => T.w_li hA'

/-- a store to slot `d` -/
theorem stS_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Nat} {r : Reg}
    {v : Val} (hA : C.AtQ s q) (hR : C.MR m regs s) (hin : InW C.W q (T.encO (.w (.stS d r)) ++ rest))
    (hd : d < C.nS) (hr : T.get s r = C.repr m.blks v) (hv : Valid m.blks v) :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO (.w (.stS d r))).length) ∧ C.MR m (upd regs d v) s' ∧
      T.Same s s' := by
  obtain ⟨e, hram, hal, hcap, htop⟩ := hR.slot hd
  have hF := hR.F0_lt
  refine T.toCore.runsTo_mono (C.opW hA hin (fun hA' => T.w_stS (Nat.lt_of_lt_of_le hd hR.nsl) hA'
      (by rw [e]; exact hram) (by rw [e]; exact hal)
      (fun i hi => C.wr _ _ (.inr ⟨by rw [e]; omega, by rw [e]; omega⟩)))
    (fun s' ⟨_, hm⟩ => unch_work hA.2.2 hm (by rw [e]; omega) (by rw [e, length_le8]; omega))) ?_
  rintro s' ⟨hA', hk, hs, hm⟩
  exact ⟨hA', hR.stS hd hA'.1 hk hs (by rw [hm, e, hr]) hv, hs⟩

/-- one jump -/
theorem jW_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q t : Nat} {o : EOp} {rest : List (BitVec 32)}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hj : T.jW q t = some o) (hin : InW C.W q (T.encO o ++ rest)) :
    T.runsTo s fun s' => C.AtQ s' t ∧ C.MR m regs s' ∧ T.Same s s' := by
  unfold Target.jW at hj
  have hAt := C.at_of hA hin.left
  split at hj
  · next hqt =>
    split at hj
    · next hok =>
      cases hj
      refine T.toCore.runsTo_mono (T.w_jmp hok hAt) fun s' ⟨d, hs, hm⟩ => ?_
      have hpc := d.hpc; rw [tgt_fwd _ hqt] at hpc
      exact ⟨⟨d.ok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2⟩, hR.Same d.ok d.keep hm hs, hs⟩
    · exact nomatch hj
  · next hqt =>
    split at hj
    · next hok =>
      cases hj
      refine T.toCore.runsTo_mono (T.w_jmp hok hAt) fun s' ⟨d, hs, hm⟩ => ?_
      have hpc := d.hpc; rw [tgt_back _ (by omega)] at hpc
      exact ⟨⟨d.ok, hpc, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2⟩, hR.Same d.ok d.keep hm hs, hs⟩
    · exact nomatch hj

/-- go to word `t`: fall through or jump -/
theorem jTo_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q t : Nat} {os : List EOp} {rest : List (BitVec 32)}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hj : T.jTo q t = some os) (hin : InW C.W q (T.words os ++ rest)) :
    T.runsTo s fun s' => C.AtQ s' t ∧ C.MR m regs s' := by
  unfold Target.jTo at hj
  split at hj
  · next e => cases hj; subst e; exact T.runsTo_of ⟨hA, hR⟩
  · cases h : T.jW q t with
    | none => rw [h] at hj; exact nomatch hj
    | some o =>
      rw [h] at hj; cases hj
      exact T.toCore.runsTo_mono (C.jW_ok hA hR h (by simpa [Target.words] using hin)) fun _ h => ⟨h.1, h.2.1⟩

/-- a compare-and-branch on `r0, r1` -/
theorem br_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {c : Cond} {k : Bool}
    {n : Nat} {a b : Reg} (hA : C.AtQ s q) (hR : C.MR m regs s)
    (hin : InW C.W q (T.encO (.w (.br c a (some b) k n)) ++ rest)) (hb : T.brOK k n = true) (hk : k = true → n ≤ q) :
    T.runsTo s fun s' => C.MR m regs s' ∧ T.Same s s' ∧
      (c.eval (T.get s a) (T.get s b) = true → C.AtQ s' (if k then q - n else q + n)) ∧
      (c.eval (T.get s a) (T.get s b) = false → C.AtQ s' (q + T.lenBr)) := by
  refine T.toCore.runsTo_mono (T.w_br hb (C.at_of hA hin.left)) fun s' ⟨d, hs, hm⟩ => ?_
  have hU : C.Unch s' := fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2
  refine ⟨hR.Same d.ok d.keep hm hs, hs, fun ht => ⟨d.ok, ?_, hU⟩, fun hf => ⟨d.ok, ?_, hU⟩⟩
  · have hpc := d.hpc
    simp only [Base.getO] at hpc
    rw [if_pos ht] at hpc
    cases k
    · have := tgt_fwd C.pc0 (q := q) (t := q + n) (Nat.le_add_right q n)
      rw [show q + n - q = n by omega] at this
      rw [this] at hpc; simpa using hpc
    · have := tgt_back C.pc0 (q := q) (t := q - n) (by omega)
      rw [show q - (q - n) = n by have := hk rfl; omega] at this
      rw [this] at hpc; simpa using hpc
  · have hpc := d.hpc
    simp only [Base.getO] at hpc
    rw [if_neg (by rw [hf]; decide), next_add] at hpc
    exact hpc

theorem jW_len {q t : Nat} {o : EOp} (hj : T.jW q t = some o) : (T.encO o).length = T.lenJ := by
  unfold Target.jW at hj
  split at hj <;> split at hj <;> cases hj <;> exact T.len_j _ _

/-- a conditional branch to word `t`, short or long -/
theorem brTo_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q t : Nat} {c : Cond} {os : List EOp}
    {rest : List (BitVec 32)} (hA : C.AtQ s q) (hR : C.MR m regs s) (hb : T.brTo c q t = some os)
    (hin : InW C.W q (T.words os ++ rest)) :
    T.runsTo s fun s' => C.MR m regs s' ∧ T.Same s s' ∧
      (c.eval (T.get s R0) (T.get s R1) = true → C.AtQ s' t) ∧
      (c.eval (T.get s R0) (T.get s R1) = false → C.AtQ s' (q + T.len os)) := by
  unfold Target.brTo at hb
  by_cases hok : T.brOK (decide (t < q)) (if t < q then q - t else t - q) = true
  · rw [if_pos hok] at hb
    cases hb
    refine T.toCore.runsTo_mono (C.br_ok (c := c) (a := R0) (b := R1) hA hR (by simpa [Target.words] using hin) hok
      (fun h => by split <;> simp_all <;> omega)) fun s' ⟨hR', hs', ht, hf⟩ => ⟨hR', hs', fun e => ?_, fun e => ?_⟩
    · have := ht e
      by_cases h : t < q
      · simp only [h, decide_true, if_true] at this; rwa [show q - (q - t) = t by omega] at this
      · simp only [h, decide_false, Bool.false_eq_true, if_false] at this; rwa [show q + (t - q) = t by omega] at this
    · have := hf e
      simp only [Target.len, Target.words, List.append_nil, T.len_brO]; exact this
  · rw [if_neg hok] at hb
    split at hb
    · next hok =>
      cases hj : T.jW (q + T.lenBr) t with
      | none => rw [hj] at hb; exact nomatch hb
      | some j =>
        rw [hj] at hb; cases hb
        have hin' : InW C.W q (T.encO (.w (.br c.neg R0 (some R1) false (T.lenBr + T.lenJ))) ++
            (T.encO j ++ rest)) := by simpa [Target.words, List.append_assoc] using hin
        refine T.toCore.runsTo_trans (C.br_ok (a := R0) (b := R1) hA hR hin' hok (fun h => nomatch h)) fun s₁ ⟨hR₁, hs₁, ht, hf⟩ => ?_
        have e0 : T.get s₁ R0 = T.get s R0 := hs₁ R0
        have e1 : T.get s₁ R1 = T.get s R1 := hs₁ R1
        have hlen : T.len [.w (.br c.neg R0 (some R1) false (T.lenBr + T.lenJ)), j] = T.lenBr + T.lenJ := by
          simp only [Target.len, Target.words, List.append_nil, List.length_append, T.len_brO, jW_len hj]
        cases hc : c.eval (T.get s R0) (T.get s R1)
        · have hA₁ := ht (by rw [Cond.eval_neg, hc]; rfl)
          refine T.runsTo_of ⟨hR₁, hs₁, fun e => absurd e (by decide), fun _ => ?_⟩
          simp only [if_false, Bool.false_eq_true] at hA₁; rw [hlen]; exact hA₁
        · have hA₁ := hf (by rw [Cond.eval_neg, hc]; rfl)
          have hin₂ := hin'.right
          rw [T.len_brO] at hin₂
          exact T.toCore.runsTo_mono (C.jW_ok hA₁ hR₁ hj hin₂) fun s' ⟨hA', hR', hs'⟩ =>
            ⟨hR', fun r => by rw [hs' r, hs₁ r], fun _ => hA', fun e => absurd e (by decide)⟩
    · exact nomatch hb

end Ctx
end Proven.Ir

/- The memory instructions' code simulates them: `stb` (output byte), `ld` / `st` (cells). -/
import Legacy.Compiler.Ir.EmitInst

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- `byte k of the output := x` -/
theorem stb_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {p : Nat}
    {i v : Arg Nat} {k x : BitVec 64} (hA : C.AtQ s q) (hR : C.MR m regs s)
    (hp : p < C.nS) (hi : okA C.nS i = true) (hv : okA C.nS v = true) (hoff : T.offOK 0 = true)
    (hin : InW C.W q (T.words [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), ldArg R1 v,
      .w (.sb R1 R0 0)] ++ rest))
    (hx : v.word regs = some x) (hk : i.word regs = some k) (hpv : regs p = .p 1 0)
    (hO : (setOut m.out k.toNat (UInt8.ofBitVec (x.setWidth 8))).length ≤ C.outL) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), ldArg R1 v,
      .w (.sb R1 R0 0)]) ∧ C.MR { m with out := setOut m.out k.toNat (UInt8.ofBitVec (x.setWidth 8)) } regs s' := by
  refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin.cons (by decide) hp) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin.next.cons (by decide) hi) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin.next.next.cons (by decide) fun h => T.w_bin h)
    fun s3 ⟨hA3, hR3, st3⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA3 hR3 hin.next.next.next.cons (by decide) hv)
    fun s4 ⟨hA4, hR4, st4⟩ => ?_
  have hkl : k.toNat < C.outL := Nat.lt_of_lt_of_le (setOut_length_lt _ _ _) hO
  obtain ⟨ho1, ho2⟩ := C.outR; have hlt := T.ramHi_lt
  have hO' := C.dOW; unfold disjoint at hO'; dsimp only at hO'
  have e4 : (T.get s4 R0 + 0).toNat = C.outA + k.toNat := by
    rw [Core.Set1.other T.toCore st4 R0_ne_R1, Core.Set1.same T.toCore st3, Core.Set1.other T.toCore st2 R0_ne_R1,
      Core.Set1.same T.toCore st1, Core.Set1.same T.toCore st2, Arg.word_eval hk, hpv]
    show (Op.eval .add (BitVec.ofNat 64 (C.outA + 8 * 0)) k + BitVec.ofNat 64 0).toNat = _
    simp only [Op.eval]
    rw [bv_add_ofNat, bv_ofNat_add, ofNat_toNat' (by omega)]; omega
  have e1 : T.get s4 R1 = x := by
    rw [Core.Set1.same T.toCore st4, Arg.word_eval hx]; rfl
  refine T.toCore.runsTo_mono (C.opW hA4 hin.next.next.next.next.cons (fun h => T.w_sb hoff h
      (by rw [e4]; exact C.wr _ _ (.inl ⟨by omega, by omega⟩)))
    (fun s' ⟨_, hm⟩ x' h1 h2 => by
      rw [hm, e4]; unfold Proven.Mach.Mem.upd; rw [if_neg (by omega)]; exact hA4.2.2 x' h1 h2)) ?_
  rintro s5 ⟨hA5, hk5, hs5, hm5⟩
  refine ⟨hA5.congr ?_, hR4.stOut hO hA5.1 hk5 hs5 (by rw [hm5, e4, e1])⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

theorem cell_addr {m : Mem} {regs : Nat → Val} {s : T.S} (hR : C.MR m regs s) {kk a0 sz o k : Nat}
    (hbl : m.blks[kk]? = some (a0, sz, true)) (hlt : o + k < sz) :
    (BitVec.ofNat 64 (C.wb + 8 * (a0 + o)) + BitVec.ofNat 64 (8 * k)).toNat = C.wb + 8 * (a0 + o + k) ∧
      a0 + o + k < m.cells.length ∧ T.inRAM (C.wb + 8 * (a0 + o + k)) 8 ∧ (C.wb + 8 * (a0 + o + k)) % 8 = 0 ∧
      C.wb + 8 * (a0 + o + k) + 8 ≤ C.F0 := by
  have hb := (hR.mok.blks kk a0 sz true hbl).1
  have hcap := hR.cap; have hF := hR.F0_lt; obtain ⟨hw1, hw2⟩ := C.wR; have hal := C.wal
  have hlt' := T.ramHi_lt
  rw [bv_ofNat_add, ofNat_toNat' (by omega)]
  refine ⟨by omega, by omega, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- `d := cell k` -/
theorem ld_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d p k : Nat}
    {b o a0 sz : Nat} {v : Val} (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS) (hp : p < C.nS)
    (hoff : T.offOK (BitVec.ofNat 64 (8 * k)) = true)
    (hin : InW C.W q (T.words [.w (.ldS R0 p), .w (.ld R0 R0 (BitVec.ofNat 64 (8 * k))), .w (.stS d R0)] ++ rest))
    (hpv : regs p = .p b o) (hb : m.blk b = some (a0, sz)) (hlt : o + k < sz)
    (hc : m.cells[a0 + o + k]? = some (some v)) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.ldS R0 p), .w (.ld R0 R0 (BitVec.ofNat 64 (8 * k))),
      .w (.stS d R0)]) ∧ C.MR m (upd regs d v) s' := by
  obtain ⟨kk, rfl, hbl⟩ := blk_some hb
  refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin.cons (by decide) hp) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  obtain ⟨ea, -, hram, hal, -⟩ := cell_addr hR hbl hlt
  have e1 : T.get s1 R0 = BitVec.ofNat 64 (C.wb + 8 * (a0 + o)) := by
    rw [Core.Set1.same T.toCore st1, hpv, C.repr_blk hbl]
  rw [← e1] at ea
  refine T.toCore.runsTo_trans (C.reg_ok hA1 hR1 hin.next.cons (by decide) fun h => T.w_ld (v := C.repr m.blks v)
    hoff h (by rw [ea]; exact hram) (by rw [ea]; exact hal) (by rw [ea]; exact hR1.cells _ v hc))
    fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_mono (C.stS_ok hA2 hR2 hin.next.next.cons hd (Core.Set1.same T.toCore st2)
    (hR.mok.cv _ v hc)) fun s3 ⟨hA3, hR3, _⟩ => ⟨hA3.congr ?_, hR3⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

/-- `cell k := w` -/
theorem st_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {p k : Nat}
    {w : Arg Nat} {b o a0 sz : Nat} (hA : C.AtQ s q) (hR : C.MR m regs s) (hp : p < C.nS)
    (hw : okA C.nS w = true) (hoff : T.offOK (BitVec.ofNat 64 (8 * k)) = true)
    (hin : InW C.W q (T.words [.w (.ldS R0 p), ldArg R1 w, .w (.sd R1 R0 (BitVec.ofNat 64 (8 * k)))] ++ rest))
    (hpv : regs p = .p b o) (hb : m.blk b = some (a0, sz)) (hlt : o + k < sz) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.ldS R0 p), ldArg R1 w,
      .w (.sd R1 R0 (BitVec.ofNat 64 (8 * k)))]) ∧
      C.MR { m with cells := m.cells.set (a0 + o + k) (some (w.eval regs)) } regs s' := by
  obtain ⟨kk, rfl, hbl⟩ := blk_some hb
  refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin.cons (by decide) hp) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin.next.cons (by decide) hw) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  obtain ⟨ea, hg, hram, hal, htop⟩ := cell_addr hR hbl hlt
  have e2 : T.get s2 R0 = BitVec.ofNat 64 (C.wb + 8 * (a0 + o)) := by
    rw [Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1, hpv, C.repr_blk hbl]
  rw [← e2] at ea
  have hF := hR.F0_lt
  refine T.toCore.runsTo_mono (C.opW hA2 hin.next.next.cons (fun h => T.w_sd hoff h (by rw [ea]; exact hram)
      (by rw [ea]; exact hal) (fun i hi => by rw [ea]; exact C.wr _ _ (.inr ⟨by omega, by omega⟩)))
    (fun s' ⟨_, hm⟩ => unch_work hA2.2.2 hm (by rw [ea]; omega) (by rw [ea, length_le8]; omega))) ?_
  rintro s3 ⟨hA3, hk3, hs3, hm3⟩
  refine ⟨hA3.congr ?_, hR2.stCell hg hA3.1 hk3 hs3 (by rw [hm3, ea, Core.Set1.same T.toCore st2])
    (valid_eval hR.valid w)⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

end Ctx
end Proven.Ir

/- Each instruction's code simulates the instruction (`let_`, `ldb`, `stb`, `ld`, `st`; `alloc` in
`EmitAlloc.lean`). -/
import Legacy.Compiler.Ir.EmitOps

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem Arg.word_eval {regs : Nat → Val} {a : Arg Nat} {x : BitVec 64} (h : a.word regs = some x) :
    a.eval regs = .w x := by
  unfold Arg.word at h; split at h
  · next e => cases h; exact e
  · exact nomatch h

theorem valid_eval {bl : List (Nat × Nat × Bool)} {regs : Nat → Val} (hv : ∀ j, Valid bl (regs j)) :
    ∀ a : Arg Nat, Valid bl (a.eval regs)
  | .r x => hv x
  | .i _ => trivial

theorem bv_add_ofNat (A : Nat) (k : BitVec 64) : BitVec.ofNat 64 A + k = BitVec.ofNat 64 (A + k.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
theorem bv_ofNat_add (A B : Nat) : BitVec.ofNat 64 A + BitVec.ofNat 64 B = BitVec.ofNat 64 (A + B) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
theorem bv_shl3 (k : BitVec 64) : Op.eval .shl k 3 = BitVec.ofNat 64 (8 * k.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [Op.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
theorem bv_lshr3 (X : Nat) (h : X < 2 ^ 64) : Op.eval .lshr (BitVec.ofNat 64 X) 3 = BitVec.ofNat 64 (X / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [Op.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h]
  omega
theorem bv_sub (A B : Nat) (h : B ≤ A) (hA : A < 2 ^ 64) : Op.eval .sub (BitVec.ofNat 64 A) (BitVec.ofNat 64 B) = BitVec.ofNat 64 (A - B) := by
  apply BitVec.eq_of_toNat_eq
  simp [Op.eval, BitVec.toNat_sub, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show B < 2^64 by omega)]
  omega

theorem blk_some {m : Mem} {b a0 sz : Nat} (h : m.blk b = some (a0, sz)) :
    ∃ k, b = k + 2 ∧ m.blks[k]? = some (a0, sz, true) := by
  match b, h with
  | k + 2, h =>
    refine ⟨k, rfl, ?_⟩
    simp only [Mem.blk] at h
    split at h
    · next e => cases h; exact e
    · exact nomatch h

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem repr_blk {bl : List (Nat × Nat × Bool)} {k a0 sz o : Nat} (h : bl[k]? = some (a0, sz, true)) :
    C.repr bl (.p (k + 2) o) = BitVec.ofNat 64 (C.wb + 8 * (a0 + o)) := by
  simp only [repr, h]

theorem AtQ.congr {s : T.S} {a b : Nat} (h : C.AtQ s a) (e : a = b) : C.AtQ s b := e ▸ h

theorem R0_ne_R1 : R0 ≠ R1 := by decide

/-- `d := a` -/
theorem let_arg_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Nat}
    {a : Arg Nat} (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS) (ha : okA C.nS a = true)
    (hin : InW C.W q (T.words [ldArg R0 a, .w (.stS d R0)] ++ rest)) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [ldArg R0 a, .w (.stS d R0)]) ∧ C.MR m (upd regs d (a.eval regs)) s' := by
  refine T.toCore.runsTo_trans (C.ldArg_ok hA hR hin.cons (by decide) ha) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_mono (C.stS_ok hA1 hR1 hin.next.cons hd (Core.Set1.same T.toCore st1)
    (valid_eval hR.valid a)) fun s2 ⟨hA2, hR2, _⟩ => ⟨hA2.congr ?_, hR2⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

/-- `d := o a b` and `d := m a b` -/
theorem let_bin_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Nat}
    {a b : Arg Nat} {o : WOp} {f : BitVec 64 → BitVec 64 → BitVec 64} {x y : BitVec 64}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS) (ha : okA C.nS a = true) (hb : okA C.nS b = true)
    (hin : InW C.W q (T.words [ldArg R0 a, ldArg R1 b, .w o, .w (.stS d R0)] ++ rest))
    (hx : a.word regs = some x) (hy : b.word regs = some y)
    (law : ∀ {s : T.S} {pc : BitVec 64}, T.At s pc (T.wenc o) →
      T.runsTo s fun s' => T.Done s s' (next pc (T.wenc o).length) ∧
        T.Set1 s s' R0 (f (T.get s R0) (T.get s R1)) ∧ T.mem s' = T.mem s) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [ldArg R0 a, ldArg R1 b, .w o, .w (.stS d R0)]) ∧
      C.MR m (upd regs d (.w (f x y))) s' := by
  refine T.toCore.runsTo_trans (C.ldArg_ok hA hR hin.cons (by decide) ha) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin.next.cons (by decide) hb) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin.next.next.cons (by decide) fun h => law h)
    fun s3 ⟨hA3, hR3, st3⟩ => ?_
  have e3 : T.get s3 R0 = f x y := by
    rw [Core.Set1.same T.toCore st3, Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1, Core.Set1.same T.toCore st2,
      Arg.word_eval hx, Arg.word_eval hy]; rfl
  refine T.toCore.runsTo_mono (C.stS_ok (v := .w (f x y)) hA3 hR3 hin.next.next.next.cons hd e3 trivial)
    fun s4 ⟨hA4, hR4, _⟩ => ⟨hA4.congr ?_, hR4⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

/-- `d := p + i` (cells) -/
theorem padd_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d p : Nat}
    {i : Arg Nat} {b o a0 sz : Nat} {k : BitVec 64}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS) (hp : p < C.nS) (hi : okA C.nS i = true)
    (himm : T.immOK .shl 3 = true)
    (hin : InW C.W q (T.words [.w (.ldS R0 p), ldArg R1 i, .w (.bini .shl R1 R1 3), .w (.bin .add R0 R0 R1),
      .w (.stS d R0)] ++ rest))
    (hpv : regs p = .p b o) (hk : i.word regs = some k) (hb : m.blk b = some (a0, sz)) (hle : o + k.toNat ≤ sz) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.ldS R0 p), ldArg R1 i, .w (.bini .shl R1 R1 3),
      .w (.bin .add R0 R0 R1), .w (.stS d R0)]) ∧ C.MR m (upd regs d (.p b (o + k.toNat))) s' := by
  obtain ⟨kk, rfl, hbl⟩ := blk_some hb
  refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin.cons (by decide) hp) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin.next.cons (by decide) hi) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin.next.next.cons (by decide) fun h => T.w_bini himm h)
    fun s3 ⟨hA3, hR3, st3⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA3 hR3 hin.next.next.next.cons (by decide) fun h => T.w_bin h)
    fun s4 ⟨hA4, hR4, st4⟩ => ?_
  have e4 : T.get s4 R0 = C.repr m.blks (.p (kk + 2) (o + k.toNat)) := by
    rw [Core.Set1.same T.toCore st4, Core.Set1.same T.toCore st3, Core.Set1.other T.toCore st3 R0_ne_R1,
      Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1, Core.Set1.same T.toCore st2,
      Arg.word_eval hk, hpv, C.repr_blk hbl, C.repr_blk hbl]
    show BitVec.ofNat 64 (C.wb + 8 * (a0 + o)) + Op.eval .shl k 3 = _
    rw [bv_shl3, bv_ofNat_add]; congr 1; omega
  refine T.toCore.runsTo_mono (C.stS_ok hA4 hR4 hin.next.next.next.next.cons hd e4 ⟨a0, sz, hbl, hle⟩)
    fun s5 ⟨hA5, hR5, _⟩ => ⟨hA5.congr ?_, hR5⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

/-- the last two operations of `ldb`: the byte at `B + k` into slot `d` -/
theorem lbu_tail {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d : Nat}
    {B : Nat} {y : BitVec 8} (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS) (hoff : T.offOK 0 = true)
    (hin : InW C.W q (T.words [.w (.lbu R0 R0 0), .w (.stS d R0)] ++ rest))
    (h0 : T.get s R0 = BitVec.ofNat 64 B) (hB : B < 2 ^ 64) (hram : T.inRAM B 1) (hy : T.mem s B = some y) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.lbu R0 R0 0), .w (.stS d R0)]) ∧
      C.MR m (upd regs d (.w (y.setWidth 64))) s' := by
  have ea : (T.get s R0 + 0).toNat = B := by
    rw [h0, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, bv_ofNat_add, Nat.add_zero, ofNat_toNat' hB]
  refine T.toCore.runsTo_trans (C.reg_ok hA hR hin.cons (by decide) fun h => T.w_lbu (v := y) hoff h (by rw [ea]; exact hram)
    (by rw [ea]; exact hy)) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_mono (C.stS_ok (v := .w (y.setWidth 64)) hA1 hR1 hin.next.cons hd
    (Core.Set1.same T.toCore st1) trivial) fun s2 ⟨hA2, hR2, _⟩ => ⟨hA2.congr ?_, hR2⟩
  simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega

/-- `d := byte i` of the input or the output -/
theorem ldb_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q : Nat} {rest : List (BitVec 32)} {d p : Nat}
    {i : Arg Nat} {k : BitVec 64} {g' : Nat → Val} (hA : C.AtQ s q) (hR : C.MR m regs s) (hd : d < C.nS)
    (hp : p < C.nS) (hi : okA C.nS i = true) (hoff : T.offOK 0 = true)
    (hin : InW C.W q (T.words [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), .w (.lbu R0 R0 0),
      .w (.stS d R0)] ++ rest))
    (hk : i.word regs = some k)
    (hcase : (regs p = .p 0 0 ∧ ∃ b, m.inp[k.toNat]? = some b ∧ g' = upd regs d (.w (b.toBitVec.setWidth 64))) ∨
      (regs p = .p 1 0 ∧ ∃ b, m.out[k.toNat]? = some (some b) ∧ g' = upd regs d (.w (b.toBitVec.setWidth 64)))) :
    T.runsTo s fun s' => C.AtQ s' (q + T.len [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1),
      .w (.lbu R0 R0 0), .w (.stS d R0)]) ∧ C.MR m g' s' := by
  refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin.cons (by decide) hp) fun s1 ⟨hA1, hR1, st1⟩ => ?_
  refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin.next.cons (by decide) hi) fun s2 ⟨hA2, hR2, st2⟩ => ?_
  refine T.toCore.runsTo_trans (C.reg_ok hA2 hR2 hin.next.next.cons (by decide) fun h => T.w_bin h)
    fun s3 ⟨hA3, hR3, st3⟩ => ?_
  have hin3 := hin.next.next.next
  have e3 : ∀ B, C.repr m.blks (regs p) = BitVec.ofNat 64 B → T.get s3 R0 = BitVec.ofNat 64 (B + k.toNat) := by
    intro B hB
    rw [Core.Set1.same T.toCore st3, Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1,
      Core.Set1.same T.toCore st2, Arg.word_eval hk, hB]
    exact bv_add_ofNat _ _
  have hlt := T.ramHi_lt
  have hl : T.len [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), .w (.lbu R0 R0 0), .w (.stS d R0)] =
      (T.encO (.w (.ldS R0 p))).length + (T.encO (ldArg R1 i)).length + (T.encO (.w (.bin .add R0 R0 R1))).length +
        T.len [.w (.lbu R0 R0 0), .w (.stS d R0)] := by
    simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega
  rw [hl]
  rcases hcase with ⟨hpv, b, hb, rfl⟩ | ⟨hpv, b, hb, rfl⟩
  · have hkl : k.toNat < C.input.length := by
      rw [← hR.mok.inp]; exact (List.getElem?_eq_some_iff.1 hb).1
    have hin' := C.inR; have hlo := C.lo
    have hI := C.dIO; have hW := C.dIW; unfold disjoint at hI hW; dsimp only at hI hW
    have := lbu_tail (y := b.toBitVec) (B := C.inA + k.toNat) hA3 hR3 hd hoff hin3
      (e3 _ (by rw [hpv]; simp [repr])) (by have := hin'.2; omega) ⟨by have := hin'.1; omega, by have := hin'.2; omega⟩
      (by
        rw [hA3.2.2 _ (by omega) (by omega), C.inb _ hkl]
        rw [hR.mok.inp] at hb
        rw [List.getElem?_eq_getElem hkl] at hb; cases hb; rfl)
    simpa only [Nat.add_assoc] using this
  · have hkl : k.toNat < m.out.length := (List.getElem?_eq_some_iff.1 hb).1
    have ho := C.outR; have hlo := C.lo; have hoL := hR.outL
    have := lbu_tail (y := b.toBitVec) (B := C.outA + k.toNat) hA3 hR3 hd hoff hin3
      (e3 _ (by rw [hpv]; simp [repr])) (by have := ho.2; omega) ⟨by have := ho.1; omega, by have := ho.2; omega⟩
      (hR3.out _ _ hb)
    simpa only [Nat.add_assoc] using this

end Ctx
end Proven.Ir

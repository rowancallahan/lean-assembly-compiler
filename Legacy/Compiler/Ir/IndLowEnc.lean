/- The correctness of the inductive path's lowering to RTL, part 5: the encoder `enc` (`encF`) writes the byte format
`C.enc shO` of a value in memory to the output after the bytes written so far (strings: the count of the cells with a
child, then their bytes, `encStr`). -/
import Legacy.Compiler.Ir.IndLowDec

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

variable {P : Prog VReg}

theorem ex_let {g : VReg → Val} {m : Mem} (d : VReg) (e : Rhs VReg) {v : Val} (hv : e.eval m g = some v) :
    SC.Ex P (.i (.let_ d e)) g m (upd g d v) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, hv])

theorem u8_of (x : BitVec 64) : UInt8.ofBitVec (x.setWidth 8) = UInt8.ofNat x.toNat := by rw [x8]

theorem setOut_snoc (O : List UInt8) (b : UInt8) : setOut (O.map some) O.length b = (O ++ [b]).map some := by
  simp [setOut]

/-- `put`: one byte at the cursor -/
theorem ex_put {g : VReg → Val} {m : Mem} {v : Arg VReg} {x : BitVec 64} (hv : v.word g = some x) (O : List UInt8)
    (h0 : g 0 = .p 1 0) (h2 : g 2 = .w (BitVec.ofNat 64 O.length)) (hO : O.length < 2 ^ 60) (hm : m.out = O.map some) :
    SC.Ex P (put v) g m (upd g 2 (.w (BitVec.ofNat 64 (O ++ [UInt8.ofNat x.toNat]).length)))
      { m with out := (O ++ [UInt8.ofNat x.toNat]).map some } := by
  have x₁ : SC.Ex P (.i (.stb v 0 (.r 2))) g m g { m with out := (O ++ [UInt8.ofNat x.toNat]).map some } :=
    .i (e := []) (fun _ _ _ h => nomatch h) (by
      simp only [Inst.exec, hv, word_r h2, h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show O.length < 2 ^ 64 by omega), hm,
        setOut_snoc, u8_of])
  have x₂ := ex_addK (P := P) { m with out := (O ++ [UInt8.ofNat x.toNat]).map some } 2 2 1 h2
  rw [show (BitVec.ofNat 64 O.length + 1 : BitVec 64) = BitVec.ofNat 64 (O.length + 1) from ofNat_add _ 1] at x₂
  simpa [put] using SC.Ex.seq x₁ x₂

/-- the output so far: `O`, the cursor at its end -/
def OutAt (g : VReg → Val) (m : Mem) (O : List UInt8) : Prop :=
  g 0 = .p 1 0 ∧ g 2 = .w (BitVec.ofNat 64 O.length) ∧ m.out = O.map some

/-- one byte of `put8` -/
def p8Step (x t : VReg) (j : Nat) : SC :=
  .seq (.i (.let_ t (.op .lshr (.r x) (.i (BitVec.ofNat 64 (8 * j)))))) (put (.r t))

theorem put8_eq (x t : VReg) : put8 x t = .seqs ((List.range' 0 8).map (p8Step x t)) := by
  simp only [put8, List.range_eq_range']; rfl

theorem put8_loop {x t : VReg} (hx0 : x ≠ 0) (hx2 : x ≠ 2) (ht0 : t ≠ 0) (ht2 : t ≠ 2) (hxt : x ≠ t) (w : BitVec 64) :
    ∀ k j, j + k = 8 → ∀ (g : VReg → Val) (m : Mem) (O : List UInt8), g x = .w w → OutAt g m O →
      O.length + k < 2 ^ 60 →
      ∃ g', SC.Ex P (.seqs ((List.range' j k).map (p8Step x t))) g m g' { m with out := (O ++ (leN 8 w.toNat).drop j).map some } ∧
        OutAt g' { m with out := (O ++ (leN 8 w.toNat).drop j).map some } (O ++ (leN 8 w.toNat).drop j) ∧
        ∀ q : Nat, q ≠ 2 → q ≠ t → g' q = g q
  | 0, j, hj, g, m, O, hw, ⟨h0, h2, hm⟩, hO => by
    have : (leN 8 w.toNat).drop j = [] := List.drop_eq_nil_of_le (by rw [leN_length]; omega)
    rw [this, List.append_nil]
    have hm' : ({ m with out := O.map some } : Mem) = m := by rw [← hm]
    rw [hm']
    exact ⟨g, by simp only [List.range'_zero, List.map_nil, SC.seqs]; exact .nop, ⟨h0, h2, hm⟩, fun _ _ _ => rfl⟩
  | k + 1, j, hj, g, m, O, hw, ⟨h0, h2, hm⟩, hO => by
    have hjl : j < (leN 8 w.toNat).length := by rw [leN_length]; omega
    have hdrop : (leN 8 w.toNat).drop j = (leN 8 w.toNat)[j] :: (leN 8 w.toNat).drop (j + 1) :=
      List.drop_eq_getElem_cons hjl
    have hbyte : (leN 8 w.toNat)[j] = UInt8.ofNat (Op.eval .lshr w (BitVec.ofNat 64 (8 * j))).toNat := by
      have e1 := leN_get 8 w.toNat j (by omega)
      rw [List.getElem?_eq_getElem hjl] at e1
      have e2 := byte_eq w j (by omega)
      rw [Option.some.inj e1, ← u8_of, e2]
    have x₁ := ex_let (P := P) (g := g) (m := m) t (.op .lshr (.r x) (.i (BitVec.ofNat 64 (8 * j))))
      (v := .w (Op.eval .lshr w (BitVec.ofNat 64 (8 * j)))) (by simp [Rhs.eval, Arg.word, Arg.eval, hw])
    have x₂ := ex_put (P := P) (g := upd g t (.w (Op.eval .lshr w (BitVec.ofNat 64 (8 * j))))) (m := m) (v := .r t)
      (word_r (upd_same _ _ _)) O (by rw [upd_ne _ _ (Ne.symm ht0)]; exact h0) (by rw [upd_ne _ _ (Ne.symm ht2)]; exact h2)
      (by omega) hm
    rw [← hbyte] at x₂
    obtain ⟨g', x₃, hout, fr⟩ := put8_loop hx0 hx2 ht0 ht2 hxt w k (j + 1) (by omega)
      (upd (upd g t (.w (Op.eval .lshr w (BitVec.ofNat 64 (8 * j))))) 2 (.w (BitVec.ofNat 64 (O ++ [(leN 8 w.toNat)[j]]).length)))
      { m with out := (O ++ [(leN 8 w.toNat)[j]]).map some } (O ++ [(leN 8 w.toNat)[j]])
      (by rw [upd_ne _ _ (by omega), upd_ne _ _ hxt]; exact hw)
      ⟨by rw [upd_ne _ _ (by omega), upd_ne _ _ (Ne.symm ht0)]; exact h0, by rw [upd_same], rfl⟩
      (by simp; omega)
    have e : O ++ [(leN 8 w.toNat)[j]] ++ (leN 8 w.toNat).drop (j + 1) = O ++ (leN 8 w.toNat).drop j := by
      rw [hdrop, List.append_assoc, List.singleton_append]
    rw [e] at x₃ hout
    refine ⟨g', ?_, hout, fun q a b => by rw [fr q a b, upd_ne _ _ a, upd_ne _ _ b]⟩
    rw [List.range'_succ, List.map_cons]
    refine ex_seqs_cons (.seq x₁ x₂) ?_
    simpa using x₃

theorem put8_ok {x t : VReg} (hx0 : x ≠ 0) (hx2 : x ≠ 2) (ht0 : t ≠ 0) (ht2 : t ≠ 2) (hxt : x ≠ t) {w : BitVec 64}
    {g : VReg → Val} {m : Mem} {O : List UInt8} (hw : g x = .w w) (hO : OutAt g m O) (hl : O.length + 8 < 2 ^ 60) :
    ∃ g', SC.Ex P (put8 x t) g m g' { m with out := (O ++ leN 8 w.toNat).map some } ∧
      OutAt g' { m with out := (O ++ leN 8 w.toNat).map some } (O ++ leN 8 w.toNat) ∧
      ∀ q : Nat, q ≠ 2 → q ≠ t → g' q = g q := by
  rw [put8_eq]
  simpa using put8_loop (P := P) hx0 hx2 ht0 ht2 hxt w 8 0 rfl g m O hw hO hl

theorem Rv.z_inv {m : Mem} {v : Val} (h : Rv m v .z) : v = .w 0 := by cases h; rfl

theorem MLe.out (m : Mem) (o : List (Option UInt8)) : MLe m { m with out := o } := ⟨rfl, fun _ _ _ h => h, fun _ _ h => h⟩

/-- the count loop of `encStr` -/
def cntBody : SC := .seqs [addK 7 7 1, mov 8 9, nextL 9 8]

theorem cnt_loop : ∀ (w : C) (g : VReg → Val) (m : Mem) (cnt : Nat), Rv m (g 8) w → Rv m (g 9) w.lv →
    g 7 = .w (BitVec.ofNat 64 cnt) → cnt + w.sb.length < 2 ^ 60 →
    ∃ g', SC.Ex P (.loop (nz 9) cntBody) g m g' m ∧ g' 7 = .w (BitVec.ofNat 64 (cnt + w.sb.length)) ∧
      ∀ q : Nat, q ≠ 7 → q ≠ 8 → q ≠ 9 → g' q = g q
  | .z, g, m, cnt, h8, h9, h7, hc => by
    have := Rv.z_inv h9
    exact ⟨g, .loopF (by rw [nz_w this]; rfl), by simpa using h7, fun _ _ _ _ => rfl⟩
  | .c t x .z r, g, m, cnt, h8, h9, h7, hc => by
    have := Rv.z_inv h9
    exact ⟨g, .loopF (by rw [nz_w this]; rfl), by simpa using h7, fun _ _ _ _ => rfl⟩
  | .c t x (.c t' x' l' r') r, g, m, cnt, h8, h9, h7, hc => by
    obtain ⟨b, c0, vl, vr, hv, -⟩ := Rv.inv h9
    simp only [sb_cc, List.length_cons] at hc ⊢
    have x₁ := ex_addK (P := P) m 7 7 1 h7
    rw [show (BitVec.ofNat 64 cnt + 1 : BitVec 64) = BitVec.ofNat 64 (cnt + 1) from ofNat_add _ 1] at x₁
    have x₂ := ex_mov (P := P) (upd g 7 (.w (BitVec.ofNat 64 (cnt + 1)))) m 8 9
    have h8' : Rv m (upd (upd g 7 (.w (BitVec.ofNat 64 (cnt + 1)))) 8 (upd g 7 (.w (BitVec.ofNat 64 (cnt + 1))) 9) 8)
        (.c t' x' l' r') := by rw [upd_same, upd_ne _ _ (by decide)]; exact h9
    obtain ⟨w', x₃, -, -, h2, -⟩ := ex_fld (P := P) (d := 9) h8' 2 (by decide) 0
    obtain ⟨g', x₄, h7', fr⟩ := cnt_loop (.c t' x' l' r')
      (upd (upd (upd g 7 (.w (BitVec.ofNat 64 (cnt + 1)))) 8 (upd g 7 (.w (BitVec.ofNat 64 (cnt + 1))) 9)) 9 w') m (cnt + 1)
      (by rw [upd_ne _ _ (by decide)]; exact h8') (by rw [upd_same]; exact h2 rfl rfl)
      (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]) (by omega)
    refine ⟨g', .loopT (nz_p hv) (by simp only [cntBody, nextL, SC.seqs]; exact .seq x₁ (.seq x₂ x₃)) x₄, ?_,
      fun q a b c => by rw [fr q a b c, upd_ne _ _ c, upd_ne _ _ b, upd_ne _ _ a]⟩
    rw [h7']; congr 2; omega

/-- the bytes loop of `encStr` -/
def bytBody : SC := .seqs [.i (.ld 10 8 1), put (.r 10), mov 8 9, nextL 9 8]

theorem byt_loop : ∀ (w : C) (g : VReg → Val) (m : Mem) (O : List UInt8), Rv m (g 8) w → Rv m (g 9) w.lv →
    OutAt g m O → O.length + w.sb.length < 2 ^ 60 →
    ∃ g', SC.Ex P (.loop (nz 9) bytBody) g m g' { m with out := (O ++ w.sb).map some } ∧
      OutAt g' { m with out := (O ++ w.sb).map some } (O ++ w.sb) ∧
      ∀ q : Nat, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 10 → g' q = g q
  | .z, g, m, O, h8, h9, hO, hc => by
    have := Rv.z_inv h9
    have hm : ({ m with out := (O ++ C.sb .z).map some } : Mem) = m := by rw [sb_z, List.append_nil, ← hO.2.2]
    rw [hm]
    exact ⟨g, .loopF (by rw [nz_w this]; rfl), by simpa using hO, fun _ _ _ _ _ => rfl⟩
  | .c t x .z r, g, m, O, h8, h9, hO, hc => by
    have := Rv.z_inv h9
    have hm : ({ m with out := (O ++ C.sb (.c t x .z r)).map some } : Mem) = m := by
      rw [sb_cz, List.append_nil, ← hO.2.2]
    rw [hm]
    exact ⟨g, .loopF (by rw [nz_w this]; rfl), by simpa using hO, fun _ _ _ _ _ => rfl⟩
  | .c t x (.c t' x' l' r') r, g, m, O, h8, h9, hO, hc => by
    obtain ⟨b, c0, vl, vr, hv, -⟩ := Rv.inv h9
    obtain ⟨b8, c8, vl8, vr8, hv8, hb8, -, -, e1, -⟩ := Rv.inv h8
    obtain ⟨h0, h2, hm⟩ := hO
    simp only [sb_cc, List.length_cons] at hc ⊢
    have x₁ := ex_ld (P := P) (d := 10) hv8 hb8 (by decide) e1
    have x₂ := ex_put (P := P) (g := upd g 10 (.w x)) (m := m) (v := .r 10) (word_r (upd_same _ _ _)) O
      (by rw [upd_ne _ _ (by decide)]; exact h0) (by rw [upd_ne _ _ (by decide)]; exact h2) (by omega) hm
    generalize hg₂ : upd (upd g 10 (.w x)) 2 (.w (BitVec.ofNat 64 (O ++ [UInt8.ofNat x.toNat]).length)) = g₂ at x₂
    generalize hm₂ : ({ m with out := (O ++ [UInt8.ofNat x.toNat]).map some } : Mem) = m₂ at x₂
    have ml : MLe m m₂ := by rw [← hm₂]; exact MLe.out m _
    have x₃ := ex_mov (P := P) g₂ m₂ 8 9
    have h8' : Rv m₂ (upd g₂ 8 (g₂ 9) 8) (.c t' x' l' r') := by
      rw [upd_same, ← hg₂, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact h9.mono ml
    obtain ⟨w', x₄, -, -, h2', -⟩ := ex_fld (P := P) (d := 9) h8' 2 (by decide) 0
    obtain ⟨g', x₅, hout, fr⟩ := byt_loop (.c t' x' l' r') (upd (upd g₂ 8 (g₂ 9)) 9 w') m₂ (O ++ [UInt8.ofNat x.toNat])
      (by rw [upd_ne _ _ (by decide)]; exact h8') (by rw [upd_same]; exact h2' rfl rfl)
      ⟨by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), ← hg₂, upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
          exact h0,
        by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), ← hg₂, upd_same], by rw [← hm₂]⟩
      (by simp; omega)
    have e : O ++ [UInt8.ofNat x.toNat] ++ C.sb (.c t' x' l' r') = O ++ UInt8.ofNat x.toNat :: C.sb (.c t' x' l' r') := by
      simp
    have em : ({ m₂ with out := (O ++ [UInt8.ofNat x.toNat] ++ C.sb (.c t' x' l' r')).map some } : Mem) =
        { m with out := (O ++ UInt8.ofNat x.toNat :: C.sb (.c t' x' l' r')).map some } := by rw [← hm₂, e]
    rw [em] at x₅; rw [em, e] at hout
    refine ⟨g', .loopT (nz_p hv) (by simp only [bytBody, nextL, SC.seqs]; exact .seq x₁ (.seq x₂ (.seq x₃ x₄))) x₅,
      hout, fun q a b c d => ?_⟩
    rw [fr q a b c d, upd_ne _ _ c, upd_ne _ _ b, ← hg₂, upd_ne _ _ a, upd_ne _ _ d]

theorem toNat_small (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- **`encStr`**: a string's byte format -/
theorem encStr_ok {c : VReg} (hc0 : c ≠ 0) (hc2 : c ≠ 2) (hc7 : c ≠ 7) (hc8 : c ≠ 8) (hc9 : c ≠ 9) (hc10 : c ≠ 10)
    {v : C} {g : VReg → Val} {m : Mem} {O : List UInt8} (hv : Rv m (g c) v) (hO : OutAt g m O)
    (hl : O.length + v.senc.length < 2 ^ 60) :
    ∃ g', SC.Ex P (encStr c) g m g' { m with out := (O ++ v.senc).map some } ∧
      OutAt g' { m with out := (O ++ v.senc).map some } (O ++ v.senc) ∧
      ∀ q : Nat, q ≠ 2 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 10 → g' q = g q := by
  obtain ⟨h0, h2, hm⟩ := hO
  simp only [C.senc, List.length_append, leN_length] at hl
  have x₁ := ex_setK (P := P) g m 7 0
  have x₂ := ex_mov (P := P) (upd g 7 (.w 0)) m 8 c
  have r8 : Rv m (upd (upd g 7 (.w 0)) 8 (upd g 7 (.w 0) c) 8) v := by rw [upd_same, upd_ne _ _ hc7]; exact hv
  obtain ⟨w, x₃, -, -, hw, -⟩ := ex_fld (P := P) (d := 9) r8 2 (by decide) 0
  generalize hg₃ : upd (upd (upd g 7 (.w 0)) 8 (upd g 7 (.w 0) c)) 9 w = g₃ at x₃
  have e3 : ∀ q : Nat, q ≠ 7 → q ≠ 8 → q ≠ 9 → g₃ q = g q := fun q a b c' => by
    rw [← hg₃, upd_ne _ _ c', upd_ne _ _ b, upd_ne _ _ a]
  obtain ⟨g₄, x₄, h47, f₄⟩ := cnt_loop (P := P) v g₃ m 0 (by rw [← hg₃, upd_ne _ _ (by decide)]; exact r8)
    (by rw [← hg₃, upd_same]; exact hw rfl rfl)
    (by rw [← hg₃, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]; rfl)
    (by omega)
  simp only [Nat.zero_add] at h47
  obtain ⟨g₅, x₅, ⟨h50, h52, hm5⟩, f₅⟩ := put8_ok (P := P) (x := 7) (t := 10) (by decide) (by decide) (by decide)
    (by decide) (by decide) h47 (O := O) (m := m)
    ⟨by rw [f₄ 0 (by decide) (by decide) (by decide), e3 0 (by decide) (by decide) (by decide)]; exact h0,
      by rw [f₄ 2 (by decide) (by decide) (by decide), e3 2 (by decide) (by decide) (by decide)]; exact h2, hm⟩
    (by omega)
  rw [toNat_small _ (by omega)] at x₅ hm5 h52
  generalize hm₅ : ({ m with out := (O ++ leN 8 v.sb.length).map some } : Mem) = m₅ at x₅ hm5
  have ml : MLe m m₅ := by rw [← hm₅]; exact MLe.out m _
  have e5 : ∀ q : Nat, q ≠ 2 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 10 → g₅ q = g q := fun q a b c' d e => by
    rw [f₅ q a e, f₄ q b c' d, e3 q b c' d]
  have x₆ := ex_mov (P := P) g₅ m₅ 8 c
  have r8' : Rv m₅ (upd g₅ 8 (g₅ c) 8) v := by
    rw [upd_same, e5 c hc2 hc7 hc8 hc9 hc10]; exact hv.mono ml
  obtain ⟨w', x₇, -, -, hw', -⟩ := ex_fld (P := P) (d := 9) r8' 2 (by decide) 0
  obtain ⟨g₈, x₈, hout, f₈⟩ := byt_loop (P := P) v (upd (upd g₅ 8 (g₅ c)) 9 w') m₅ (O ++ leN 8 v.sb.length)
    (by rw [upd_ne _ _ (by decide)]; exact r8') (by rw [upd_same]; exact hw' rfl rfl)
    ⟨by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact h50,
      by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact h52, hm5⟩ (by simp [leN_length]; omega)
  have em : ({ m₅ with out := (O ++ leN 8 v.sb.length ++ v.sb).map some } : Mem) =
      { m with out := (O ++ (leN 8 v.sb.length ++ v.sb)).map some } := by rw [← hm₅, List.append_assoc]
  rw [em] at x₈; rw [em, List.append_assoc] at hout
  refine ⟨g₈, ?_, hout, fun q a b c' d e => ?_⟩
  · simp only [encStr, nextL, SC.seqs]
    exact .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ (.seq x₇ x₈))))))
  · rw [f₈ q a c' d e, upd_ne _ _ d, upd_ne _ _ c', e5 q a b c' d e]

/-- the registers of `enc` after some fields of the node `c t x l r`: output so far `O` -/
def EInv (x : BitVec 64) (l r : C) (g : VReg → Val) (mm : Mem) (O : List UInt8) : Prop :=
  OutAt g mm O ∧ g 4 = .w x ∧ Rv mm (g 5) l ∧ Rv mm (g 6) r

/-- `enc` writes the value `c` after `O` -/
def EncRet (P : Prog VReg) (sh : Shape) (mm : Mem) (v : Val) (O : List UInt8) (c : C) : Prop :=
  ∃ mm', Returns P 2 [.p 1 0, v, .w (BitVec.ofNat 64 O.length)] mm [.w (BitVec.ofNat 64 (O ++ c.enc sh).length)] mm' ∧
    MLe mm mm' ∧ mm'.out = (O ++ c.enc sh).map some

theorem leN_take1 (x : BitVec 64) : (leN 8 x.toNat).take 1 = [UInt8.ofNat x.toNat] := by
  simp only [leN, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
  apply UInt8.toNat.inj; simp

/-- **one field** of `enc` -/
theorem encFld_ok (sh : Shape) (x : BitVec 64) (l r : C) (f : Fld)
    (ihl : f = .l → ∀ v O mm, Rv mm v l → mm.out = O.map some → O.length + (l.enc sh).length < 2 ^ 60 →
      EncRet P sh mm v O l)
    (ihr : f = .r → ∀ v O mm, Rv mm v r → mm.out = O.map some → O.length + (r.enc sh).length < 2 ^ 60 →
      EncRet P sh mm v O r)
    (g : VReg → Val) (mm : Mem) (O : List UInt8) (hI : EInv x l r g mm O)
    (hc : O.length + (Ind.encF x (l.enc sh) (r.enc sh) l.senc r.senc f).length < 2 ^ 60) :
    ∃ g' mm', SC.Ex P (encFld f) g mm g' mm' ∧ MLe mm mm' ∧
      EInv x l r g' mm' (O ++ Ind.encF x (l.enc sh) (r.enc sh) l.senc r.senc f) := by
  obtain ⟨⟨h0, h2, hm⟩, h4, h5, h6⟩ := hI
  cases f with
  | x =>
    simp only [Ind.encF] at hc ⊢
    rw [leN_length] at hc
    obtain ⟨g', x₁, hout, fr⟩ := put8_ok (P := P) (x := 4) (t := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) h4 ⟨h0, h2, hm⟩ (by omega)
    refine ⟨g', _, x₁, MLe.out mm _, hout, by rw [fr 4 (by decide) (by decide)]; exact h4, ?_, ?_⟩
    · rw [fr 5 (by decide) (by decide)]; exact h5.mono (MLe.out mm _)
    · rw [fr 6 (by decide) (by decide)]; exact h6.mono (MLe.out mm _)
  | b =>
    simp only [Ind.encF, leN_take1] at hc ⊢
    have x₁ := ex_put (P := P) (v := .r 4) (word_r h4) O h0 h2 (by simp at hc; omega) hm
    refine ⟨_, _, x₁, MLe.out mm _, ⟨by rw [upd_ne _ _ (by decide)]; exact h0, by rw [upd_same], rfl⟩,
      by rw [upd_ne _ _ (by decide)]; exact h4, ?_, ?_⟩
    · rw [upd_ne _ _ (by decide)]; exact h5.mono (MLe.out mm _)
    · rw [upd_ne _ _ (by decide)]; exact h6.mono (MLe.out mm _)
  | l =>
    simp only [Ind.encF] at hc ⊢
    obtain ⟨mm', hret, ml, ho⟩ := ihl rfl (g 5) O mm h5 hm hc
    refine ⟨_, mm', .call (vs := [.w (BitVec.ofNat 64 (O ++ l.enc sh).length)]) (by
      simp only [List.map, Arg.eval, h0, h2]; exact hret) rfl, ml, ⟨?_, ?_, ho⟩, ?_, ?_, ?_⟩
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h0
    · rw [setMany_one, upd_same]
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h4
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h5.mono ml
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h6.mono ml
  | r =>
    simp only [Ind.encF] at hc ⊢
    obtain ⟨mm', hret, ml, ho⟩ := ihr rfl (g 6) O mm h6 hm hc
    refine ⟨_, mm', .call (vs := [.w (BitVec.ofNat 64 (O ++ r.enc sh).length)]) (by
      simp only [List.map, Arg.eval, h0, h2]; exact hret) rfl, ml, ⟨?_, ?_, ho⟩, ?_, ?_, ?_⟩
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h0
    · rw [setMany_one, upd_same]
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h4
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h5.mono ml
    · rw [setMany_one, upd_ne _ _ (by decide)]; exact h6.mono ml
  | sl =>
    simp only [Ind.encF] at hc ⊢
    obtain ⟨g', x₁, hout, fr⟩ := encStr_ok (P := P) (c := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h5 ⟨h0, h2, hm⟩ hc
    refine ⟨g', _, x₁, MLe.out mm _, hout, by rw [fr 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4,
      ?_, ?_⟩
    · rw [fr 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.mono (MLe.out mm _)
    · rw [fr 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6.mono (MLe.out mm _)
  | sr =>
    simp only [Ind.encF] at hc ⊢
    obtain ⟨g', x₁, hout, fr⟩ := encStr_ok (P := P) (c := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h6 ⟨h0, h2, hm⟩ hc
    refine ⟨g', _, x₁, MLe.out mm _, hout, by rw [fr 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4,
      ?_, ?_⟩
    · rw [fr 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5.mono (MLe.out mm _)
    · rw [fr 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6.mono (MLe.out mm _)

/-- **the fields** of `enc` -/
theorem encFlds_ok (sh : Shape) (x : BitVec 64) (l r : C) (fs : List Fld)
    (ihl : Fld.l ∈ fs → ∀ v O mm, Rv mm v l → mm.out = O.map some → O.length + (l.enc sh).length < 2 ^ 60 →
      EncRet P sh mm v O l)
    (ihr : Fld.r ∈ fs → ∀ v O mm, Rv mm v r → mm.out = O.map some → O.length + (r.enc sh).length < 2 ^ 60 →
      EncRet P sh mm v O r) :
    ∀ (fs₂ : List Fld) (g : VReg → Val) (mm : Mem) (O : List UInt8), (∀ f ∈ fs₂, f ∈ fs) → EInv x l r g mm O →
      O.length + (fs₂.flatMap (Ind.encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length < 2 ^ 60 →
      ∃ g' mm', SC.Ex P (SC.seqs (fs₂.map encFld)) g mm g' mm' ∧ MLe mm mm' ∧
        EInv x l r g' mm' (O ++ fs₂.flatMap (Ind.encF x (l.enc sh) (r.enc sh) l.senc r.senc))
  | [], g, mm, O, _, hI, _ => ⟨g, mm, .nop, MLe.refl mm, by simpa using hI⟩
  | f :: fs₂, g, mm, O, hs, hI, hc => by
    simp only [List.flatMap_cons, List.length_append] at hc ⊢
    have hf := hs f (by simp)
    obtain ⟨g₁, mm₁, x₁, ml₁, hI₁⟩ := encFld_ok (P := P) sh x l r f (fun e => ihl (e ▸ hf)) (fun e => ihr (e ▸ hf))
      g mm O hI (by omega)
    obtain ⟨g₂, mm₂, x₂, ml₂, hI₂⟩ := encFlds_ok sh x l r fs ihl ihr fs₂ g₁ mm₁ _ (fun f' h => hs f' (by simp [h])) hI₁
      (by simp only [List.length_append]; omega)
    refine ⟨g₂, mm₂, ex_seqs_cons x₁ x₂, ml₁.trans ml₂, ?_⟩
    simpa only [List.append_assoc] using hI₂

theorem encF_eq (sh : Shape) : encF sh = mkFunc [0, 1, 2] [0, 1, 2] (sh.length + 2)
    (rs3 (.ite (nz 1)
        (.seq (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)])
          (.term (.switch 3 ((List.range sh.length).map (· + 1)) (sh.length + 1))))
        (.seq (put (.i 255)) (.term (.ret [.r 2])))) sh
      (fun fs => .seq (SC.seqs (fs.map encFld)) (.term (.jmp (sh.length + 1) [])))
      (.term (.ret [.r 2]))) := rfl

theorem enc_args (v : Val) (n : Nat) :
    let g := (setMany (fun _ => Val.w 0) [0, 1, 2] [.p 1 0, v, .w (BitVec.ofNat 64 n)] : VReg → Val)
    g 0 = .p 1 0 ∧ g 1 = v ∧ g 2 = .w (BitVec.ofNat 64 n) := by simp [setMany, upd]

/-- **`enc`** writes a value's byte format -/
theorem enc_ok (sh : Shape) (hP : P.funcs[2]? = some (encF sh)) :
    ∀ (c : C) (v : Val) (O : List UInt8) (mm : Mem), Rv mm v c → mm.out = O.map some →
      O.length + (c.enc sh).length < 2 ^ 60 → EncRet P sh mm v O c := by
  intro c
  generalize hFF : encF sh = F at hP
  rw [encF_eq] at hFF
  have hFe : F.entry = 0 := by rw [← hFF]; rfl
  have hFp : F.params = [0, 1, 2] := by rw [← hFF]; rfl
  have ok0 := rs3_ok0 [0, 1, 2] (.ite (nz 1)
        (.seq (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)])
          (.term (.switch 3 ((List.range sh.length).map (· + 1)) (sh.length + 1))))
        (.seq (put (.i 255)) (.term (.ret [.r 2])))) sh
      (fun fs => .seq (SC.seqs (fs.map encFld)) (.term (.jmp (sh.length + 1) [])))
      (.term (.ret [.r 2]))
  have okE := rs3_okE [0, 1, 2] (.ite (nz 1)
        (.seq (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)])
          (.term (.switch 3 ((List.range sh.length).map (· + 1)) (sh.length + 1))))
        (.seq (put (.i 255)) (.term (.ret [.r 2])))) sh
      (fun fs => .seq (SC.seqs (fs.map encFld)) (.term (.jmp (sh.length + 1) [])))
      (.term (.ret [.r 2]))
  have okj := rs3_okj [0, 1, 2] (.ite (nz 1)
        (.seq (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)])
          (.term (.switch 3 ((List.range sh.length).map (· + 1)) (sh.length + 1))))
        (.seq (put (.i 255)) (.term (.ret [.r 2])))) sh
      (fun fs => .seq (SC.seqs (fs.map encFld)) (.term (.jmp (sh.length + 1) [])))
      (.term (.ret [.r 2]))
  rw [hFF] at ok0 okE okj
  obtain ⟨n0, ok0⟩ := ok0
  obtain ⟨nE, okE⟩ := okE
  obtain ⟨BE, hBE, hpE⟩ := ok_open_block (flatT_start _ _ okE)
  -- from an end at the entry's `ret`
  have fin : ∀ (g g' : VReg → Val) (mm mm' : Mem) (l' pc' : Nat) (B : Block VReg) (rvs : List (Arg VReg)),
      Reach P 2 0 0 g mm l' pc' g' mm' → F.blocks.lookup l' = some B → B.body[pc']? = none → B.term = .ret rvs →
      ∀ (v : Val) (n : Nat), g = setMany (fun _ => Val.w 0) [0, 1, 2] [.p 1 0, v, .w (BitVec.ofNat 64 n)] →
      ∀ res, rvs.map (Arg.eval g') = [res] →
      Returns P 2 [.p 1 0, v, .w (BitVec.ofNat 64 n)] mm [res] mm' := by
    intro g g' mm mm' l' pc' B rvs hR hB hk ht v n hg res hv
    exact ⟨F, hP, by rw [hFp]; rfl, l', pc', g', B, rvs, by rw [hFe, hFp, ← hg]; exact hR, hB, hk, ht, hv⟩
  induction c with
  | z =>
    intro v O mm hv hm hc
    have hv0 := Rv.z_inv hv; subst hv0
    obtain ⟨h0, h1, h2⟩ := enc_args (.w 0) O.length
    generalize hg : setMany (fun _ => Val.w 0) [0, 1, 2] [.p 1 0, .w 0, .w (BitVec.ofNat 64 O.length)] = g at h0 h1 h2
    unfold EncRet
    simp only [C.enc] at hc ⊢
    have x₁ := ex_put (P := P) (g := g) (m := mm) (v := .i 255) (x := 255) rfl O h0 h2 (by simp at hc; omega) hm
    have e := flatT_ok hP _ (.iteF (by rw [nz_w h1]; rfl) (.seq x₁ .ret)) _ ok0
    obtain ⟨l', pc', g', B, rvs, hR, hB, hk, ht, hv'⟩ := e
    refine ⟨_, fin g g' mm _ l' pc' B rvs hR hB hk ht _ _ hg.symm _ hv', MLe.out mm _, rfl⟩
  | c t x l r ihl ihr =>
    intro v O mm hv hm hc
    obtain ⟨bk, c0, vl, vr, hvp, hb, ht, e0, e1, e2, e3, rl, rr⟩ := Rv.inv hv
    obtain ⟨h0, h1, h2⟩ := enc_args v O.length
    generalize hg : setMany (fun _ => Val.w 0) [0, 1, 2] [.p 1 0, v, .w (BitVec.ofNat 64 O.length)] = g at h0 h1 h2
    rw [hvp] at h1
    unfold EncRet
    simp only [C.enc, List.length_cons] at hc ⊢
    -- loads and the tag byte
    have xl : SC.Ex P (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3)]) g mm
        (upd (upd (upd (upd g 3 (.w (BitVec.ofNat 64 t))) 4 (.w x)) 5 vl) 6 vr) mm := by
      simp only [SC.seqs]
      refine .seq (ex_ld h1 hb (by decide) (by simpa using e0)) (.seq (ex_ld ?_ hb (by decide) e1)
        (.seq (ex_ld ?_ hb (by decide) e2) (ex_ld ?_ hb (by decide) e3)))
      · rw [upd_ne _ _ (by decide)]; exact h1
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact h1
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact h1
    generalize hg₁ : upd (upd (upd (upd g 3 (.w (BitVec.ofNat 64 t))) 4 (.w x)) 5 vl) 6 vr = g₁ at xl
    have hg₁q : ∀ q : Nat, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → g₁ q = g q := fun q a b c d => by
      rw [← hg₁, upd_ne _ _ d, upd_ne _ _ c, upd_ne _ _ b, upd_ne _ _ a]
    have g3 : g₁ 3 = .w (BitVec.ofNat 64 t) := by
      rw [← hg₁, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]
    have g4 : g₁ 4 = .w x := by rw [← hg₁, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]
    have g5 : g₁ 5 = vl := by rw [← hg₁, upd_ne _ _ (by decide), upd_same]
    have g6 : g₁ 6 = vr := by rw [← hg₁, upd_same]
    have htn : (BitVec.ofNat 64 t).toNat = t := toNat_small t (by omega)
    have xp := ex_put (P := P) (g := g₁) (m := mm) (v := .r 3) (word_r g3) O
      (by rw [hg₁q 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
      (by rw [hg₁q 2 (by decide) (by decide) (by decide) (by decide)]; exact h2) (by omega) hm
    rw [htn] at xp
    generalize hg₂ : upd g₁ 2 (.w (BitVec.ofNat 64 (O ++ [UInt8.ofNat t]).length)) = g₂ at xp
    generalize hm₂ : ({ mm with out := (O ++ [UInt8.ofNat t]).map some } : Mem) = m₂ at xp
    have ml₂ : MLe mm m₂ := by rw [← hm₂]; exact MLe.out mm _
    have x₀ : SC.Ex P (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)]) g mm g₂ m₂ := by
      simp only [SC.seqs] at xl ⊢
      cases xl with
      | seq a r1 => cases r1 with
        | seq b r2 => cases r2 with
          | seq c d => exact .seq a (.seq b (.seq c (.seq d xp)))
    have g23 : g₂ 3 = .w (BitVec.ofNat 64 t) := by rw [← hg₂, upd_ne _ _ (by decide)]; exact g3
    have hI : EInv x l r g₂ m₂ (O ++ [UInt8.ofNat t]) :=
      ⟨⟨by rw [← hg₂, upd_ne _ _ (by decide), hg₁q 0 (by decide) (by decide) (by decide) (by decide)]; exact h0,
        by rw [← hg₂, upd_same], by rw [← hm₂]⟩,
        by rw [← hg₂, upd_ne _ _ (by decide)]; exact g4, by rw [← hg₂, upd_ne _ _ (by decide), g5]; exact rl.mono ml₂,
        by rw [← hg₂, upd_ne _ _ (by decide), g6]; exact rr.mono ml₂⟩
    by_cases hts : t < sh.length
    · obtain ⟨nj, okj⟩ := okj t hts
      obtain ⟨Bj, hBj, hpj⟩ := ok_open_block (flatT_start _ _ okj)
      have hL : ((List.range sh.length).map (· + 1))[(BitVec.ofNat 64 t).toNat]?.getD (sh.length + 1) = t + 1 := by
        rw [htn]; simp [hts]
      have e0 := flatT_ok hP _ (.iteT (nz_p h1) (.seq x₀ (.sw g23 (by rw [hL]; exact hBj) hpj))) _ ok0
      rw [hL] at e0
      have hfs : sh.getD t [] = sh[t] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hts]
      rw [hfs] at hc ⊢
      obtain ⟨g₃, m₃, x₃, ml₃, ⟨⟨h30, h32, hm3⟩, -⟩⟩ := encFlds_ok (P := P) sh x l r sh[t]
        (fun _ v' O' mm' a b c => ihl v' O' mm' a b c) (fun _ v' O' mm' a b c => ihr v' O' mm' a b c) sh[t] g₂ m₂
        (O ++ [UInt8.ofNat t]) (fun _ h => h) hI (by simp only [List.length_append, List.length_singleton]; omega)
      have e1 := flatT_ok hP _ (.seq x₃ (.jmp (as := []) hBE (by rw [hpE]; rfl))) _ okj
      simp only [hpE, List.map_nil, setMany] at e1
      have e2 := flatT_ok hP _ (g := g₃) (m := m₃) .ret _ okE
      obtain ⟨l', pc', g', B, rvs, hR, hB, hk, ht', hv'⟩ := e2
      refine ⟨m₃, fin g g' mm m₃ l' pc' B rvs ((e0.trans e1).trans hR) hB hk ht' v O.length hg.symm _ ?_,
        ml₂.trans ml₃, by rw [hm3]; simp⟩
      rw [hv']; simp only [List.map, Arg.eval, h32]; simp
    · have hL : ((List.range sh.length).map (· + 1))[(BitVec.ofNat 64 t).toNat]?.getD (sh.length + 1) =
          sh.length + 1 := by rw [htn]; simp [hts]
      have e0 := flatT_ok hP _ (.iteT (nz_p h1) (.seq x₀ (.sw g23 (by rw [hL]; exact hBE) hpE))) _ ok0
      rw [hL] at e0
      have hfs : sh.getD t [] = [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hts)]
      rw [hfs] at hc ⊢
      have e2 := flatT_ok hP _ (g := g₂) (m := m₂) .ret _ okE
      obtain ⟨l', pc', g', B, rvs, hR, hB, hk, ht', hv'⟩ := e2
      refine ⟨m₂, fin g g' mm m₂ l' pc' B rvs (e0.trans hR) hB hk ht' v O.length hg.symm _ ?_, ml₂, by rw [← hm₂]; simp⟩
      rw [hv']; simp only [List.map, Arg.eval, hI.1.2.1]; simp

end Proven.Ir.IndLow

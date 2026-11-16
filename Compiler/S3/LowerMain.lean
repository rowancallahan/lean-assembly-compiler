/- The lowering of S3 is correct, part 3: `main` (the input bytes as a byte list, the call, the result list written
to the output), and **the meaning of the RTL program is the meaning of the S3 program** (`lower_meaning`). -/
import Compiler.S3.LowerOk
import Compiler.Ir.IndLowMain

namespace Proven.S3
open Proven.Ir Proven.Ir.IndLow Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem bytesOut_nil {w : V} (h : bytesOut w = some []) : w = .c 0 [] := by
  unfold bytesOut at h
  split at h
  · rfl
  · rename_i x r; cases hr : bytesOut r <;> simp [hr] at h
  · exact nomatch h

theorem bytesOut_cons {w : V} {b : UInt8} {rest : List UInt8} (h : bytesOut w = some (b :: rest)) :
    ∃ x r, w = .c 1 [.w x, r] ∧ bytesOut r = some rest ∧ b = UInt8.ofBitVec (x.setWidth 8) := by
  unfold bytesOut at h
  split at h
  · exact nomatch h
  · rename_i x r
    cases hr : bytesOut r with
    | none => simp [hr] at h
    | some o => simp [hr] at h; obtain ⟨h1, h2⟩ := h; subst h2; exact ⟨x, r, rfl, hr, h1.symm⟩
  · exact nomatch h

section
variable {Q : Ir.Prog VReg}

/-- the loop of `inLoop` -/
def inBody : SC := SC.seqs [opK .sub 4 (.r 4) (.i 1), .i (.ldb 5 0 (.r 4)), .i (.alloc 6 (.i 3)),
  .i (.st (.i 1) 6 0), .i (.st (.r 5) 6 1), .i (.st (.r 3) 6 2), mov 3 6]

theorem in_loop (input : List UInt8) (hI : input.length < 2 ^ 64) : ∀ i, i ≤ input.length →
    ∀ (g : VReg → Val) (m : Ir.Mem), g 4 = .w (BitVec.ofNat 64 i) → g 0 = .p 0 0 → m.inp = input →
      Rep m (bytesV (input.drop i)) (g 3) →
      ∃ g' m', SC.Ex Q (.loop ⟨.ne, .r 4, .i 0⟩ inBody) g m g' m' ∧ Grow m m' ∧ Rep m' (bytesV input) (g' 3) ∧
        ∀ r : Nat, r < 3 → g' r = g r
  | 0, _, g, m, h4, _, _, h3 => by
    refine ⟨g, m, .loopF (by simp [Tst.eval, Arg.eval, h4, Cond.eval]), Grow.refl m, by simpa using h3,
      fun _ _ => rfl⟩
  | i + 1, hi, g, m, h4, h0, hin, h3 => by
    have hb : input[i]? = some input[i] := List.getElem?_eq_getElem (by omega)
    -- `4 := i`
    have x1 := ex_op (Q := Q) (g := g) m .sub 4 (.r 4) (.i 1) (x := BitVec.ofNat 64 (i + 1)) (y := 1) (by simp [Arg.eval, h4]) rfl
    have e1 : Op.eval .sub (BitVec.ofNat 64 (i + 1)) 1 = BitVec.ofNat 64 i := by
      simp only [Op.eval]; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e1] at x1
    generalize hg1 : upd g 4 (.w (BitVec.ofNat 64 i)) = g1 at x1
    -- `5 := input[i]`
    have x2 : SC.Ex Q (.i (.ldb 5 0 (.r 4))) g1 m (upd g1 5 (.w (input[i].toBitVec.setWidth 64))) m := by
      refine .i (e := []) (fun _ _ _ h => nomatch h) ?_
      have h10 : g1 0 = .p 0 0 := by rw [← hg1, upd_ne _ _ (by decide), h0]
      have h14 : g1 4 = .w (BitVec.ofNat 64 i) := by rw [← hg1, upd_same]
      simp only [Inst.exec, Arg.word, Arg.eval, h14, h10, hin]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hb]
    generalize hg2 : upd g1 5 (.w (input[i].toBitVec.setWidth 64)) = g2 at x2
    -- the cell
    have x3 := ex_alloc (Q := Q) (g := g2) m 6 3
    generalize hg3 : upd g2 6 (.p (m.blks.length + 2) 0) = g3 at x3
    have h36 : g3 6 = .p (m.blks.length + 2) 0 := by rw [← hg3, upd_same]
    have x4 := ex_st_blk (Q := Q) m (List.replicate (BitVec.toNat (3 : BitVec 64)) none) 6 h36 (.i 1) 0 (by decide)
    have x5 := ex_st_blk (Q := Q) m ((List.replicate (BitVec.toNat (3 : BitVec 64)) none).set 0
      (some ((Arg.i 1 : Arg VReg).eval g3))) 6 h36 (.r 5) 1 (by simp)
    have x6 := ex_st_blk (Q := Q) m (((List.replicate (BitVec.toNat (3 : BitVec 64)) none).set 0
      (some ((Arg.i 1 : Arg VReg).eval g3))).set 1 (some ((Arg.r 5 : Arg VReg).eval g3))) 6 h36 (.r 3) 2
      (by simp)
    have x7 := ex_mov (P := Q) g3 (m.withBlk (((((List.replicate (3 : BitVec 64).toNat none).set 0
      (some ((Arg.i 1 : Arg VReg).eval g3))).set 1 (some ((Arg.r 5 : Arg VReg).eval g3))).set 2
      (some ((Arg.r 3 : Arg VReg).eval g3))))) 3 6
    have hcs : ((((List.replicate (3 : BitVec 64).toNat (none : Option Val)).set 0
        (some ((Arg.i 1 : Arg VReg).eval g3))).set 1 (some ((Arg.r 5 : Arg VReg).eval g3))).set 2
        (some ((Arg.r 3 : Arg VReg).eval g3))) = [some (.w 1), some (g3 5), some (g3 3)] := by
      simp [Arg.eval]
    rw [hcs] at x7
    have h35 : g3 5 = .w (input[i].toBitVec.setWidth 64) := by rw [← hg3, upd_ne _ _ (by decide), ← hg2, upd_same]
    have h33 : g3 3 = g 3 := by
      rw [← hg3, upd_ne _ _ (by decide), ← hg2, upd_ne _ _ (by decide), ← hg1, upd_ne _ _ (by decide)]
    have gr := withBlk_grow m [some (.w 1), some (g3 5), some (g3 3)]
    have xb : SC.Ex Q inBody g m (upd g3 3 (g3 6)) (m.withBlk [some (.w 1), some (g3 5), some (g3 3)]) := by
      unfold inBody; simp only [SC.seqs]
      rw [hcs] at x6
      exact .seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 (.seq x6 x7)))))
    generalize hgB : upd g3 3 (g3 6) = gB at xb
    generalize hmB : m.withBlk [some (.w 1), some (g3 5), some (g3 3)] = mB at xb gr
    have hB4 : gB 4 = .w (BitVec.ofNat 64 i) := by
      rw [← hgB, upd_ne _ _ (by decide), ← hg3, upd_ne _ _ (by decide), ← hg2, upd_ne _ _ (by decide), ← hg1, upd_same]
    have hB0 : gB 0 = .p 0 0 := by
      rw [← hgB, upd_ne _ _ (by decide), ← hg3, upd_ne _ _ (by decide), ← hg2, upd_ne _ _ (by decide), ← hg1,
        upd_ne _ _ (by decide), h0]
    have hBr : ∀ r : Nat, r < 3 → gB r = g r := fun r hr => by
      rw [← hgB, upd_ne _ _ (show r ≠ 3 by omega), ← hg3, upd_ne _ _ (show r ≠ 6 by omega), ← hg2,
        upd_ne _ _ (show r ≠ 5 by omega), ← hg1, upd_ne _ _ (show r ≠ 4 by omega)]
    have hB3 : Rep mB (bytesV (input.drop i)) (gB 3) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp only [bytesV]
      rw [← hgB, upd_same, h36]
      refine ⟨_, m.cells.length, rfl, by rw [← hmB, withBlk_blk]; rfl, by rw [← hmB]; simp [Ir.Mem.withBlk], ?_⟩
      refine ⟨⟨g3 5, by rw [← hmB]; simp [Ir.Mem.withBlk], by simp only [Rep]; exact h35⟩,
        ⟨g3 3, by rw [← hmB]; simp only [Ir.Mem.withBlk]; rw [List.getElem?_append_right (by omega), show m.cells.length + 1 + 1 - m.cells.length = 2 by omega]; rfl, by rw [h33]; exact Rep.mono gr.1 _ _ h3⟩, trivial⟩
    obtain ⟨g', m', xl, gr', rp, fr⟩ := in_loop input hI i (by omega) gB mB hB4 hB0 (by rw [← hmB]; exact hin) hB3
    refine ⟨g', m', .loopT (by
      simp [Tst.eval, Arg.eval, h4, Cond.eval]; intro he; have := congrArg BitVec.toNat he; simp at this; omega)
      xb xl, gr.trans gr', rp, fun r hr => by rw [fr r hr, hBr r hr]⟩

theorem ex_ldG {g : VReg → Val} {m : Ir.Mem} {d p : VReg} {k : Nat} {b c0 sz : Nat} {v : Val} (hp : g p = .p b 0)
    (hb : m.blk b = some (c0, sz)) (hk : k < sz) (hc : m.cells[c0 + k]? = some (some v)) :
    SC.Ex Q (.i (.ld d p k)) g m (upd g d v) m :=
  .i (e := []) (fun _ _ _ h => nomatch h) (by simp [Inst.exec, hp, hb, hk, hc])

def tagOf (rest : List UInt8) : BitVec 64 := if rest = [] then 0 else 1

/-- a byte-list value: its tag cell -/
theorem rep_tag {m : Ir.Mem} {w : V} {a : Val} {rest : List UInt8} (hr : Rep m w a) (h : bytesOut w = some rest) :
    ∃ b c0 sz, a = .p b 0 ∧ m.blk b = some (c0, sz) ∧ 0 < sz ∧ m.cells[c0 + 0]? = some (some (.w (tagOf rest))) := by
  cases rest with
  | nil =>
    rw [bytesOut_nil h] at hr
    obtain ⟨b, c0, e, hb, hc, -⟩ := (by simpa only [Rep] using hr : ∃ b c0, a = .p b 0 ∧ m.blk b = some (c0, 0 + 1) ∧
      m.cells[c0]? = some (some (.w (BitVec.ofNat 64 0))) ∧ RepL m [] (c0 + 1))
    exact ⟨b, c0, _, e, hb, by omega, by simpa [tagOf] using hc⟩
  | cons x rest =>
    obtain ⟨y, r, hw, -, -⟩ := bytesOut_cons h
    subst hw
    obtain ⟨b, c0, e, hb, hc, -⟩ := (by simpa only [Rep] using hr : ∃ b c0, a = .p b 0 ∧ m.blk b = some (c0, [V.w y, r].length + 1) ∧
      m.cells[c0]? = some (some (.w (BitVec.ofNat 64 1))) ∧ RepL m [V.w y, r] (c0 + 1))
    exact ⟨b, c0, _, e, hb, by omega, by simpa [tagOf] using hc⟩

/-- the loop of `outLoop` -/
def outBody : SC := SC.seqs [.i (.ld 10 7 1), .i (.stb (.r 10) 2 (.r 8)), addK 8 8 1, .i (.ld 7 7 2), .i (.ld 9 7 0)]

theorem out_loop : ∀ (rest written : List UInt8) (w : V) (g : VReg → Val) (m : Ir.Mem), bytesOut w = some rest →
    Rep m w (g 7) → g 8 = .w (BitVec.ofNat 64 written.length) → g 2 = .p 1 0 → m.out = written.map some →
    (written ++ rest).length < 2 ^ 64 → g 9 = .w (tagOf rest) →
    ∃ g' m', SC.Ex Q (.loop ⟨.ne, .r 9, .i 0⟩ outBody) g m g' m' ∧ m'.out = (written ++ rest).map some
  | [], written, w, g, m, _, _, _, _, ho, _, h9 =>
    ⟨g, m, .loopF (by simp [Tst.eval, Arg.eval, h9, Cond.eval, tagOf]), by simpa using ho⟩
  | b :: rest, written, w, g, m, hw, hr, h8, h2, ho, hl, h9 => by
    obtain ⟨x, r, hwe, hro, hbx⟩ := bytesOut_cons hw
    subst hwe
    obtain ⟨blk, c0, e7, hblk, -, hRL⟩ := (by simpa only [Rep] using hr : ∃ blk c0, g 7 = .p blk 0 ∧
      m.blk blk = some (c0, [V.w x, r].length + 1) ∧ m.cells[c0]? = some (some (.w (BitVec.ofNat 64 1))) ∧
      RepL m [V.w x, r] (c0 + 1))
    obtain ⟨y1, hy1, hr1⟩ := hRL.get 0 (by simp)
    obtain ⟨y2, hy2, hr2⟩ := hRL.get 1 (by simp)
    have hy1' : y1 = .w x := by simpa only [Rep, List.getElem_cons_zero] using hr1
    subst hy1'
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hr2
    -- `10 := x`
    have x1 := ex_ldG (Q := Q) (d := 10) (k := 1) e7 hblk (by simp) (by simpa using hy1)
    generalize hg1 : upd g 10 (.w x) = g1 at x1
    have g18 : g1 8 = .w (BitVec.ofNat 64 written.length) := by rw [← hg1, upd_ne _ _ (by decide), h8]
    have g12 : g1 2 = .p 1 0 := by rw [← hg1, upd_ne _ _ (by decide), h2]
    have g17 : g1 7 = .p blk 0 := by rw [← hg1, upd_ne _ _ (by decide), e7]
    -- the byte
    have hwl : written.length < 2 ^ 64 := by simp at hl; omega
    generalize hm1 : ({ m with out := (written ++ [b]).map some } : Ir.Mem) = m1
    have x2 : SC.Ex Q (.i (.stb (.r 10) 2 (.r 8))) g1 m g1 m1 := by
      refine .i (e := []) (fun _ _ _ h => nomatch h) ?_
      have g110 : g1 10 = .w x := by rw [← hg1, upd_same]
      simp only [Inst.exec, Arg.word, Arg.eval, g110, g18, g12]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl, ho, setOut_snoc' written _ rfl, ← hm1, hbx]
    have x3 := ex_addK (P := Q) m1 8 8 1 g18
    have e3 : BitVec.ofNat 64 written.length + 1 = BitVec.ofNat 64 (written ++ [b]).length := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e3] at x3
    generalize hg3 : upd g1 8 (.w (BitVec.ofNat 64 (written ++ [b]).length)) = g3 at x3
    have hb1 : m1.blk blk = some (c0, [V.w x, r].length + 1) := by rw [← hm1]; exact hblk
    have g37 : g3 7 = .p blk 0 := by rw [← hg3, upd_ne _ _ (by decide), g17]
    have x4 := ex_ldG (Q := Q) (d := 7) g37 hb1 (k := 2) (by simp) (by rw [← hm1]; simpa using hy2)
    generalize hg4 : upd g3 7 y2 = g4 at x4
    have gr1 : MLe m m1 := by rw [← hm1]; exact ⟨rfl, fun _ _ _ h => h, fun _ _ h => h⟩
    have hr2' : Rep m1 r (g4 7) := by rw [← hg4, upd_same]; exact Rep.mono gr1 _ _ hr2
    obtain ⟨b', c0', sz', e', hb', hsz', hc'⟩ := rep_tag hr2' hro
    have x5 := ex_ldG (Q := Q) (d := 9) e' hb' hsz' hc'
    generalize hg5 : upd g4 9 (.w (tagOf rest)) = g5 at x5
    have xb : SC.Ex Q outBody g m g5 m1 := by
      unfold outBody; simp only [SC.seqs]
      exact .seq x1 (.seq x2 (.seq x3 (.seq x4 x5)))
    have g57 : g5 7 = g4 7 := by rw [← hg5, upd_ne _ _ (by decide)]
    have g58 : g5 8 = .w (BitVec.ofNat 64 (written ++ [b]).length) := by
      rw [← hg5, upd_ne _ _ (by decide), ← hg4, upd_ne _ _ (by decide), ← hg3, upd_same]
    have g52 : g5 2 = .p 1 0 := by
      rw [← hg5, upd_ne _ _ (by decide), ← hg4, upd_ne _ _ (by decide), ← hg3, upd_ne _ _ (by decide), g12]
    have g59 : g5 9 = .w (tagOf rest) := by rw [← hg5, upd_same]
    obtain ⟨g', m', xl, ho'⟩ := out_loop rest (written ++ [b]) r g5 m1 hro (by rw [g57]; exact hr2') g58 g52
      (by rw [← hm1]) (by simpa using hl) g59
    refine ⟨g', m', .loopT (by simp [Tst.eval, Arg.eval, h9, Cond.eval, tagOf]) xb xl, by simpa using ho'⟩

end

end Proven.S3

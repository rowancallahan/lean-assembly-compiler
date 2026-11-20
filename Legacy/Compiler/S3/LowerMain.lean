/- The lowering of S3 is correct, part 3: `main` (the input bytes as a byte list, the call, the result list written
to the output), and **the meaning of the RTL program is the meaning of the S3 program** (`lower_meaning`). -/
import Legacy.Compiler.S3.LowerOk
import Legacy.Compiler.Ir.IndLowMain

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
    obtain ⟨b, c0, e, hb, hc, -⟩ := (by simp only [Rep] at hr; exact hr : ∃ b c0, a = .p b 0 ∧ m.blk b = some (c0, 0 + 1) ∧
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
    ∃ g' m', SC.Ex Q (.loop ⟨.ne, .r 9, .i 0⟩ outBody) g m g' m' ∧ m'.out = (written ++ rest).map some ∧
      g' 8 = .w (BitVec.ofNat 64 (written ++ rest).length)
  | [], written, w, g, m, _, _, h8, _, ho, _, h9 =>
    ⟨g, m, .loopF (by simp [Tst.eval, Arg.eval, h9, Cond.eval, tagOf]), by simpa using ho, by simpa using h8⟩
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
    obtain ⟨g', m', xl, ho', h8'⟩ := out_loop rest (written ++ [b]) r g5 m1 hro (by rw [g57]; exact hr2') g58 g52
      (by rw [← hm1]) (by simpa using hl) g59
    refine ⟨g', m', .loopT (by simp [Tst.eval, Arg.eval, h9, Cond.eval, tagOf]) xb xl, by simpa using ho',
      by simpa using h8'⟩

end

/-- what the compiler checks: small datatypes, a one-parameter `main` -/
def Accepted (P : Prog) : Prop := Small P.S ∧ (P.S.fn P.main).1.length = 1

theorem lowerP_fn (P : Prog) (f : Fin P.S.fns.length) : (lowerP P).funcs[f.val]? = some (lowFn P f) := by
  simp [lowerP, List.getElem?_append_left (show f.val < (List.ofFn (lowFn P)).length by simp)]

theorem lowerP_main (P : Prog) : (lowerP P).funcs[(lowerP P).main]? = some (mainF P.main.val) := by
  simp [lowerP]

/-- **the run of the lowered program**: on every input where `main` has a value whose bytes are `out`, the RTL
program's run ends with the output `out` and `main` returns the number of bytes `out.length` -/
theorem lower_result (P : Prog) (hG : Accepted P) (input out : List UInt8) (v : V) (hD : P.Den input v)
    (ho : bytesOut v = some out) (hI : input.length < 2 ^ 64) (hO : out.length < 2 ^ 64) :
    ∃ r, (lowerP P).result input = some r ∧ r.mem.output = some out ∧
      r.vs = [.w (BitVec.ofNat 64 out.length)] := by
  generalize hQ : lowerP P = Q
  have hfns : HasFns P Q := fun f => by rw [← hQ]; exact lowerP_fn P f
  have hQm : Q.funcs[Q.main]? = some (mainF P.main.val) := by rw [← hQ]; exact lowerP_main P
  generalize hF : mainF P.main.val = F at hQm
  obtain ⟨nl', okm⟩ := mkFunc_region (params := [0, 1, 2]) (ps := [0, 1, 2]) (nl := 1)
    (rs := [(0, mainTC P.main.val)]) (by simp) (by simp) 0 (by simp)
  have hF' : mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC P.main.val)] = F := hF
  rw [hF'] at okm
  simp only [List.getElem_cons_zero, if_true] at okm
  generalize hg0 : setMany (fun _ => Val.w 0) [0, 1, 2] [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0] = g0
  have g00 : g0 0 = .p 0 0 := by rw [← hg0]; simp [setMany, upd]
  have g01 : g0 1 = .w (BitVec.ofNat 64 input.length) := by rw [← hg0]; simp [setMany, upd]
  have g02 : g0 2 = .p 1 0 := by rw [← hg0]; simp [setMany, upd]
  -- the empty list
  have m0 := Ir.Mem.init input
  have xa := ex_alloc (Q := Q) (g := g0) (Ir.Mem.init input) 3 1
  generalize hga : upd g0 3 (.p ((Ir.Mem.init input).blks.length + 2) 0) = ga at xa
  have ha3 : ga 3 = .p ((Ir.Mem.init input).blks.length + 2) 0 := by rw [← hga, upd_same]
  have xb := ex_st_blk (Q := Q) (Ir.Mem.init input) (List.replicate (BitVec.toNat (1 : BitVec 64)) none) 3 ha3 (.i 0) 0
    (by simp)
  have hcs : (List.replicate (BitVec.toNat (1 : BitVec 64)) (none : Option Val)).set 0
      (some ((Arg.i 0 : Arg VReg).eval ga)) = [some (.w 0)] := by simp [Arg.eval]
  rw [hcs] at xb
  generalize hm1 : (Ir.Mem.init input).withBlk [some (.w 0)] = m1 at xb
  have gr1 : Grow (Ir.Mem.init input) m1 := by rw [← hm1]; exact withBlk_grow _ _
  have xc := ex_mov (P := Q) ga m1 4 1
  generalize hgc : upd ga 4 (ga 1) = gc at xc
  have gc4 : gc 4 = .w (BitVec.ofNat 64 input.length) := by
    rw [← hgc, upd_same, ← hga, upd_ne _ _ (by decide), g01]
  have gc0 : gc 0 = .p 0 0 := by rw [← hgc, upd_ne _ _ (by decide), ← hga, upd_ne _ _ (by decide), g00]
  have gc3 : Rep m1 (bytesV (input.drop input.length)) (gc 3) := by
    rw [List.drop_length]
    rw [← hgc, upd_ne _ _ (by decide), ha3]
    refine ⟨_, (Ir.Mem.init input).cells.length, rfl, by rw [← hm1, withBlk_blk]; rfl, by
      rw [← hm1]; simp [Ir.Mem.withBlk, Ir.Mem.init], trivial⟩
  obtain ⟨gd, md, xd, grd, rpd, frd⟩ := in_loop (Q := Q) input hI input.length (Nat.le_refl _) gc m1 gc4 gc0
    (by rw [← hm1]; rfl) gc3
  -- the call
  obtain ⟨x, me, hR, gre, rpe⟩ := fn_returns hfns P.main
    (fun ρ n g m he hb => low_ok hfns hG.1 hD ρ n g m he hb) [gd 3] rfl (by rw [hG.2]; rfl)
    (fun k h₁ h₂ => by
      have : k = 0 := by simp at h₁; omega
      subst this; exact rpd)
  have xe : SC.Ex Q (.i (.call [7] P.main.val [.r 3])) gd md (upd gd 7 x) me := by
    have := SC.Ex.call (P := Q) (ds := [7]) (as := [.r 3]) (g := gd) (by simpa [Arg.eval] using hR) rfl
    simpa [setMany] using this
  generalize hge : upd gd 7 x = ge at xe
  have ge2 : ge 2 = .p 1 0 := by
    rw [← hge, upd_ne _ _ (by decide), frd 2 (by decide), ← hgc, upd_ne _ _ (by decide), ← hga,
      upd_ne _ _ (by decide), g02]
  -- the output
  have xf := ex_setK (P := Q) ge me 8 0
  generalize hgf : upd ge 8 (.w 0) = gf at xf
  have rpf : Rep me v (gf 7) := by rw [← hgf, upd_ne _ _ (by decide), ← hge, upd_same]; exact rpe
  obtain ⟨b', c0', sz', e', hb', hsz', hc'⟩ := rep_tag rpf ho
  have xg := ex_ldG (Q := Q) (d := 9) e' hb' hsz' hc'
  generalize hgg : upd gf 9 (.w (tagOf out)) = gg at xg
  have heo : me.out = [] := by
    rw [gre.2, grd.2, gr1.2]; rfl
  obtain ⟨gh, mh, xh, hoh, h8h⟩ := out_loop (Q := Q) out [] v gg me ho
    (by rw [← hgg, upd_ne _ _ (by decide)]; exact rpf)
    (by rw [← hgg, upd_ne _ _ (by decide), ← hgf, upd_same]; rfl)
    (by rw [← hgg, upd_ne _ _ (by decide), ← hgf, upd_ne _ _ (by decide), ge2])
    (by rw [heo]; rfl) (by simpa using hO) (by rw [← hgg, upd_same])
  -- the run
  have xM : TC.Ex Q F (mainTC P.main.val) g0 (Ir.Mem.init input) (.ret [gh 8] mh) := by
    simp only [mainTC, inLoop, outLoop, SC.seqs]
    exact .seq (.seq (.seq xa (.seq xb (.seq xc (by simpa [inBody, SC.seqs] using xd))))
      (.seq xe (.seq xf (.seq xg (by simpa [outBody, SC.seqs] using xh))))) .ret
  obtain ⟨l', pc', g', B, rvs, hR', hB, hk, ht, hv⟩ := flatT_ok hQm _ xM _ okm
  have hFe : F.entry = 0 := by rw [← hF']; rfl
  have hFp : F.params = [0, 1, 2] := by rw [← hF']; rfl
  have hinit : init Q input = ⟨[⟨Q.main, 0, 0, g0, []⟩], Ir.Mem.init input, []⟩ := by
    unfold init; rw [hQm]; dsimp only; rw [hFe, hFp, hg0]
  obtain ⟨ev', hst⟩ := hR' [] [] []
  have hdone : step Q ⟨[⟨Q.main, l', pc', g', []⟩], mh, ev'⟩ = .done ⟨rvs.map (Arg.eval g'), mh, ev'⟩ := by
    unfold step; simp only [hQm, hB, hk, ht, termStep]
  obtain ⟨n, hn⟩ := Star.run hst hdone
  have hres := Prog.result_eq (P := Q) (input := input) ⟨n, by rw [hinit]; exact hn⟩
  refine ⟨_, hres, ?_, ?_⟩
  · simp only [Ir.Mem.output, hoh, List.nil_append, mapM_some]
  · simp only [hv, h8h, List.nil_append]

/-- **the lowering is correct**: on every input where `main` has a value whose bytes are `out`, the RTL program's
meaning is `out` -/
theorem lower_meaning (P : Prog) (hG : Accepted P) (input out : List UInt8) (v : V) (hD : P.Den input v)
    (ho : bytesOut v = some out) (hI : input.length < 2 ^ 64) (hO : out.length < 2 ^ 64) :
    (lowerP P).meaning input = some out := by
  obtain ⟨r, hr, hout, -⟩ := lower_result P hG input out v hD ho hI hO
  show ((lowerP P).result input).bind (fun r => r.mem.output) = _
  rw [hr]; exact hout

end Proven.S3

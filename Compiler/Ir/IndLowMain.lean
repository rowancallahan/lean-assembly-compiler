/- The correctness of the inductive path's lowering to RTL, part 6: the program's functions (`chain_ok`: each returns
its `Pg.sem`, the later ones first), `main` (decode, call, encode), and **`lower_ok`**: the RTL program's meaning on
the input bytes of well-formed values is the output of `Pg.sem`. -/
import Compiler.Ir.IndLowEnc
import Compiler.IndMain

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

variable {P : Prog VReg}

theorem semX_get : ∀ (ps : List (Σ k : Kd, Pg k)) (j : Nat) (hj : j < ps.length) (t : C) (a : BitVec 64) (b : C),
    semX ps j t a b = ps[j].1.pair (ps[j].2.sem t a b)
  | [], _, hj, _, _, _ => absurd hj (by simp)
  | ⟨k, p⟩ :: ps, 0, _, t, a, b => rfl
  | ⟨k, p⟩ :: ps, j + 1, hj, t, a, b => semX_get ps j (by simp at hj; omega) t a b

/-- **every function of the chain returns its meaning** -/
theorem chain_ok : ∀ (fs : List (Σ k : Kd, Pg k)) (base : Nat),
    (∀ i (hi : i < fs.length), P.funcs[base + i]? = some (lowPg (base + i) fs[i].2)) → Chain fs → okL fs = true →
    ∀ i (hi : i < fs.length) (t : C) (a : BitVec 64) (b : C) (vt vb : Val) (mm : Mem), Rv mm vt t → Rv mm vb b →
      RetOk P (base + i) [vt, .w a, vb] mm fs[i].1 (fs[i].2.sem t a b)
  | [], _, _, _, _, i, hi, _, _, _, _, _, _, _, _ => absurd hi (by simp)
  | ⟨k, p⟩ :: ps, base, hget, hch, hok, i, hi, t, a, b, vt, vb, mm, rt, rb => by
    have hget' : ∀ i (hi : i < ps.length), P.funcs[(base + 1) + i]? = some (lowPg ((base + 1) + i) ps[i].2) :=
      fun i hi => by
        have := hget (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show base + 1 + i = base + (i + 1) by omega]; exact this
    simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
    obtain ⟨⟨-, hok1⟩, hok2⟩ := hok
    obtain ⟨hX, hch2⟩ := hch
    have ih := chain_ok ps (base + 1) hget' hch2 hok2
    cases i with
    | zero =>
      have hF := hget 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hF ⊢
      have hX' : ∀ (j : Nat) (hj : j < (List.map (fun x : (Σ k : Kd, Pg k) => x.1) ps).length) (t' : C)
          (a' : BitVec 64) (b' : C) (vt' vb' : Val) (mm' : Mem), Rv mm' vt' t' → Rv mm' vb' b' →
          RetOk P (base + 1 + j) [vt', .w a', vb'] mm' (List.map (fun x : (Σ k : Kd, Pg k) => x.1) ps)[j]
            ((List.map (fun x : (Σ k : Kd, Pg k) => x.1) ps)[j].pick (p.X j t' a' b')) := by
        intro j hj t' a' b' vt' vb' mm' r1 r2
        have hj' : j < ps.length := by simpa using hj
        rw [(hX j hj').1, semX_get ps j hj']
        rw [List.getElem_map, Kd.pick_pair]
        exact ih j hj' t' a' b' vt' vb' mm' r1 r2
      have := pg_ok (P := P) base (List.map (fun x : (Σ k : Kd, Pg k) => x.1) ps) p hF (fun e he => hok1 e he) hX'
        (t.depth + 1) t (by omega) a b _ mm (by rw [(regs0 vt vb a).1]; exact rt) (regs0 vt vb a).2.1
        (by rw [(regs0 vt vb a).2.2]; exact rb)
      exact fret_returns hF rfl rfl this
    | succ i =>
      have := ih i (by simp at hi; omega) t a b vt vb mm rt rb
      simp only [List.getElem_cons_succ]
      rw [show base + (i + 1) = base + 1 + i by omega]; exact this

/-! ## main -/

/-- one byte of a word result -/
def wStep (j : Nat) : SC :=
  .seq (.i (.let_ 8 (.op .lshr (.r 7) (.i (BitVec.ofNat 64 (8 * j)))))) (.i (.stb (.r 8) 2 (.i (BitVec.ofNat 64 j))))

theorem setOut_snoc' (O : List UInt8) (j : Nat) (hj : O.length = j) (b : UInt8) :
    setOut (O.map some) j b = (O ++ [b]).map some := by rw [← hj]; exact setOut_snoc O b

theorem wout_loop (y : BitVec 64) : ∀ k j, j + k ≤ 8 → ∀ (g : VReg → Val) (m : Mem), g 7 = .w y → g 2 = .p 1 0 →
    m.out = ((leN 8 y.toNat).take j).map some →
    ∃ g', SC.Ex P (.seqs ((List.range' j k).map wStep)) g m g' { m with out := ((leN 8 y.toNat).take (j + k)).map some }
  | 0, j, _, g, m, _, _, hm => by
    have : ({ m with out := ((leN 8 y.toNat).take (j + 0)).map some } : Mem) = m := by rw [Nat.add_zero, ← hm]
    rw [this]; exact ⟨g, .nop⟩
  | k + 1, j, hj, g, m, h7, h2, hm => by
    have hjl : j < (leN 8 y.toNat).length := by rw [leN_length]; omega
    have x₁ := ex_let (P := P) (g := g) (m := m) 8 (.op .lshr (.r 7) (.i (BitVec.ofNat 64 (8 * j))))
      (v := .w (Op.eval .lshr y (BitVec.ofNat 64 (8 * j)))) (by simp [Rhs.eval, Arg.word, Arg.eval, h7])
    have hbyte : (leN 8 y.toNat)[j] = UInt8.ofNat (Op.eval .lshr y (BitVec.ofNat 64 (8 * j))).toNat := by
      have e1 := leN_get 8 y.toNat j (by omega)
      rw [List.getElem?_eq_getElem hjl] at e1
      rw [Option.some.inj e1, ← u8_of, byte_eq y j (by omega)]
    have htl : ((leN 8 y.toNat).take j).length = j := by simp [leN_length]; omega
    have x₂ : SC.Ex P (.i (.stb (.r 8) 2 (.i (BitVec.ofNat 64 j)))) (upd g 8 (.w (Op.eval .lshr y (BitVec.ofNat 64 (8 * j)))))
        m (upd g 8 (.w (Op.eval .lshr y (BitVec.ofNat 64 (8 * j))))) { m with out := ((leN 8 y.toNat).take (j + 1)).map some } :=
      .i (e := []) (fun _ _ _ h => nomatch h) (by
        simp only [Inst.exec, Arg.word, Arg.eval, upd_same, upd_ne _ _ (show (2 : Nat) ≠ 8 by decide), h2,
          toNat_small j (by omega), hm]
        rw [setOut_snoc' _ _ htl, u8_of, ← hbyte, List.take_succ, List.getElem?_eq_getElem hjl]; rfl)
    obtain ⟨g', x₃⟩ := wout_loop y k (j + 1) (by omega) (upd g 8 (.w (Op.eval .lshr y (BitVec.ofNat 64 (8 * j)))))
      { m with out := ((leN 8 y.toNat).take (j + 1)).map some }
      (by rw [upd_ne _ _ (by decide)]; exact h7) (by rw [upd_ne _ _ (by decide)]; exact h2) rfl
    rw [show j + 1 + k = j + (k + 1) by omega] at x₃
    refine ⟨g', ?_⟩
    rw [List.range'_succ, List.map_cons]
    exact ex_seqs_cons (.seq x₁ x₂) (by simpa using x₃)

theorem mapM_some (L : List UInt8) : (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.map_cons, List.mapM_cons, id, ih]; rfl

def biSC : BIn → SC
  | .inp => .i (.call [5, 3] 1 [.r 0, .r 3])
  | .ctor t => mkCell 5 (.i (BitVec.ofNat 64 t)) (.i 0) (.i 0) (.i 0)
  | .none => setK 5 0

def ainSC (ain : Bool) (a0 : BitVec 64) : SC := if ain then rd8 0 3 6 8 9 else setK 6 a0

def outSC (tree : Bool) (nb : Nat) : SC :=
  if tree then .i (.call [8] 2 [.r 2, .r 7, .i 0]) else .seqs ((List.range' 0 nb).map wStep)

def mainTC (bi : BIn) (ain : Bool) (a0 : BitVec 64) (tree : Bool) (nb : Nat) : TC :=
  .seq (.seqs [setK 3 0, .i (.call [4, 3] 1 [.r 0, .r 3]), biSC bi, ainSC ain a0, .i (.call [7] 3 [.r 4, .r 6, .r 5]),
    outSC tree nb]) (.term (.ret []))

theorem mainF_eq (bi : BIn) (ain : Bool) (a0 : BitVec 64) (tree : Bool) (nb : Nat) :
    mainF bi ain a0 tree nb = mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC bi ain a0 tree nb)] := by
  simp only [mainF, mainTC, outSC, biSC, ainSC, List.range_eq_range']
  cases bi <;> rfl

theorem inAt_of {input A L B : List UInt8} (h : input = A ++ L ++ B) : InAt input A.length L := by
  intro i hi; subst h
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem lower_get {rk : Kd} (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (nb : Nat) : ∀ i (hi : i < (⟨rk, pg⟩ :: hs).length),
    (lower sh shO pg hs bi ain a0 nb).funcs[3 + i]? = some (lowPg (3 + i) (⟨rk, pg⟩ :: hs)[i].2)
  | 0, _ => rfl
  | i + 1, hi => by
    simp only [List.length_cons] at hi
    simp only [lower, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil, List.getElem?_mapIdx,
      show 3 + (i + 1) - (0 + 1 + 1 + 1 + 1) = i by omega, List.getElem?_eq_getElem (show i < hs.length by omega),
      Option.map_some, show 4 + i = 3 + (i + 1) by omega]

/-- **the lowering is correct**: on the input bytes of well-formed values, the RTL program's meaning is the bytes
of `Pg.sem` (for outputs of at most `2 ^ 32` bytes, all a machine's memory can hold) -/
theorem lower_ok {rk : Kd} (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (nb : Nat) (hsh : sh.length < 255) (hch : Chain (⟨rk, pg⟩ :: hs))
    (hok : okL (⟨rk, pg⟩ :: hs) = true) (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (v₁ v₂ : C) (a : BitVec 64) (h1 : v₁.wf sh) (h2 : bi = .inp → v₂.wf sh)
    (hI : (inBytesA sh bi ain v₁ v₂ a).length ≤ 2 ^ 20)
    (hO : (Kd.out shO nb rk (pg.sem v₁ (if ain then a else a0) (bi.val v₂))).length ≤ 2 ^ 32) :
    (lower sh shO pg hs bi ain a0 nb).meaning (inBytesA sh bi ain v₁ v₂ a) =
      some (Kd.out shO nb rk (pg.sem v₁ (if ain then a else a0) (bi.val v₂))) := by
  generalize hP : lower sh shO pg hs bi ain a0 nb = P
  have hget := lower_get sh shO pg hs bi ain a0 nb
  rw [hP] at hget
  have hP0 : P.funcs[0]? = some (mainF bi ain a0 (decide (rk = .t)) nb) := by rw [← hP]; rfl
  have hP1 : P.funcs[1]? = some (decF sh) := by rw [← hP]; rfl
  have hP2 : P.funcs[2]? = some (encF shO) := by rw [← hP]; rfl
  have hmain : P.main = 0 := by rw [← hP]; rfl
  generalize hin : inBytesA sh bi ain v₁ v₂ a = input at hI
  generalize haa : (if ain then a else a0) = aa at hO ⊢
  generalize hy : pg.sem v₁ aa (bi.val v₂) = y at hO
  rw [mainF_eq] at hP0
  generalize hF : mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC bi ain a0 (decide (rk = .t)) nb)] = F at hP0
  obtain ⟨nl', okm⟩ := mkFunc_region (params := [0, 1, 2]) (ps := [0, 1, 2]) (nl := 1)
    (rs := [(0, mainTC bi ain a0 (decide (rk = .t)) nb)]) (by simp) (by simp) 0 (by simp)
  rw [hF] at okm
  simp only [List.getElem_cons_zero, if_true] at okm
  -- the start
  generalize hg0 : setMany (fun _ => Val.w 0) [0, 1, 2] [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0] = g0
  have g00 : g0 0 = .p 0 0 := by rw [← hg0]; simp [setMany, upd]
  have g02 : g0 2 = .p 1 0 := by rw [← hg0]; simp [setMany, upd]
  have hlen₁ : (v₁.enc sh).length < 2 ^ 20 + 1 := by
    have : (v₁.enc sh).length ≤ input.length := by
      rw [← hin]; simp only [inBytesA, inBytes, List.length_append]; split <;> simp <;> omega
    omega
  -- dec of the first value
  have xA := ex_setK (P := P) g0 (Mem.init input) 3 0
  obtain ⟨v1, m1, hr1, ml1, o1, rv1⟩ := dec_ok (P := P) sh hsh hP1 v₁ h1 0 (Mem.init input)
    (by
      have := inAt_of (A := []) (L := v₁.enc sh)
        (B := (if bi = .inp then v₂.enc sh else []) ++ if ain then leN 8 a.toNat else []) (input := input)
        (by rw [← hin]; simp only [inBytesA, inBytes]; cases bi <;> simp)
      simpa [Mem.init] using this) (by omega)
  have xB : SC.Ex P (.i (.call [4, 3] 1 [.r 0, .r 3])) (upd g0 3 (.w 0)) (Mem.init input)
      (setMany (upd g0 3 (.w 0)) [4, 3] [v1, .w (BitVec.ofNat 64 (0 + (v₁.enc sh).length))]) m1 :=
    .call (by simp only [List.map, Arg.eval, upd_same, upd_ne _ _ (show (0 : Nat) ≠ 3 by decide), g00]; exact hr1) rfl
  generalize hgB : setMany (upd g0 3 (.w 0)) [4, 3] [v1, .w (BitVec.ofNat 64 (0 + (v₁.enc sh).length))] = gB at xB
  have gB0 : gB 0 = .p 0 0 := by
    rw [← hgB, setMany_two, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact g00
  have gB2 : gB 2 = .p 1 0 := by
    rw [← hgB, setMany_two, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact g02
  have gB3 : gB 3 = .w (BitVec.ofNat 64 (v₁.enc sh).length) := by rw [← hgB, setMany_two, upd_same, Nat.zero_add]
  have gB4 : Rv m1 (gB 4) v₁ := by rw [← hgB, setMany_two, upd_ne _ _ (by decide), upd_same]; exact rv1
  have hinB : (inBytes sh bi v₁ v₂).length + (if ain then 8 else 0) = input.length := by
    rw [← hin]; simp only [inBytesA, List.length_append]; split <;> simp [leN_length]
  -- the second value
  have stepC : ∃ gC mC, SC.Ex P (biSC bi) gB m1 gC mC ∧ MLe m1 mC ∧ mC.out = m1.out ∧ Rv mC (gC 5) (bi.val v₂) ∧
      gC 3 = .w (BitVec.ofNat 64 (inBytes sh bi v₁ v₂).length) ∧ ∀ q : Nat, q ≠ 3 → q ≠ 5 → gC q = gB q := by
    cases bi with
    | inp =>
      have hl2 : (v₁.enc sh).length + (v₂.enc sh).length ≤ input.length := by
        have := hinB; simp only [inBytes, List.length_append] at this; omega
      obtain ⟨v2, m2, hr2, ml2, o2, rv2⟩ := dec_ok (P := P) sh hsh hP1 v₂ (h2 rfl) (v₁.enc sh).length m1
        (by
          rw [ml1.1]
          have := inAt_of (A := v₁.enc sh) (L := v₂.enc sh) (B := if ain then leN 8 a.toNat else []) (input := input)
            (by rw [← hin]; simp only [inBytesA, inBytes])
          simpa [Mem.init] using this) (by omega)
      refine ⟨_, m2, .call (vs := [v2, .w (BitVec.ofNat 64 ((v₁.enc sh).length + (v₂.enc sh).length))])
        (by simp only [List.map, Arg.eval, gB0, gB3]; exact hr2) rfl, ml2, o2, ?_, ?_, fun q a b => ?_⟩
      · rw [setMany_two, upd_ne _ _ (by decide), upd_same]; exact rv2
      · rw [setMany_two, upd_same]; simp [inBytes]
      · rw [setMany_two, upd_ne _ _ a, upd_ne _ _ b]
    | ctor t =>
      have ht := hbi t rfl
      obtain ⟨hle, hrv⟩ := mkCell_rv (m := m1) (t := t) (x := 0) ht Rv.z Rv.z
      exact ⟨_, _, ex_mkCell' (P := P) (vt := .w (BitVec.ofNat 64 t)) (vx := .w 0) (vl := .w 0) (vr := .w 0)
        rfl rfl rfl rfl, hle, rfl, by rw [upd_same]; exact hrv, by rw [upd_ne _ _ (by decide)]; exact gB3,
        fun q a b => upd_ne _ _ b⟩
    | none =>
      exact ⟨_, m1, ex_setK gB m1 5 0, MLe.refl m1, rfl, by rw [upd_same]; exact Rv.z,
        by rw [upd_ne _ _ (by decide)]; exact gB3, fun q a b => upd_ne _ _ b⟩
  obtain ⟨gC, mC, xC, mlC, oC, gC5, gC3, fC⟩ := stepC
  -- the word argument
  have stepD : ∃ gD, SC.Ex P (ainSC ain a0) gC mC gD mC ∧ gD 6 = .w aa ∧ ∀ q : Nat, q ≠ 6 → q ≠ 8 → q ≠ 9 → gD q = gC q := by
    cases ain with
    | false =>
      simp only [Bool.false_eq_true, if_false] at haa
      exact ⟨_, ex_setK gC mC 6 a0, by rw [upd_same, haa], fun q a b c => upd_ne _ _ a⟩
    | true =>
      simp only [if_true] at haa hinB
      have hA : InAt mC.inp (inBytes sh bi v₁ v₂).length (leN 8 a.toNat) := by
        rw [mlC.1, ml1.1]
        have := inAt_of (A := inBytes sh bi v₁ v₂) (L := leN 8 a.toNat) (B := []) (input := input)
          (by rw [← hin]; simp [inBytesA])
        simpa [Mem.init] using this
      obtain ⟨gD, xD, hD6, fD⟩ := rd8_ok (P := P) (inp := 0) (cur := 3) (d := 6) (t1 := 8) (t2 := 9) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (leN 8 a.toNat) (leN_length _ _) (fun i hi => hA i (by rw [leN_length]; exact hi)) (by omega)
        (by rw [fC 0 (by decide) (by decide)]; exact gB0) gC3
      rw [unle_leN8 _ a.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq, haa] at hD6
      exact ⟨gD, xD, hD6, fun q a b c => fD q a b c⟩
  obtain ⟨gD, xD, gD6, fD⟩ := stepD
  -- the call
  have gD4 : Rv mC (gD 4) v₁ := by
    rw [fD 4 (by decide) (by decide) (by decide), fC 4 (by decide) (by decide)]; exact gB4.mono mlC
  have gD5 : Rv mC (gD 5) (bi.val v₂) := by rw [fD 5 (by decide) (by decide) (by decide)]; exact gC5
  obtain ⟨res, mE, hrE, mlE, oE, rvE⟩ := chain_ok (P := P) (⟨rk, pg⟩ :: hs) 3 hget hch hok 0 (by simp) v₁ aa
    (bi.val v₂) (gD 4) (gD 5) mC gD4 gD5
  simp only [List.getElem_cons_zero, Nat.add_zero] at hrE rvE
  rw [hy] at rvE
  have xE : SC.Ex P (.i (.call [7] 3 [.r 4, .r 6, .r 5])) gD mC (upd gD 7 res) mE :=
    .call (vs := [res]) (by simp only [List.map, Arg.eval, gD6]; exact hrE) rfl
  have gE2 : upd gD 7 res 2 = .p 1 0 := by
    rw [upd_ne _ _ (by decide), fD 2 (by decide) (by decide) (by decide), fC 2 (by decide) (by decide)]; exact gB2
  have oE' : mE.out = [] := by rw [oE, oC, o1]; rfl
  -- the output
  have stepF : ∃ gF mF, SC.Ex P (outSC (decide (rk = .t)) nb) (upd gD 7 res) mE gF mF ∧
      mF.out = (Kd.out shO nb rk y).map some := by
    cases rk with
    | t =>
      obtain ⟨mF, hrF, -, oF⟩ := enc_ok (P := P) shO hP2 y res [] mE rvE (by rw [oE']; rfl) (by simp [Kd.out] at hO; simp; omega)
      refine ⟨setMany (upd gD 7 res) [8] [.w (BitVec.ofNat 64 ([] ++ y.enc shO).length)], mF, ?_, by rw [oF]; rfl⟩
      show SC.Ex P (.i (.call [8] 2 [.r 2, .r 7, .i 0])) _ _ _ _
      exact .call (ds := [8]) (vs := [.w (BitVec.ofNat 64 ([] ++ y.enc shO).length)])
        (by
          rw [show List.map (Arg.eval (upd gD 7 res)) [Arg.r 2, Arg.r 7, Arg.i 0] = [.p 1 0, res, .w 0] by
            simp [Arg.eval, gE2]]
          exact hrF) rfl
    | w =>
      obtain ⟨gF, xF⟩ := wout_loop (P := P) y nb 0 (by omega) (upd gD 7 res) mE (by rw [upd_same]; exact rvE) gE2
        (by rw [oE']; rfl)
      refine ⟨gF, { mE with out := ((leN 8 y.toNat).take (0 + nb)).map some }, ?_, by simp [Kd.out]⟩
      simp only [outSC, show decide (Kd.w = Kd.t) = false from rfl, Bool.false_eq_true, if_false]
      simpa using xF
  obtain ⟨gF, mF, xF, oF⟩ := stepF
  -- the run
  have xM : TC.Ex P F (mainTC bi ain a0 (decide (rk = .t)) nb) g0 (Mem.init input) (.ret [] mF) := by
    simp only [mainTC, SC.seqs]
    exact .seq (.seq xA (.seq xB (.seq xC (.seq xD (.seq xE xF))))) .ret
  obtain ⟨l', pc', g', B, rvs, hR, hB, hk, ht, hv⟩ := flatT_ok hP0 _ xM _ okm
  have hFe : F.entry = 0 := by rw [← hF]; rfl
  have hFp : F.params = [0, 1, 2] := by rw [← hF]; rfl
  have hinit : init P input = ⟨[⟨0, 0, 0, g0, []⟩], Mem.init input, []⟩ := by
    unfold init; rw [hmain, hP0]; dsimp only; rw [hFe, hFp, hg0]
  obtain ⟨ev', hst⟩ := hR [] [] []
  have hdone : step P ⟨[⟨0, l', pc', g', []⟩], mF, ev'⟩ = .done ⟨rvs.map (Arg.eval g'), mF, ev'⟩ := by
    unfold step; simp only [hP0, hB, hk, ht, termStep]
  obtain ⟨n, hn⟩ := Star.run hst hdone
  have hres := Prog.result_eq (P := P) (input := input) ⟨n, by rw [hinit]; exact hn⟩
  show (P.result input).bind (fun r => r.mem.output) = _
  rw [hres]
  simp only [Option.bind_some, Mem.output, oF, mapM_some]

/-- the checkable conditions of `lower_ok` (all but `Chain`) -/
def goodB {rk : Kd} (sh : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (nb : Nat) : Bool :=
  decide (sh.length < 255) && okL (⟨rk, pg⟩ :: hs) && (match bi with | .ctor t => decide (t < 256) | _ => true) &&
    decide (nb ≤ 8)

theorem goodB_spec {rk : Kd} {sh : Shape} {pg : Pg rk} {hs : List (Σ k : Kd, Pg k)} {bi : BIn} {nb : Nat}
    (h : goodB sh pg hs bi nb = true) :
    sh.length < 255 ∧ okL (⟨rk, pg⟩ :: hs) = true ∧ (∀ t, bi = .ctor t → t < 256) ∧ nb ≤ 8 := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun t e => ?_, h4⟩
  subst e; simpa using h3

end Proven.Ir.IndLow

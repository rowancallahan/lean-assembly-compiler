/- The lowering of S3 is correct, part 2: **every big-step derivation of an expression is a run of its code**
(`low_ok`), by induction on the derivation; calls are runs of the callee's IR function (`fn_returns`). -/
import Compiler.S3.LowerMem

namespace Proven.S3
open Proven.Ir Proven.Ir.IndLow Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- the IR program holds the lowered functions -/
def HasFns (P : Prog) (Q : Ir.Prog VReg) : Prop :=
  ∀ f : Fin P.S.fns.length, Q.funcs[f.val]? = some (lowFn P f)

/-- datatypes with fewer than `2 ^ 32` constructors and fields (tags and block sizes fit a word) -/
def Small (S : Sig) : Prop := ∀ i, S.nc i < 2 ^ 32 ∧ ∀ j, (S.flds i j).length < 2 ^ 32

theorem rep_w {m : Ir.Mem} {x : BitVec 64} {a : Val} (h : Rep m (.w x) a) : a = .w x := by
  simpa only [Rep] using h

theorem upd_lt {g : VReg → Val} {n d : Nat} (hd : n ≤ d) (v : Val) : ∀ r : Nat, r < n → upd g d v r = g r :=
  fun r hr => upd_ne _ _ (show r ≠ d by omega)

section
variable {P : Prog} {Q : Ir.Prog VReg}

theorem ex_lowPrim {g : VReg → Val} (m : Ir.Mem) (o : Prim) (n a b : Nat) {x y : BitVec 64} (ha : g a = .w x)
    (hb : g b = .w y) : ∃ g', SC.Ex Q (lowPrim o n a b) g m g' m ∧ g' n = .w (o.eval x y) ∧
      ∀ r : Nat, r < n → g' r = g r := by
  cases o with
  | op o => exact ⟨_, ex_op m o n (.r a) (.r b) (by simp [Arg.eval, ha]) (by simp [Arg.eval, hb]), upd_same _ _ _,
      upd_lt (Nat.le_refl n) _⟩
  | mul => exact ⟨_, ex_mop m .mul n a b ha hb, upd_same _ _ _, upd_lt (Nat.le_refl n) _⟩
  | urem => exact ⟨_, ex_mop m .remu n a b ha hb, upd_same _ _ _, upd_lt (Nat.le_refl n) _⟩
  | udiv =>
    by_cases hy : y = 0
    · subst hy
      refine ⟨_, .iteT (by simp [Tst.eval, Arg.eval, hb, Cond.eval]) (ex_setK g m n 0), ?_, upd_lt (Nat.le_refl n) _⟩
      simp [Prim.eval, BitVec.udiv_zero]
    · refine ⟨_, .iteF (by simp [Tst.eval, Arg.eval, hb, Cond.eval]; exact hy) (ex_mop m .divu n a b ha hb), ?_,
        upd_lt (Nat.le_refl n) _⟩
      simp [Prim.eval, MOp.eval]; intro h; exact absurd h hy

theorem bv_xor (c : Bool) : bv c ^^^ 1 = bv (!c) := by cases c <;> decide

theorem ex_lowCmp {g : VReg → Val} (m : Ir.Mem) (c : Cmp) (n a b : Nat) {x y : BitVec 64} (ha : g a = .w x)
    (hb : g b = .w y) : ∃ g', SC.Ex Q (lowCmp c n a b) g m g' m ∧ g' n = .w (bv (c.eval x y)) ∧
      ∀ r : Nat, r < n → g' r = g r := by
  have hA : (Arg.r a : Arg VReg).eval g = .w x := by simp [Arg.eval, ha]
  have hB : (Arg.r b : Arg VReg).eval g = .w y := by simp [Arg.eval, hb]
  have two : ∀ (o : Op) (A B : Arg VReg) (u w : BitVec 64), A.eval g = .w u → B.eval g = .w w →
      ∃ g', SC.Ex Q (.seq (opK o n A B) (opK .xor n (.r n) (.i 1))) g m g' m ∧ g' n = .w (o.eval u w ^^^ 1) ∧
        ∀ r : Nat, r < n → g' r = g r := by
    intro o A B u w hu hw
    refine ⟨_, .seq (ex_op m o n A B hu hw) (ex_op m .xor n (.r n) (.i 1) (x := o.eval u w) (y := 1) (by simp [Arg.eval]) rfl), by
      simp [Op.eval], fun r hr => by rw [upd_lt (Nat.le_refl n) _ r hr, upd_lt (Nat.le_refl n) _ r hr]⟩
  cases c with
  | eq => exact ⟨_, ex_op m .eq n _ _ hA hB, by simp [Op.eval, bv, Cmp.eval], upd_lt (Nat.le_refl n) _⟩
  | ult => exact ⟨_, ex_op m .ult n _ _ hA hB, by simp [Op.eval, bv, Cmp.eval], upd_lt (Nat.le_refl n) _⟩
  | slt => exact ⟨_, ex_op m .slt n _ _ hA hB, by simp [Op.eval, bv, Cmp.eval]; rfl, upd_lt (Nat.le_refl n) _⟩
  | ne =>
    obtain ⟨g', h1, h2, h3⟩ := two .eq _ _ x y hA hB
    refine ⟨g', h1, ?_, h3⟩
    rw [h2]; congr 1
    have : Op.eval .eq x y = bv (x == y) := by simp [Op.eval, bv]
    rw [this, bv_xor]; simp [Cmp.eval, bne]
  | ule =>
    obtain ⟨g', h1, h2, h3⟩ := two .ult _ _ y x hB hA
    refine ⟨g', h1, ?_, h3⟩
    rw [h2]; congr 1
    have : Op.eval .ult y x = bv (decide (y < x)) := by simp [Op.eval, bv]
    rw [this, bv_xor]; simp only [Cmp.eval]; congr 1
    rcases Decidable.em (x ≤ y) with hxy | hxy
    · have : ¬ y < x := BitVec.not_lt.2 hxy; simp [hxy, this]
    · have : y < x := BitVec.not_le.1 hxy; simp [hxy, this]
  | sle =>
    obtain ⟨g', h1, h2, h3⟩ := two .slt _ _ y x hB hA
    refine ⟨g', h1, ?_, h3⟩
    rw [h2]; congr 1
    have : Op.eval .slt y x = bv (y.slt x) := by simp [Op.eval, bv]
    rw [this, bv_xor]; simp [Cmp.eval, BitVec.sle_eq_not_slt]

theorem ex_alloc {g : VReg → Val} (m : Ir.Mem) (d : VReg) (c : BitVec 64) :
    SC.Ex Q (.i (.alloc d (.i c))) g m (upd g d (.p (m.blks.length + 2) 0)) (m.withBlk (List.replicate c.toNat none)) :=
  .i (e := [.alloc c.toNat]) (fun _ _ _ h => nomatch h) (by
    simp [Inst.exec, Arg.word, Arg.eval, Ir.Mem.withBlk])

/-- a call of a lowered function -/
theorem fn_returns (hQ : HasFns P Q) (f : Fin P.S.fns.length) {vs : List V} {v : V} {m : Ir.Mem}
    (ih : ∀ (ρ : List VReg) (n : Nat) (g : VReg → Val) (m : Ir.Mem), EnvR m vs ρ g → (∀ r : Nat, r ∈ ρ → r < n) →
      ∃ g' m', SC.Ex Q (low (P.body f) ρ n) g m g' m' ∧ Grow m m' ∧ Rep m' v (g' n) ∧ ∀ r : Nat, r < n → g' r = g r)
    (vals : List Val) (hl : vs.length = vals.length) (hk : vs.length = (P.S.fn f).1.length)
    (hr : ∀ k (h₁ : k < vs.length) (h₂ : k < vals.length), Rep m vs[k] vals[k]) :
    ∃ x m', Returns Q f.val vals m [x] m' ∧ Grow m m' ∧ Rep m' v x := by
  generalize hK : (P.S.fn f).1.length = K at hk
  have hF : Q.funcs[f.val]? = some (lowFn P f) := hQ f
  generalize hFF : lowFn P f = F at hF
  have hFdef : F = mkFunc (List.range K) (List.range K) 1 [(0, fnTC (P.body f))] := by rw [← hFF, ← hK]; rfl
  generalize hg0 : setMany (fun _ => Val.w 0) (List.range K) vals = g0
  have henv : EnvR m vs (List.range K) g0 := by
    refine ⟨by simp [hk], fun i h₁ h₂ => ?_⟩
    rw [← hg0, setMany_nodup _ _ _ List.nodup_range (by simp; omega) i h₂ (by omega)]
    exact hr i h₁ (by omega)
  obtain ⟨g', m', x1, gr, rp, -⟩ := ih (List.range K) K g0 m henv (fun r hr => by simpa using hr)
  have xT : TC.Ex Q F (fnTC (P.body f)) g0 m (.ret [g' K] m') := by
    have e : (P.S.fn f).1.length = K := hK
    unfold fnTC; rw [e]
    exact .seq x1 .ret
  obtain ⟨nl', ok⟩ := mkFunc_region (params := List.range K) (ps := List.range K) (nl := 1)
    (rs := [(0, fnTC (P.body f))]) (by simp) (by simp) 0 (by simp)
  rw [← hFdef] at ok
  simp only [List.getElem_cons_zero, if_true] at ok
  obtain ⟨l', pc', g'', B, rvs, hR, hB, hk', ht, hv⟩ := flatT_ok hF _ xT _ ok
  refine ⟨g' K, m', ⟨F, hF, by rw [hFdef]; show vals.length = (List.range K).length; simp; omega,
    l', pc', g'', B, rvs, ?_, hB, hk', ht, hv⟩, gr, rp⟩
  rw [hFdef]
  rw [← hg0] at hR
  exact hR

/-- **the lowering is correct**: a derivation of `e`'s value is a run of `low e`, which writes only registers
`≥ n`, grows memory, and leaves the value's representation in register `n` -/
theorem low_ok (hQ : HasFns P Q) (hS : Small P.S) {Γ : List Ty} {τ : Ty} {env : List V} {e : Expr P.S Γ τ} {v : V}
    (h : Ev P env e v) : ∀ (ρ : List VReg) (n : Nat) (g : VReg → Val) (m : Ir.Mem), EnvR m env ρ g →
      (∀ r : Nat, r ∈ ρ → r < n) → ∃ g' m', SC.Ex Q (low e ρ n) g m g' m' ∧ Grow m m' ∧ Rep m' v (g' n) ∧
        ∀ r : Nat, r < n → g' r = g r := by
  induction h with
  | var hx =>
    intro ρ n g m he hb
    obtain ⟨hr, -⟩ := he.get hx
    exact ⟨_, _, ex_mov g m n _, Grow.refl m, by rw [upd_same]; exact hr, upd_lt (Nat.le_refl n) _⟩
  | lit =>
    intro ρ n g m he hb
    exact ⟨_, _, ex_setK g m n _, Grow.refl m, by rw [upd_same]; rfl, upd_lt (Nat.le_refl n) _⟩
  | blit =>
    intro ρ n g m he hb
    exact ⟨_, _, ex_setK g m n _, Grow.refl m, by rw [upd_same]; rfl, upd_lt (Nat.le_refl n) _⟩
  | bin ha hb' =>
    intro ρ n g m he hb
    obtain ⟨g', x1, h1, h2⟩ := ex_lowPrim (Q := Q) m _ n _ _ (rep_w (he.get ha).1) (rep_w (he.get hb').1)
    exact ⟨g', m, x1, Grow.refl m, by rw [h1]; rfl, h2⟩
  | cmp ha hb' =>
    intro ρ n g m he hb
    obtain ⟨g', x1, h1, h2⟩ := ex_lowCmp (Q := Q) m _ n _ _ (rep_w (he.get ha).1) (rep_w (he.get hb').1)
    exact ⟨g', m, x1, Grow.refl m, by rw [h1]; rfl, h2⟩
  | bnot ha =>
    intro ρ n g m he hb
    have hA := rep_w (he.get ha).1
    exact ⟨_, m, ex_op m .xor n _ (.i 1) (by simp only [Arg.eval, reg]; exact hA) rfl, Grow.refl m,
      by rw [upd_same]; rfl, upd_lt (Nat.le_refl n) _⟩
  | let_ _ _ ih₁ ih₂ =>
    intro ρ n g m he hb
    obtain ⟨g1, m1, x1, gr1, rp1, f1⟩ := ih₁ ρ n g m he hb
    have he2 : EnvR m1 (_ :: _) (n :: ρ) g1 :=
      (he.mono gr1.1 (fun r hr => f1 r (hb r hr))).cons rp1
    obtain ⟨g2, m2, x2, gr2, rp2, f2⟩ := ih₂ (n :: ρ) (n + 1) g1 m1 he2 (fun r hr => by
      simp only [List.mem_cons] at hr
      rcases hr with hr | hr
      · omega
      · have := hb r hr; omega)
    refine ⟨_, m2, .seq x1 (.seq x2 (ex_mov g2 m2 n (n + 1))), gr1.trans gr2, by rw [upd_same]; exact rp2,
      fun r hr => ?_⟩
    rw [upd_lt (Nat.le_refl n) _ r hr, f2 r (by omega), f1 r hr]
  | iteT hc hx _ ih =>
    intro ρ n g m he hb
    have hC := rep_w (he.get hc).1
    obtain ⟨g', m', x1, r1⟩ := ih ρ n g m he hb
    exact ⟨g', m', .iteT (by simp only [Tst.eval, Arg.eval, reg, hC]; simp [Cond.eval]; exact hx) x1, r1⟩
  | iteF hc _ ih =>
    intro ρ n g m he hb
    have hC := rep_w (he.get hc).1
    obtain ⟨g', m', x1, r1⟩ := ih ρ n g m he hb
    exact ⟨g', m', .iteF (by simp only [Tst.eval, Arg.eval, reg, hC]; simp [Cond.eval]) x1, r1⟩
  | @mk Γ env i j vs xs hv =>
    intro ρ n g m he hb
    obtain ⟨hvl, hvr⟩ := vars_rep he hv
    generalize hL : xs.idxs.length = L at hvl
    have hLs : L < 2 ^ 32 := by rw [← hL, Vars.get_length]; exact (hS i).2 j
    have hc : (BitVec.ofNat 64 (L + 1)).toNat = L + 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have x1 := ex_alloc (Q := Q) (g := g) m n (BitVec.ofNat 64 (L + 1))
    rw [hc] at x1
    generalize hg1 : upd g n (.p (m.blks.length + 2) 0) = g1 at x1
    have hg1n : g1 n = .p (m.blks.length + 2) 0 := by rw [← hg1, upd_same]
    have x2 := ex_st_blk (Q := Q) (g := g1) m (List.replicate (L + 1) none) n hg1n
      (.i (BitVec.ofNat 64 j)) 0 (by simp)
    generalize hrs : xs.idxs.map (ρ.getD · 0) = rs
    have hrl : rs.length = L := by rw [← hrs, List.length_map, hL]
    have x3 := ex_stFs (Q := Q) m n hg1n rs 1
      ((List.replicate (L + 1) none).set 0 (some ((Arg.i (BitVec.ofNat 64 j) : Arg VReg).eval g1))) (by simp [hrl]; omega)
    have hcs : ((List.replicate (L + 1) (none : Option Val)).set 0 (some ((Arg.i (BitVec.ofNat 64 j) : Arg VReg).eval g1))).take 1 ++
        rs.map (fun r => some (g1 r)) ++ ((List.replicate (L + 1) none).set 0 (some ((Arg.i (BitVec.ofNat 64 j) : Arg VReg).eval g1))).drop (1 + rs.length) =
        some (.w (BitVec.ofNat 64 j)) :: rs.map (fun r => some (g1 r)) := by
      simp [List.replicate_succ, Arg.eval, hrl, Nat.add_comm 1 L]
    rw [hcs] at x3
    have hlow : low (Expr.mk (S := P.S) i j xs) ρ n = .seq (.i (.alloc n (.i (BitVec.ofNat 64 (L + 1)))))
        (.seq (.i (.st (.i (BitVec.ofNat 64 j)) n 0)) (stFs n 1 rs)) := by
      simp only [low, hL, hrs]
    have hg1r : ∀ r : Nat, r < n → g1 r = g r := fun r hr => by rw [← hg1]; exact upd_lt (Nat.le_refl n) _ r hr
    have gr := withBlk_grow m (some (.w (BitVec.ofNat 64 j)) :: rs.map (fun r => some (g1 r)))
    refine ⟨g1, _, by rw [hlow]; exact .seq x1 (.seq x2 x3), gr, ?_, hg1r⟩
    refine ⟨_, m.cells.length, hg1n, ?_, ?_, RepL.of_get fun k hk => ?_⟩
    · rw [withBlk_blk]; simp [hrl, hvl]
    · simp [Ir.Mem.withBlk]
    · have hkr : k < rs.length := by omega
      have hki : k < xs.idxs.length := by omega
      refine ⟨g1 rs[k], ?_, ?_⟩
      · simp only [Ir.Mem.withBlk]
        rw [List.getElem?_append_right (by omega), show m.cells.length + 1 + k - m.cells.length = k + 1 by omega]
        simp [hkr]
      · have hrk : rs[k] = ρ.getD xs.idxs[k] 0 := by subst hrs; simp
        obtain ⟨r1, r2⟩ := hvr k hk hki
        rw [hrk, hg1r _ (hb _ r2)]
        exact Rep.mono gr.1 _ _ r1
  | @cas Γ τ env i j fs v x arms hj hx hfl _ ih =>
    intro ρ n g m he hb
    obtain ⟨hrx, hxm⟩ := he.get hx
    obtain ⟨b, c0, hgx, hblk, htag, hRL⟩ := (by simpa only [Rep] using hrx :
      ∃ b c0, g (ρ.getD x.idx 0) = .p b 0 ∧ m.blk b = some (c0, fs.length + 1) ∧
        m.cells[c0]? = some (some (.w (BitVec.ofNat 64 j))) ∧ RepL m fs (c0 + 1))
    have hxn : ρ.getD x.idx 0 < n := hb _ hxm
    -- the tag
    have x1 : SC.Ex Q (.i (.ld (n + 1) (reg ρ x) 0)) g m (upd g (n + 1) (.w (BitVec.ofNat 64 j))) m :=
      .i (e := []) (fun _ _ _ h => nomatch h) (by simp only [Inst.exec, reg]; rw [hgx]; simp [hblk, htag])
    generalize hg1 : upd g (n + 1) (.w (BitVec.ofNat 64 j)) = g1 at x1
    have hg1r : ∀ r : Nat, r < n + 1 → g1 r = g r := fun r hr => by rw [← hg1]; exact upd_lt (Nat.le_refl _) _ r hr
    -- the fields
    generalize hM : (P.S.fld i ⟨j, hj⟩).length = M at hfl
    have hgx1 : g1 (ρ.getD x.idx 0) = .p b 0 := by rw [hg1r _ (Nat.lt_succ_of_lt hxn), hgx]
    obtain ⟨g2, x2, f2, r2⟩ := ex_ldFs (Q := Q) hgx1 hblk hRL (n + 2) (Nat.lt_of_lt_of_le hxn (Nat.le_add_right n 2))
      fs.length (Nat.le_refl _)
    have he2 : EnvR m (fs ++ env) (fregs (n + 2) M ++ ρ) g2 := by
      refine (he.mono (MLe.refl m) (fun r hr => by rw [f2 r (by have := hb r hr; omega), hg1r r (by
        have := hb r hr; omega)])).append (by simp [fregs, hfl]) (fun k h₁ h₂ => ?_)
      have : (fregs (n + 2) M)[k] = n + 2 + k := by simp [fregs]
      rw [this]; exact r2 k h₁ h₁
    obtain ⟨g3, m3, x3, gr3, rp3, f3⟩ := ih (fregs (n + 2) M ++ ρ) (n + 2 + M) g2 m he2 (fun r hr => by
      simp only [List.mem_append, fregs, List.mem_map, List.mem_range] at hr
      rcases hr with ⟨a, ha, rfl⟩ | hr
      · omega
      · have := hb r hr; omega)
    have x4 := ex_mov (P := Q) g3 m3 n (n + 2 + M)
    have xarm : SC.Ex Q (.seq (ldFs (reg ρ x) (n + 2) (P.S.fld i ⟨j, hj⟩).length)
        (.seq (low (arms ⟨j, hj⟩) (fregs (n + 2) (P.S.fld i ⟨j, hj⟩).length ++ ρ) (n + 2 + (P.S.fld i ⟨j, hj⟩).length))
          (mov n (n + 2 + (P.S.fld i ⟨j, hj⟩).length)))) g1 m (upd g3 n (g3 (n + 2 + M))) m3 := by
      rw [hfl] at x2; rw [hM]; exact .seq x2 (.seq x3 x4)
    have hjs : j < 2 ^ 32 := Nat.lt_trans hj (hS i).1
    have xc := ex_chain (Q := Q) (t := n + 1) (g := g1) (m := m) (List.ofFn fun (j' : Fin (P.S.nc i)) =>
        SC.seq (ldFs (reg ρ x) (n + 2) (P.S.fld i j').length)
          (SC.seq (low (arms j') (fregs (n + 2) (P.S.fld i j').length ++ ρ) (n + 2 + (P.S.fld i j').length))
            (mov n (n + 2 + (P.S.fld i j').length)))) 0 j (by simp [hj])
      (by rw [← hg1, upd_same, Nat.zero_add]) (fun i' hi' => by
        simp only [Nat.zero_add]
        intro he'
        have := congrArg BitVec.toNat he'
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega) (by simpa using xarm)
    refine ⟨_, m3, .seq x1 xc, gr3, by rw [upd_same]; exact rp3, fun r hr => ?_⟩
    rw [upd_lt (Nat.le_refl n) _ r hr, f3 r (by omega), f2 r (by omega), hg1r r (by omega)]
  | @call Γ τ env vs v f xs hτ hv _ ih =>
    intro ρ n g m he hb
    obtain ⟨hvl, hvr⟩ := vars_rep he hv
    have hk : vs.length = (P.S.fn f).1.length := by rw [hvl, Vars.get_length]
    obtain ⟨x, m', hR, gr, rp⟩ := fn_returns hQ f ih (xs.idxs.map fun k => g (ρ.getD k 0)) (by simp [hvl]) hk
      (fun k h₁ h₂ => by simpa using (hvr k h₁ (by simpa using h₂)).1)
    have hargs : (xs.idxs.map fun k => (Arg.r (ρ.getD k 0) : Arg VReg)).map (Arg.eval g) =
        xs.idxs.map fun k => g (ρ.getD k 0) := by simp [Arg.eval]
    refine ⟨upd g n x, m', ?_, gr, by rw [upd_same]; exact rp, upd_lt (Nat.le_refl n) _⟩
    have := SC.Ex.call (P := Q) (ds := [n]) (g := g) (by rw [hargs]; exact hR) rfl
    simpa [low, setMany] using this

end

end Proven.S3

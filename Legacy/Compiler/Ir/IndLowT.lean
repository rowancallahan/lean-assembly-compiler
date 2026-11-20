/- The correctness of the inductive path's lowering to RTL, part 3: an arm (`lowT`, tail position) either returns its
value or jumps to the entry with a child (a tail call), and a whole function (`lowPg`) returns `Pg.sem` (by induction
on the depth of the node: a tail call runs the entry again on a child). -/
import Legacy.Compiler.Ir.IndLowE

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

variable {P : Prog VReg} {rk : Kd}

/-- how an arm ends: it returns its value, or it jumps to the entry with a child of the node (the value is then the
recursive call's) -/
def TRes (f : Bool → BitVec 64 → C → rk.den) (l r : C) (m : Mem) {k : Kd} (y : k.den) : Out → Prop
  | .ret vs m' => ∃ v, vs = [v] ∧ MLe m m' ∧ m'.out = m.out ∧ RvK k m' v y
  | .go lb g' m' => lb = 0 ∧ MLe m m' ∧ m'.out = m.out ∧ ∃ (h : rk = k) (ch : Bool) (a' : BitVec 64) (b' : C),
      Rv m' (g' 0) (if ch then r else l) ∧ g' 1 = .w a' ∧ Rv m' (g' 2) b' ∧ y = h ▸ f ch a' b'

section
variable (fi : FId) (xk : List Kd) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) (F : Func VReg)

theorem tok_ret {k : Kd} {e : E rk k} {self : Cn rk} {ρ : List Nat} {n : Nat} {g : VReg → Val} {m : Mem}
    (hlow : lowT fi ρ e n = .seq (lowE fi ρ e n (n + 1)) (.term (.ret [.r n])))
    (h : EOk P (lowE fi ρ e n (n + 1)) g m n (n + 1) (ev self x l r a b e)) :
    ∃ o, TC.Ex P F (lowT fi ρ e n) g m o ∧ TRes self.f l r m (ev self x l r a b e) o := by
  obtain ⟨g', m', hx, ml, ho, hr, -⟩ := h
  exact ⟨.ret [g' n] m', by rw [hlow]; exact .seq hx .ret, ⟨g' n, rfl, ml, ho, hr⟩⟩

/-- **an arm's code returns its value or makes its tail call** -/
theorem lowT_ok (hF0 : ∃ B, F.blocks.lookup 0 = some B ∧ B.params = [0, 1, 2]) :
    ∀ {k : Kd} (e : E rk k) (self : Cn rk) (ks : List Kd) (ρ : List Nat) (n : Nat) (g : VReg → Val) (m : Mem),
    e.okc ks xk = true → e.tags < 256 → 7 ≤ n → (∀ q ∈ ρ, q < n) →
    Regs self x l r a b g m → Binds ks ρ self.ρ g m → Calls P fi xk self l r →
    ∃ o, TC.Ex P F (lowT fi ρ e n) g m o ∧ TRes self.f l r m (ev self x l r a b e) o := by
  intro k e
  induction e with
  | call ch ea eb iha ihb =>
    intro self ks ρ n g m hok ht hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := lowE_ok fi xk x l r a b ea self ks ρ n (n + 1) g m hok.1 (by omega)
      (by omega) (by omega) (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := lowE_ok fi xk x l r a b eb self ks ρ (n + 1) (n + 2) g₁ m₁ hok.2
      (by omega) (by omega) (by omega) (fun q hq => by have := hρ q hq; omega) hR₁
      (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))) hC
    have hR₂ := hR₁.step ml₂ (fun q hq => f₂ q (by omega) (by omega))
    have hv : Rv m₂ (g₂ (if ch then 6 else 5)) (if ch then r else l) := by
      cases ch
      · exact hR₂.2.2.2.2.1
      · exact hR₂.2.2.2.2.2
    have h1 : g₂ n = .w (ev self x l r a b ea) := by rw [f₂ n (by omega) (by omega)]; exact r₁
    obtain ⟨B, hB0, hp⟩ := hF0
    refine ⟨_, .seq (.seq x₁ x₂) (.jmp hB0 (by rw [hp]; rfl)), rfl, ml₁.trans ml₂, by rw [o₂, o₁], rfl, ch, ev self x l r a b ea, ev self x l r a b eb, ?_⟩
    simp only [hp, List.map, Arg.eval, setMany, upd, h1]
    exact ⟨by simpa using hv, rfl, r₂, rfl⟩
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    intro self ks ρ n g m hok ht hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := lowE_ok fi xk x l r a b c self ks ρ n (n + 1) g m hok.1.1 (by omega)
      (by omega) (by omega) (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    have hB₁ := hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))
    have hz := nz_w (x := n) (g := g₁) r₁
    have post : ∀ {k : Kd} {y : k.den} {o : Out}, TRes self.f l r m₁ y o → TRes self.f l r m y o := by
      intro k y o h
      cases o with
      | ret vs m' => obtain ⟨v, e, ml, ho, hr⟩ := h; exact ⟨v, e, ml₁.trans ml, by rw [ho, o₁], hr⟩
      | go lb g' m' => obtain ⟨e, ml, ho, rest⟩ := h; exact ⟨e, ml₁.trans ml, by rw [ho, o₁], rest⟩
    simp only [lowT]
    by_cases hc0 : ev self x l r a b c = 0
    · obtain ⟨o, xo, ro⟩ := ih₂ self ks ρ (n + 1) g₁ m₁ hok.2 (by omega) (by omega)
        (fun q hq => by have := hρ q hq; omega) hR₁ hB₁ hC
      refine ⟨o, .seq x₁ (.iteF (by rw [hz, hc0]; rfl) xo), ?_⟩
      simp only [ev, hc0, if_true]; exact post ro
    · obtain ⟨o, xo, ro⟩ := ih₁ self ks ρ (n + 1) g₁ m₁ hok.1.2 (by omega) (by omega)
        (fun q hq => by have := hρ q hq; omega) hR₁ hB₁ hC
      refine ⟨o, .seq x₁ (.iteT (by rw [hz, decide_eq_false hc0]; rfl) xo), ?_⟩
      simp only [ev, hc0, if_false]; exact post ro
  | @bind k₁ k e₁ e₂ ih₁ ih₂ =>
    intro self ks ρ n g m hok ht hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := lowE_ok fi xk x l r a b e₁ self ks ρ n (n + 1) g m hok.1 (by omega)
      (by omega) (by omega) (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    have hB₁ := hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))
    have hB' : Binds (k₁ :: ks) (n :: ρ) ({ self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } : Cn rk).ρ g₁ m₁ := by
      intro i kk hk
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
        exact ⟨n, _, rfl, rfl, by rw [Kd.pick_pair]; exact r₁⟩
      | succ i => exact hB₁ i kk (by simpa using hk)
    obtain ⟨o, xo, ro⟩ := ih₂ { self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } (k₁ :: ks) (n :: ρ) (n + 1)
      g₁ m₁ hok.2 (by omega) (by omega)
      (fun q hq => by
        rcases List.mem_cons.1 hq with e | e
        · omega
        · have := hρ q e; omega) hR₁ hB' hC
    simp only [lowT]
    refine ⟨o, .seq x₁ xo, ?_⟩
    cases o with
    | ret vs m' => obtain ⟨v, e, ml, ho, hr⟩ := ro; exact ⟨v, e, ml₁.trans ml, by rw [ho, o₁], hr⟩
    | go lb g' m' => obtain ⟨e, ml, ho, rest⟩ := ro; exact ⟨e, ml₁.trans ml, by rw [ho, o₁], rest⟩
  | _ =>
    intro self ks ρ n g m hok ht hn hρ hR hB hC
    exact tok_ret fi x l r a b F rfl (lowE_ok fi xk x l r a b _ self ks ρ n (n + 1) g m hok ht (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC)

end

/-! ## a whole function -/

/-- the context of an arm of `pg` at the node `c t x l r` (as in `Pg.sem`) -/
def cnOf (pg : Pg rk) (t : Nat) (x : BitVec 64) (l r : C) : Cn rk :=
  ⟨fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b',
    fun c₁ c₂ a' b' => if c₁ then (match r with
        | .z => rk.dflt
        | .c _ _ rl rr => if c₂ then pg.sem rr a' b' else pg.sem rl a' b')
      else (match l with
        | .z => rk.dflt
        | .c _ _ ll lr => if c₂ then pg.sem lr a' b' else pg.sem ll a' b'),
    pg.X, .c t x l r, []⟩

theorem sem_c (pg : Pg rk) (t : Nat) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) :
    pg.sem (.c t x l r) a b = match pg.arms[t]? with
      | some e => ev (cnOf pg t x l r) x l r a b e
      | none => rk.dflt := by rw [Pg.sem]; rfl

theorem sem_z (pg : Pg rk) (a : BitVec 64) (b : C) : pg.sem .z a b = rk.dflt := by rw [Pg.sem]

theorem cnOf_g (pg : Pg rk) (t : Nat) (x : BitVec 64) (l r : C) (c₁ c₂ : Bool) (a' : BitVec 64) (b' : C) :
    (cnOf pg t x l r).g c₁ c₂ a' b' = pg.sem ((if c₂ then C.rv else C.lv) (if c₁ then r else l)) a' b' := by
  cases c₁ <;> cases c₂ <;> simp only [cnOf, Bool.false_eq_true, if_false, if_true] <;> split <;> rfl

theorem depth_lv (c : C) : c.lv.depth ≤ c.depth := by cases c <;> simp [C.lv, C.depth] <;> omega
theorem depth_rv (c : C) : c.rv.depth ≤ c.depth := by cases c <;> simp [C.rv, C.depth] <;> omega

/-- the function returns `y` from the entry -/
def FRet (P : Prog VReg) (fi : FId) (F : Func VReg) (g : VReg → Val) (m : Mem) (k : Kd) (y : k.den) : Prop :=
  ∃ res m', EndsAt P fi F 0 0 g m (.ret [res] m') ∧ MLe m m' ∧ m'.out = m.out ∧ RvK k m' res y

theorem fret_returns {fi : FId} {F : Func VReg} (hF : P.funcs[fi]? = some F) (hp : F.params = [0, 1, 2])
    (he : F.entry = 0) {v vb : Val} {a : BitVec 64} {mm : Mem} {k : Kd} {y : k.den}
    (h : FRet P fi F (setMany (fun _ => .w 0) [0, 1, 2] [v, .w a, vb]) mm k y) : RetOk P fi [v, .w a, vb] mm k y := by
  obtain ⟨res, m', ⟨l', pc', g', B, rvs, hR, hB, hk, ht, hv⟩, ml, ho, hr⟩ := h
  exact ⟨res, m', ⟨F, hF, by rw [hp]; rfl, l', pc', g', B, rvs, by rw [he, hp]; exact hR, hB, hk, ht, hv⟩, ml, ho, hr⟩

theorem regs0 (v vb : Val) (a : BitVec 64) :
    let g := setMany (fun _ => Val.w 0) [0, 1, 2] [v, .w a, vb]; g 0 = v ∧ g 1 = .w a ∧ g 2 = vb := by
  simp [setMany, upd]

theorem lowPg_eq (fi : FId) (pg : Pg rk) : lowPg fi pg = mkFunc [0, 1, 2] [0, 1, 2] (pg.arms.length + 2)
    (rs3 (entryTC pg.arms.length) pg.arms (fun e => lowT fi [] e 7) (.term (.ret [.i 0]))) := rfl

/-- **a function's code returns `Pg.sem`** (any node, by induction on its depth) -/
theorem pg_ok (fi : FId) (xk : List Kd) (pg : Pg rk) (hF : P.funcs[fi]? = some (lowPg fi pg))
    (hok : ∀ e ∈ pg.arms, e.tags < 256 ∧ e.okc [] xk = true)
    (hX : ∀ (j : Nat) (hj : j < xk.length) (t' : C) (a' : BitVec 64) (b' : C) (vt vb : Val) (mm : Mem), Rv mm vt t' →
      Rv mm vb b' → RetOk P (fi + 1 + j) [vt, .w a', vb] mm xk[j] (xk[j].pick (pg.X j t' a' b'))) :
    ∀ (N : Nat) (c : C), c.depth < N → ∀ (a : BitVec 64) (b : C) (g : VReg → Val) (m : Mem), Rv m (g 0) c → g 1 = .w a →
      Rv m (g 2) b → FRet P fi (lowPg fi pg) g m rk (pg.sem c a b) := by
  intro N
  induction N with
  | zero => intro c hc; omega
  | succ N ih =>
  intro c hc a b g m h0 h1 h2
  rw [lowPg_eq] at hF ⊢
  generalize hFF : mkFunc [0, 1, 2] [0, 1, 2] (pg.arms.length + 2)
    (rs3 (entryTC pg.arms.length) pg.arms (fun e => lowT fi [] e 7) (.term (.ret [.i 0]))) = F at hF ⊢
  have ok0 := rs3_ok0 [0, 1, 2] (entryTC pg.arms.length) pg.arms (fun e => lowT fi [] e 7) (.term (.ret [.i 0]))
  have okE := rs3_okE [0, 1, 2] (entryTC pg.arms.length) pg.arms (fun e => lowT fi [] e 7) (.term (.ret [.i 0]))
  have okj := rs3_okj [0, 1, 2] (entryTC pg.arms.length) pg.arms (fun e => lowT fi [] e 7) (.term (.ret [.i 0]))
  rw [hFF] at ok0 okE okj
  have hFp : F.params = [0, 1, 2] := by rw [← hFF]; rfl
  have hFe : F.entry = 0 := by rw [← hFF]; rfl
  obtain ⟨n0, ok0⟩ := ok0
  obtain ⟨nE, okE⟩ := okE
  have hF0 : ∃ B, F.blocks.lookup 0 = some B ∧ B.params = [0, 1, 2] := ok_open_block (flatT_start _ _ ok0)
  have hFE : ∃ B, F.blocks.lookup (pg.arms.length + 1) = some B ∧ B.params = [] := ok_open_block (flatT_start _ _ okE)
  have hFj : ∀ j (hj : j < pg.arms.length), ∃ B, F.blocks.lookup (j + 1) = some B ∧ B.params = [] := fun j hj =>
    let ⟨_, h⟩ := okj j hj; ok_open_block (flatT_start _ _ h)
  -- the default region: `ret 0`
  have retE : EndsAt P fi F (pg.arms.length + 1) 0 g m (.ret [.w 0] m) := by
    have := flatT_ok hF (.term (.ret [.i 0])) (g := g) (m := m) .ret _ okE
    exact this
  cases c with
  | z =>
    have hz : g 0 = .w 0 := by generalize g 0 = v0 at h0; cases h0; rfl
    have := flatT_ok hF (entryTC pg.arms.length) (g := g) (m := m) (.iteF (by rw [nz_w hz]; rfl) .ret) _ ok0
    exact ⟨.w 0, m, this, MLe.refl m, rfl, by rw [sem_z]; exact RvK.dflt m rk⟩
  | c t x l r =>
    obtain ⟨bk, c0, vl, vr, hv, hb, ht, e0, e1, e2, e3, rl, rr⟩ := h0.inv
    -- the four loads
    have xl : SC.Ex P (.seqs [.i (.ld 3 0 0), .i (.ld 4 0 1), .i (.ld 5 0 2), .i (.ld 6 0 3)]) g m
        (upd (upd (upd (upd g 3 (.w (BitVec.ofNat 64 t))) 4 (.w x)) 5 vl) 6 vr) m := by
      simp only [SC.seqs]
      refine .seq (ex_ld hv hb (by decide) (by simpa using e0)) (.seq (ex_ld ?_ hb (by decide) e1)
        (.seq (ex_ld ?_ hb (by decide) e2) (ex_ld ?_ hb (by decide) e3)))
      · rw [upd_ne _ _ (by decide)]; exact hv
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hv
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hv
    generalize hg₁ : upd (upd (upd (upd g 3 (.w (BitVec.ofNat 64 t))) 4 (.w x)) 5 vl) 6 vr = g₁ at xl
    have hg₁q : ∀ q : Nat, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → g₁ q = g q := fun q a b c d => by
      rw [← hg₁, upd_ne _ _ d, upd_ne _ _ c, upd_ne _ _ b, upd_ne _ _ a]
    have g3 : g₁ 3 = .w (BitVec.ofNat 64 t) := by
      rw [← hg₁, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]
    have g4 : g₁ 4 = .w x := by rw [← hg₁, upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_same]
    have g5 : g₁ 5 = vl := by rw [← hg₁, upd_ne _ _ (by decide), upd_same]
    have g6 : g₁ 6 = vr := by rw [← hg₁, upd_same]
    have htn : (BitVec.ofNat 64 t).toNat = t := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    -- the switch
    have hL : ((List.range pg.arms.length).map (· + 1))[(BitVec.ofNat 64 t).toNat]?.getD (pg.arms.length + 1) =
        if t < pg.arms.length then t + 1 else pg.arms.length + 1 := by
      rw [htn]; split <;> simp [*]
    have hLB : ∃ B, F.blocks.lookup (if t < pg.arms.length then t + 1 else pg.arms.length + 1) = some B ∧ B.params = [] := by
      split
      · exact hFj t (by assumption)
      · exact hFE
    obtain ⟨BL, hBL, hpL⟩ := hLB
    have reach : Reach P fi 0 0 g m (if t < pg.arms.length then t + 1 else pg.arms.length + 1) 0 g₁ m := by
      have := flatT_ok hF (entryTC pg.arms.length) (g := g) (m := m)
        (.iteT (nz_p hv) (.seq xl (.sw g3 (by rw [hL]; exact hBL) hpL))) _ ok0
      rw [hL] at this; exact this
    by_cases hta : t < pg.arms.length
    · simp only [hta, if_true] at reach
      obtain ⟨nj, okt⟩ := okj t hta
      have he : pg.arms[t]? = some pg.arms[t] := List.getElem?_eq_getElem hta
      obtain ⟨tg, tk⟩ := hok pg.arms[t] (List.getElem_mem hta)
      have ihF : ∀ (c' : C), c'.depth < N + 1 - 1 → ∀ (a' : BitVec 64) (b' : C) (g' : VReg → Val) (m' : Mem),
          Rv m' (g' 0) c' → g' 1 = .w a' → Rv m' (g' 2) b' → FRet P fi F g' m' rk (pg.sem c' a' b') := by
        intro c' hc' a' b' g' m' r0 r1 r2
        have := ih c' (by omega) a' b' g' m' r0 r1 r2
        rw [lowPg_eq, hFF] at this; exact this
      have hdl : l.depth < N := by simp [C.depth] at hc; omega
      have hdr : r.depth < N := by simp [C.depth] at hc; omega
      have hC : Calls P fi xk (cnOf pg t x l r) l r := by
        refine ⟨fun ch a' b' v vb mm hv' hb' => ?_, fun c₁ c₂ a' b' v vb mm hv' hb' => ?_, hX⟩
        · have := ihF (if ch then r else l) (by cases ch <;> simpa) a' b' _ mm hv' (regs0 v vb a').2.1
            hb'
          have e : pg.sem (if ch then r else l) a' b' = (cnOf pg t x l r).f ch a' b' := by cases ch <;> rfl
          rw [e] at this
          exact fret_returns hF hFp hFe this
        · have hd : ((if c₂ then C.rv else C.lv) (if c₁ then r else l)).depth < N + 1 - 1 := by
            have := depth_lv (if c₁ then r else l); have := depth_rv (if c₁ then r else l)
            cases c₁ <;> cases c₂ <;> simp at * <;> omega
          have := ihF _ hd a' b' _ mm hv' (regs0 v vb a').2.1 hb'
          rw [← cnOf_g pg t x l r c₁ c₂ a' b'] at this
          exact fret_returns hF hFp hFe this
      have hR : Regs (cnOf pg t x l r) x l r a b g₁ m :=
        ⟨by rw [hg₁q 0 (by decide) (by decide) (by decide) (by decide)]; exact h0,
          by rw [hg₁q 1 (by decide) (by decide) (by decide) (by decide)]; exact h1,
          by rw [hg₁q 2 (by decide) (by decide) (by decide) (by decide)]; exact h2, g4, by rw [g5]; exact rl,
          by rw [g6]; exact rr⟩
      have hB : Binds [] [] (cnOf pg t x l r).ρ g₁ m := fun i k h => by simp at h
      obtain ⟨o, xo, ro⟩ := lowT_ok fi xk x l r a b F hF0 pg.arms[t] (cnOf pg t x l r) [] [] 7 g₁ m tk tg (by omega)
        (by simp) hR hB hC
      have endo := flatT_ok hF _ xo _ okt
      rw [sem_c, he]
      dsimp only
      cases o with
      | ret vs m' =>
        obtain ⟨v, rfl, ml, ho, hr⟩ := ro
        exact ⟨v, m', EndsAt.pre reach endo, ml, ho, hr⟩
      | go lb g' m' =>
        obtain ⟨rfl, ml, ho, hh, ch, a', b', r0, r1, r2, hy⟩ := ro
        cases hh
        obtain ⟨res, m'', en, ml', ho', hr'⟩ := ihF (if ch then r else l) (by cases ch <;> simpa) a' b' g' m' r0 r1 r2
        refine ⟨res, m'', EndsAt.pre (reach.trans endo) en, ml.trans ml', by rw [ho', ho], ?_⟩
        rw [hy]; cases ch <;> exact hr'
    · simp only [hta, if_false] at reach
      have he : pg.arms[t]? = none := List.getElem?_eq_none (by omega)
      rw [sem_c, he]
      have retE' : EndsAt P fi F (pg.arms.length + 1) 0 g₁ m (.ret [.w 0] m) := by
        have := flatT_ok hF (.term (.ret [.i 0])) (g := g₁) (m := m) .ret _ okE
        exact this
      exact ⟨.w 0, m, EndsAt.pre reach retE', MLe.refl m, rfl, RvK.dflt m rk⟩

end Proven.Ir.IndLow

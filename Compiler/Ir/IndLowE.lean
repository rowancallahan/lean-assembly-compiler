/- The correctness of the inductive path's lowering to RTL, part 2: an expression (`lowE`) computes its value (`ev`)
into its destination register, given the registers of the arm (`Regs`), the `let` values (`Binds`) and the calls it
makes (`Calls`: recursive calls on children and grandchildren, the later functions). -/
import Compiler.Ir.IndLowMem

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

variable {P : Prog VReg} {rk : Kd}

/-- the registers of an arm: `0` node, `1` word, `2` tree, `4` x, `5` l, `6` r -/
def Regs (self : Cn rk) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) (g : VReg → Val) (m : Mem) : Prop :=
  Rv m (g 0) self.me ∧ g 1 = .w a ∧ Rv m (g 2) b ∧ g 4 = .w x ∧ Rv m (g 5) l ∧ Rv m (g 6) r

/-- the `let` values: binder `i` of kind `ks[i]` in register `ρ[i]` -/
def Binds (ks : List Kd) (ρ : List Nat) (vals : List (BitVec 64 × C)) (g : VReg → Val) (m : Mem) : Prop :=
  ∀ (i : Nat) (k : Kd), ks[i]? = some k → ∃ q v, ρ[i]? = some q ∧ vals[i]? = some v ∧ RvK k m (g q) (k.pick v)

/-- a call returns a value of kind `k` and only grows memory -/
def RetOk (P : Prog VReg) (f : FId) (args : List Val) (mm : Mem) (k : Kd) (y : k.den) : Prop :=
  ∃ res mm', Returns P f args mm [res] mm' ∧ MLe mm mm' ∧ mm'.out = mm.out ∧ RvK k mm' res y

/-- the calls of an arm: on a child, on a grandchild, of a later function -/
def Calls (P : Prog VReg) (fi : FId) (xk : List Kd) (self : Cn rk) (l r : C) : Prop :=
  (∀ (ch : Bool) (a' : BitVec 64) (b' : C) (v vb : Val) (mm : Mem), Rv mm v (if ch then r else l) → Rv mm vb b' →
    RetOk P fi [v, .w a', vb] mm rk (self.f ch a' b')) ∧
  (∀ (c₁ c₂ : Bool) (a' : BitVec 64) (b' : C) (v vb : Val) (mm : Mem),
    Rv mm v ((if c₂ then C.rv else C.lv) (if c₁ then r else l)) → Rv mm vb b' →
    RetOk P fi [v, .w a', vb] mm rk (self.g c₁ c₂ a' b')) ∧
  (∀ (j : Nat) (hj : j < xk.length) (t' : C) (a' : BitVec 64) (b' : C) (vt vb : Val) (mm : Mem), Rv mm vt t' →
    Rv mm vb b' → RetOk P (fi + 1 + j) [vt, .w a', vb] mm xk[j] (xk[j].pick (self.X j t' a' b')))

theorem Regs.step {self : Cn rk} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {g g' : VReg → Val} {m m' : Mem}
    (h : Regs self x l r a b g m) (hm : MLe m m') (hg : ∀ q : Nat, q < 7 → g' q = g q) : Regs self x l r a b g' m' := by
  obtain ⟨h0, h1, h2, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg 0 (by decide)]; exact h0.mono hm
  · rw [hg 1 (by decide)]; exact h1
  · rw [hg 2 (by decide)]; exact h2.mono hm
  · rw [hg 4 (by decide)]; exact h4
  · rw [hg 5 (by decide)]; exact h5.mono hm
  · rw [hg 6 (by decide)]; exact h6.mono hm

theorem Binds.step {ks : List Kd} {ρ : List Nat} {vals : List (BitVec 64 × C)} {g g' : VReg → Val} {m m' : Mem}
    (h : Binds ks ρ vals g m) (hm : MLe m m') (hg : ∀ q ∈ ρ, g' q = g q) : Binds ks ρ vals g' m' := by
  unfold Binds at *
  intro i k hk
  obtain ⟨q, v, hq, hv, hr⟩ := h i k hk
  refine ⟨q, v, hq, hv, ?_⟩
  rw [hg q (List.mem_of_getElem? hq)]; exact hr.mono hm

theorem setMany_one (g : VReg → Val) (d : VReg) (v : Val) : setMany g [d] [v] = upd g d v := rfl

theorem tags_lt {n a b : Nat} (h : max a b < n) : a < n ∧ b < n := ⟨by omega, by omega⟩

theorem ex_mkCell' {g : VReg → Val} {m : Mem} {d : VReg} {t x l r : Arg VReg} {vt vx vl vr : Val}
    (ht : t.eval (upd g d (.p (m.blks.length + 2) 0)) = vt) (hx : x.eval (upd g d (.p (m.blks.length + 2) 0)) = vx)
    (hl : l.eval (upd g d (.p (m.blks.length + 2) 0)) = vl) (hr : r.eval (upd g d (.p (m.blks.length + 2) 0)) = vr) :
    SC.Ex P (mkCell d t x l r) g m (upd g d (.p (m.blks.length + 2) 0)) (m.push4 vt vx vl vr) := by
  have := ex_mkCell (P := P) g m d t x l r
  rw [ht, hx, hl, hr] at this; exact this

theorem okc_ext {ks xk : List Kd} {j : Nat} {kk : Kd} (h : (xk[j]? == some kk) = true) : ∃ hj : j < xk.length, xk[j] = kk := by
  have h' : xk[j]? = some kk := by simpa using h
  exact List.getElem?_eq_some_iff.1 h'

section
variable (fi : FId) (xk : List Kd) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C)

/-- what an expression's code does: its value in `d`, memory grows, the output stays, registers below `n` other than
`d` stay -/
def EOk (P : Prog VReg) {k : Kd} (sc : SC) (g : VReg → Val) (m : Mem) (d n : Nat) (y : k.den) : Prop :=
  ∃ g' m', SC.Ex P sc g m g' m' ∧ MLe m m' ∧ m'.out = m.out ∧ RvK k m' (g' d) y ∧ ∀ q : Nat, q ≠ d → q < n → g' q = g q

theorem eok_mov {g : VReg → Val} {m : Mem} {k : Kd} {y : k.den} (d s n : Nat) (h : RvK k m (g s) y) :
    EOk P (mov d s) g m d n y :=
  ⟨_, m, ex_mov g m d s, MLe.refl m, rfl, by rw [upd_same]; exact h, fun q hq _ => upd_ne g _ hq⟩

theorem eok_setK {g : VReg → Val} {m : Mem} {k : Kd} {y : k.den} (d n : Nat) (c : BitVec 64) (h : RvK k m (.w c) y) :
    EOk P (setK d c) g m d n y :=
  ⟨_, m, ex_setK g m d c, MLe.refl m, rfl, by rw [upd_same]; exact h, fun q hq _ => upd_ne g _ hq⟩

/-- **an expression's code computes its value** -/
theorem lowE_ok : ∀ {k : Kd} (e : E rk k) (self : Cn rk) (ks : List Kd) (ρ : List Nat) (d n : Nat) (g : VReg → Val)
    (m : Mem), e.okc ks xk = true → e.tags < 256 → d < n → 7 ≤ n → (∀ q ∈ ρ, q < n) →
    Regs self x l r a b g m → Binds ks ρ self.ρ g m → Calls P fi xk self l r →
    EOk P (lowE fi ρ e d n) g m d n (ev self x l r a b e) := by
  intro k e
  induction e with
  | x => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 4 n hR.2.2.2.1
  | a => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 1 n hR.2.1
  | k c => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_setK d n c rfl
  | l => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 5 n hR.2.2.2.2.1
  | r => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 6 n hR.2.2.2.2.2
  | b => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 2 n hR.2.2.1
  | nul => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_setK d n 0 Rv.z
  | me => intro self ks ρ d n g m _ _ hd hn hρ hR hB hC; exact eok_mov d 0 n hR.1
  | var i kk =>
    intro self ks ρ d n g m hok _ hd hn hρ hR hB hC
    have hk : ks[i]? = some kk := by simpa [E.okc] using hok
    obtain ⟨q, v, hq, hv, hr⟩ := hB i kk hk
    have e1 : ρ.getD i 0 = q := by simp [List.getD_eq_getElem?_getD, hq]
    have e2 : self.ρ.getD i (0, .z) = v := by simp [List.getD_eq_getElem?_getD, hv]
    simp only [lowE, ev, e1, e2]
    exact eok_mov d q n hr
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ih₁ self ks ρ n (n + 1) g m hok.1 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ih₂ self ks ρ (n + 1) (n + 2) g₁ m₁ hok.2 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) (hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega)))
      (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))) hC
    have h1 : g₂ n = .w (ev self x l r a b e₁) := by rw [f₂ n (by omega) (by omega)]; exact r₁
    simp only [lowE, SC.seqs]
    refine ⟨_, m₂, .seq x₁ (.seq x₂ (ex_bin m₂ op d n (n + 1) h1 r₂)), ml₁.trans ml₂, o₂.trans o₁,
      by rw [upd_same]; rfl, fun q hq hqn => ?_⟩
    rw [upd_ne _ _ hq, f₂ q (by omega) (by omega), f₁ q (by omega) (by omega)]
  | mk t ex el er ihx ihl ihr =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    have hρ' : ∀ j, ∀ q ∈ ρ, q < n + j := fun j q hq => by have := hρ q hq; omega
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ihx self ks ρ n (n + 1) g m hok.1.1 (by omega) (by omega) (by omega)
      (hρ' 1) hR hB hC
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ihl self ks ρ (n + 1) (n + 2) g₁ m₁ hok.1.2 (by omega) (by omega)
      (by omega) (hρ' 2) (hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega)))
      (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))) hC
    have hR₂ := (hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))).step ml₂ (fun q hq => f₂ q (by omega) (by omega))
    have hB₂ := (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))).step ml₂
      (fun q hq => by have := hρ q hq; exact f₂ q (by omega) (by omega))
    obtain ⟨g₃, m₃, x₃, ml₃, o₃, r₃, f₃⟩ := ihr self ks ρ (n + 2) (n + 3) g₂ m₂ hok.2 (by omega) (by omega)
      (by omega) (hρ' 3) hR₂ hB₂ hC
    have e0 : g₃ n = .w (ev self x l r a b ex) := by
      rw [f₃ n (by omega) (by omega), f₂ n (by omega) (by omega)]; exact r₁
    have e1 : g₃ (n + 1) = g₂ (n + 1) := f₃ _ (by omega) (by omega)
    obtain ⟨hle, hrv⟩ := mkCell_rv (t := t) (x := ev self x l r a b ex) (by omega)
      ((show Rv m₂ (g₂ (n + 1)) (ev self x l r a b el) from r₂).mono ml₃) (show Rv m₃ (g₃ (n + 2)) _ from r₃)
    simp only [lowE, SC.seqs]
    refine ⟨_, _, .seq x₁ (.seq x₂ (.seq x₃ (ex_mkCell' (vt := .w (BitVec.ofNat 64 t)) (vx := g₃ n) (vl := g₃ (n + 1))
      (vr := g₃ (n + 2)) rfl (by simp only [Arg.eval]; exact upd_ne _ _ (by omega))
      (by simp only [Arg.eval]; exact upd_ne _ _ (by omega)) (by simp only [Arg.eval]; exact upd_ne _ _ (by omega))))),
      ml₁.trans (ml₂.trans (ml₃.trans ?_)), ?_, ?_, fun q hq hqn => ?_⟩
    · rw [e0, e1]; exact hle
    · show m₃.out = m.out; rw [o₃, o₂, o₁]
    · rw [upd_same, e0, e1]; exact hrv
    · rw [upd_ne _ _ hq, f₃ q (by omega) (by omega), f₂ q (by omega) (by omega), f₁ q (by omega) (by omega)]
  | call ch ea eb iha ihb =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := iha self ks ρ n (n + 1) g m hok.1 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ihb self ks ρ (n + 1) (n + 2) g₁ m₁ hok.2 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR₁
      (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))) hC
    have hR₂ := hR₁.step ml₂ (fun q hq => f₂ q (by omega) (by omega))
    have hv : Rv m₂ (g₂ (if ch then 6 else 5)) (if ch then r else l) := by
      cases ch
      · exact hR₂.2.2.2.2.1
      · exact hR₂.2.2.2.2.2
    have h1 : g₂ n = .w (ev self x l r a b ea) := by rw [f₂ n (by omega) (by omega)]; exact r₁
    obtain ⟨res, m₃, hret, ml₃, o₃, r₃⟩ := hC.1 ch _ _ _ _ m₂ hv r₂
    simp only [lowE, SC.seqs]
    refine ⟨_, m₃, .seq x₁ (.seq x₂ (.call (vs := [res]) ?_ rfl)), ml₁.trans (ml₂.trans ml₃), by rw [o₃, o₂, o₁],
      by rw [setMany_one, upd_same]; exact r₃, fun q hq hqn => ?_⟩
    · simp only [List.map, Arg.eval, h1]; exact hret
    · rw [setMany_one, upd_ne _ _ hq, f₂ q (by omega) (by omega), f₁ q (by omega) (by omega)]
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ihc self ks ρ n (n + 1) g m hok.1.1 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    have hB₁ := hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))
    have hz := nz_w (x := n) (g := g₁) r₁
    simp only [lowE]
    by_cases hc0 : ev self x l r a b c = 0
    · obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ih₂ self ks ρ d (n + 1) g₁ m₁ hok.2 (by omega) (by omega) (by omega)
        (fun q hq => by have := hρ q hq; omega) hR₁ hB₁ hC
      refine ⟨g₂, m₂, .seq x₁ (.iteF (by rw [hz, hc0]; rfl) x₂), ml₁.trans ml₂, by rw [o₂, o₁], ?_,
        fun q hq hqn => by rw [f₂ q hq (by omega), f₁ q (by omega) (by omega)]⟩
      simp only [ev, hc0, if_true]; exact r₂
    · obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ih₁ self ks ρ d (n + 1) g₁ m₁ hok.1.2 (by omega) (by omega) (by omega)
        (fun q hq => by have := hρ q hq; omega) hR₁ hB₁ hC
      refine ⟨g₂, m₂, .seq x₁ (.iteT (by rw [hz, decide_eq_false hc0]; rfl) x₂), ml₁.trans ml₂, by rw [o₂, o₁], ?_,
        fun q hq hqn => by rw [f₂ q hq (by omega), f₁ q (by omega) (by omega)]⟩
      simp only [ev, hc0, if_false]; exact r₂
  | fw i e ih =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ih self ks ρ n (n + 1) g m hok ht (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    obtain ⟨w, xw, h0, h1, -, -⟩ := ex_fld (P := P) (d := d) r₁ (if i then 1 else 0) (by split <;> omega)
      (if i then 0 else 255)
    simp only [lowE]
    refine ⟨_, m₁, .seq x₁ xw, ml₁, o₁, ?_, fun q hq hqn => by rw [upd_ne _ _ hq, f₁ q (by omega) (by omega)]⟩
    rw [upd_same]
    cases i
    · exact h0 rfl rfl
    · exact h1 rfl rfl
  | ft ch e ih =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ih self ks ρ n (n + 1) g m hok ht (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    obtain ⟨w, xw, -, -, h2, h3⟩ := ex_fld (P := P) (d := d) r₁ (if ch then 3 else 2) (by split <;> omega) 0
    simp only [lowE]
    refine ⟨_, m₁, .seq x₁ xw, ml₁, o₁, ?_, fun q hq hqn => by rw [upd_ne _ _ hq, f₁ q (by omega) (by omega)]⟩
    rw [upd_same]
    cases ch
    · exact h2 rfl rfl
    · exact h3 rfl rfl
  | ext j kk et ea eb iht iha ihb =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨hj, hjk⟩ := okc_ext (ks := ks) hok.1.1.1
    subst hjk
    have hρ' : ∀ j, ∀ q ∈ ρ, q < n + j := fun j q hq => by have := hρ q hq; omega
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := iht self ks ρ n (n + 1) g m hok.1.1.2 (by omega) (by omega) (by omega)
      (hρ' 1) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    have hB₁ := hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := iha self ks ρ (n + 1) (n + 2) g₁ m₁ hok.1.2 (by omega) (by omega)
      (by omega) (hρ' 2) hR₁ hB₁ hC
    have hR₂ := hR₁.step ml₂ (fun q hq => f₂ q (by omega) (by omega))
    have hB₂ := hB₁.step ml₂ (fun q hq => by have := hρ q hq; exact f₂ q (by omega) (by omega))
    obtain ⟨g₃, m₃, x₃, ml₃, o₃, r₃, f₃⟩ := ihb self ks ρ (n + 2) (n + 3) g₂ m₂ hok.2 (by omega) (by omega)
      (by omega) (hρ' 3) hR₂ hB₂ hC
    have e0 : g₃ n = g₁ n := by rw [f₃ n (by omega) (by omega), f₂ n (by omega) (by omega)]
    have e1 : g₃ (n + 1) = .w (ev self x l r a b ea) := by rw [f₃ _ (by omega) (by omega)]; exact r₂
    have rt : Rv m₃ (g₃ n) (ev self x l r a b et) := by rw [e0]; exact (r₁.mono ml₂).mono ml₃
    obtain ⟨res, m₄, hret, ml₄, o₄, r₄⟩ := hC.2.2 j hj _ _ _ _ _ m₃ rt r₃
    simp only [lowE, SC.seqs]
    refine ⟨_, m₄, .seq x₁ (.seq x₂ (.seq x₃ (.call (vs := [res]) ?_ rfl))), ml₁.trans (ml₂.trans (ml₃.trans ml₄)),
      by rw [o₄, o₃, o₂, o₁], by rw [setMany_one, upd_same]; exact r₄, fun q hq hqn => ?_⟩
    · simp only [List.map, Arg.eval, e1]; exact hret
    · rw [setMany_one, upd_ne _ _ hq, f₃ q (by omega) (by omega), f₂ q (by omega) (by omega),
        f₁ q (by omega) (by omega)]
  | @bind k₁ k e₁ e₂ ih₁ ih₂ =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := ih₁ self ks ρ n (n + 1) g m hok.1 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    have hB₁ := hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))
    have hB' : Binds (k₁ :: ks) (n :: ρ) ({ self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } : Cn rk).ρ g₁ m₁ := by
      intro i kk hk
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
        exact ⟨n, _, rfl, rfl, by rw [Kd.pick_pair]; exact r₁⟩
      | succ i => exact hB₁ i kk (by simpa using hk)
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ih₂ { self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } (k₁ :: ks)
      (n :: ρ) d (n + 1) g₁ m₁ hok.2 (by omega) (by omega) (by omega)
      (fun q hq => by
        rcases List.mem_cons.1 hq with e | e
        · omega
        · have := hρ q e; omega) hR₁ hB' hC
    simp only [lowE]
    exact ⟨g₂, m₂, .seq x₁ x₂, ml₁.trans ml₂, by rw [o₂, o₁], r₂,
      fun q hq hqn => by rw [f₂ q hq (by omega), f₁ q (by omega) (by omega)]⟩
  | call2 c₁ c₂ ea eb iha ihb =>
    intro self ks ρ d n g m hok ht hd hn hρ hR hB hC
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [E.tags] at ht
    obtain ⟨g₁, m₁, x₁, ml₁, o₁, r₁, f₁⟩ := iha self ks ρ n (n + 1) g m hok.1 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR hB hC
    have hR₁ := hR.step ml₁ (fun q hq => f₁ q (by omega) (by omega))
    obtain ⟨g₂, m₂, x₂, ml₂, o₂, r₂, f₂⟩ := ihb self ks ρ (n + 1) (n + 2) g₁ m₁ hok.2 (by omega) (by omega) (by omega)
      (fun q hq => by have := hρ q hq; omega) hR₁
      (hB.step ml₁ (fun q hq => by have := hρ q hq; exact f₁ q (by omega) (by omega))) hC
    have hR₂ := hR₁.step ml₂ (fun q hq => f₂ q (by omega) (by omega))
    have hv : Rv m₂ (g₂ (if c₁ then 6 else 5)) (if c₁ then r else l) := by
      cases c₁
      · exact hR₂.2.2.2.2.1
      · exact hR₂.2.2.2.2.2
    obtain ⟨w, xw, -, -, h2, h3⟩ := ex_fld (P := P) (d := n + 2) hv (if c₂ then 3 else 2) (by split <;> omega) 0
    have hw : Rv m₂ w ((if c₂ then C.rv else C.lv) (if c₁ then r else l)) := by
      cases c₂
      · exact h2 rfl rfl
      · exact h3 rfl rfl
    have h1 : upd g₂ (n + 2) w n = .w (ev self x l r a b ea) := by
      rw [upd_ne _ _ (by omega), f₂ n (by omega) (by omega)]; exact r₁
    have h1' : upd g₂ (n + 2) w (n + 1) = g₂ (n + 1) := upd_ne _ _ (by omega)
    obtain ⟨res, m₃, hret, ml₃, o₃, r₃⟩ := hC.2.1 c₁ c₂ _ _ _ _ m₂ hw r₂
    simp only [lowE, SC.seqs]
    refine ⟨_, m₃, .seq x₁ (.seq x₂ (.seq xw (.call (vs := [res]) ?_ rfl))), ml₁.trans (ml₂.trans ml₃),
      by rw [o₃, o₂, o₁], by rw [setMany_one, upd_same]; exact r₃, fun q hq hqn => ?_⟩
    · simp only [List.map, Arg.eval, h1, h1', upd_same]; exact hret
    · rw [setMany_one, upd_ne _ _ hq, upd_ne _ _ (by omega), f₂ q (by omega) (by omega), f₁ q (by omega) (by omega)]

end

end Proven.Ir.IndLow

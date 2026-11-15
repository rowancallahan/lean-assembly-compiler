/- Correctness of `indProg` (`Compiler/Ind.lean`) at the source level (`CExec`), once and for all. -/
import Compiler.Ind
import Compiler.Rec

set_option linter.unusedVariables false

namespace Proven.Mach.Ind
open Proven.Mach

/-! ## the heap invariant -/

structure HI (W : List (BitVec 64)) (h : Nat) : Prop where
  z0 : Z0 W
  h4 : 4 ≤ h
  hal : h % 4 = 0
  hle : h ≤ W.length
  big : W.length < 2 ^ 60

def RelK (W : List (BitVec 64)) (h : Nat) : (k : Kd) → BitVec 64 → k.den → Prop
  | .w, v, y => v = y
  | .t, v, y => Rp W h v y

theorem RelK.mono {W W' : List (BitVec 64)} {h h' : Nat} {k : Kd} {v : BitVec 64} {y : k.den}
    (r : RelK W h k v y) (hh : h ≤ h') (ha : Agree W W' h) : RelK W' h' k v y := by
  cases k
  · exact r
  · exact Rp.mono r hh ha

theorem RelK.dflt (W : List (BitVec 64)) (h : Nat) (k : Kd) : RelK W h k 0 k.dflt := by
  cases k
  · rfl
  · exact .z

theorem toNat_h {h : Nat} (hh : h < 2 ^ 60) : (BitVec.ofNat 64 h).toNat = h := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem addE_den {env : BEnv} {i h c : Nat} (hi : env i = BitVec.ofNat 64 h) (hb : h + c < 2 ^ 60) :
    ((addE i c).denote env).toNat = h + c := by
  simp only [addE, kE, BExp.denote, Op.eval, hi]
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem addE_den' {env : BEnv} {i h c : Nat} (hi : env i = BitVec.ofNat 64 h) :
    (addE i c).denote env = BitVec.ofNat 64 (h + c) := by
  simp only [addE, kE, BExp.denote, Op.eval, hi]; rw [← BitVec.ofNat_add]

theorem Rp.lt4 {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {v : C} (hr : Rp W h p v) (h4 : 4 ≤ h) :
    p.toNat < h := by
  rcases hr.lt with e | e
  · exact e
  · subst e; simp; omega

/-! ## small steps -/

theorem asg_exec (v : Nat) (e : BExp) (σ : BState) :
    BExec (asg v e) σ ⟨σ.env.set v (e.denote σ.env), σ.heap, σ.wheap⟩ := .assign

theorem stW_exec {env : BEnv} {H : Heap} {W : List (BitVec 64)} {h : Nat} (i : Nat) (e : BExp)
    (h5 : env 5 = BitVec.ofNat 64 h) (hb : h + i < W.length) (hW : W.length < 2 ^ 60) :
    BExec (stW i e) ⟨env, H, [W]⟩ ⟨env, H, [W.set (h + i) (e.denote env)]⟩ := by
  have hd := addE_den (i := 5) (c := i) h5 (by omega)
  have := BExec.store64 (b := 0) (i := addE 5 i) (e := e) (σ := ⟨env, H, [W]⟩) (by simp) (by
    show ((addE 5 i).denote env).toNat < W.length; omega)
  simp only [List.getElem_cons_zero, hd] at this
  exact this

/-- the cell `[t, x, l, r]` at `h` -/
def put (W : List (BitVec 64)) (h : Nat) (t x l r : BitVec 64) : List (BitVec 64) :=
  (((W.set h t).set (h + 1) x).set (h + 2) l).set (h + 3) r

theorem put_length (W : List (BitVec 64)) (h : Nat) (t x l r : BitVec 64) : (put W h t x l r).length = W.length := by
  simp [put]

theorem put_get (W : List (BitVec 64)) (h : Nat) (t x l r : BitVec 64) (i : Nat) :
    (put W h t x l r)[i]? = if i = h + 3 ∧ i < W.length then some r else if i = h + 2 ∧ i < W.length then some l
      else if i = h + 1 ∧ i < W.length then some x else if i = h ∧ i < W.length then some t else W[i]? := by
  simp only [put, List.getElem?_set, List.length_set]
  repeat' split
  all_goals first | rfl | omega | (subst_vars; simp_all) | simp_all

theorem put_agree (W : List (BitVec 64)) (h : Nat) (t x l r : BitVec 64) : Agree W (put W h t x l r) h :=
  fun i hi => by rw [put_get]; repeat' split
                 all_goals first | rfl | omega

theorem alloc_exec {env : BEnv} {H : Heap} {W : List (BitVec 64)} {h : Nat} (t : BExp) (vx vl vr d : Nat)
    (hd : d ≠ 5) (h5 : env 5 = BitVec.ofNat 64 h) (hb : h + 4 ≤ W.length) (hW : W.length < 2 ^ 60) :
    BExec (alloc t vx vl vr d) ⟨env, H, [W]⟩
      ⟨(env.set d (BitVec.ofNat 64 h)).set 5 (BitVec.ofNat 64 (h + 4)), H,
        [put W h (t.denote env) (env vx) (env vl) (env vr)]⟩ := by
  refine .seq (stW_exec 0 t h5 (by omega) hW) (.seq (stW_exec 1 _ h5 (by simp; omega) (by simp; omega))
    (.seq (stW_exec 2 _ h5 (by simp; omega) (by simp; omega)) (.seq (stW_exec 3 _ h5 (by simp; omega) (by simp; omega))
    (.seq (asg_exec _ _ _) ?_))))
  have := asg_exec 5 (addE 5 4) ⟨env.set d ((vE 5).denote env), H, [put W h (t.denote env) (env vx) (env vl) (env vr)]⟩
  simp only [vE, BExp.denote] at this ⊢
  rw [addE_den' (h := h) (by rw [set_ne' _ _ (by omega), h5])] at this
  simp only [put, Nat.add_zero, h5] at this ⊢
  exact this

/-- a fresh cell represents its value -/
theorem Rp_put {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {t : Nat} {x pl pr : BitVec 64} {l r : C}
    (ht : t < 256) (hb : h + 4 ≤ W.length) (rl : Rp W h pl l) (rr : Rp W h pr r) :
    Rp (put W h (BitVec.ofNat 64 t) x pl pr) (h + 4) (BitVec.ofNat 64 h) (.c t x l r) := by
  have hh := toNat_h (h := h) (by have := hi.big; omega)
  have := hi.h4; have := hi.hal
  have ll := rl.lt4 hi.h4; have lr := rr.lt4 hi.h4
  refine .c (by omega) (by omega) (by omega) ht ?_ ?_ ?_ ?_ (by omega) (by omega)
    (rl.mono (by omega) (put_agree W h _ x pl pr)) (rr.mono (by omega) (put_agree W h _ x pl pr)) <;> rw [hh] <;>
  (rw [put_get]; repeat' split
   all_goals first | rfl | omega)

theorem HI_put {W : List (BitVec 64)} {h : Nat} (hi : HI W h) (hb : h + 4 ≤ W.length) (t x l r : BitVec 64) :
    HI (put W h t x l r) (h + 4) := by
  have z := hi.z0; have := hi.h4
  refine ⟨?_, by omega, by have := hi.hal; omega, by rw [put_length]; omega, by rw [put_length]; exact hi.big⟩
  have a := put_agree W h t x l r
  exact ⟨by rw [a 0 (by omega)]; exact z.1, by rw [a 1 (by omega)]; exact z.2.1, by rw [a 2 (by omega)]; exact z.2.2.1,
    by rw [a 3 (by omega)]; exact z.2.2.2⟩

/-! ## expressions -/

/-- what a run keeps: the block length, the cells below `h`, the invariant, the bump pointer `h'` in `v_5`,
the other globals -/
structure Post (W : List (BitVec 64)) (h : Nat) (W' : List (BitVec 64)) (h' : Nat) (g E' : BEnv) : Prop where
  len : W'.length = W.length
  agr : Agree W W' h
  hi : HI W' h'
  hle : h ≤ h'
  e5 : E' 5 = BitVec.ofNat 64 h'
  glob : ∀ i, i < 8 → i ≠ 5 → E' i = g i

theorem Post.trans {W₁ W₂ W₃ : List (BitVec 64)} {h₁ h₂ h₃ : Nat} {g₁ g₂ g₃ : BEnv}
    (p : Post W₁ h₁ W₂ h₂ g₁ g₂) (q : Post W₂ h₂ W₃ h₃ g₂ g₃) : Post W₁ h₁ W₃ h₃ g₁ g₃ :=
  ⟨q.len.trans p.len, p.agr.trans q.agr p.hle, q.hi, Nat.le_trans p.hle q.hle, q.e5,
    fun i hi h5 => (q.glob i hi h5).trans (p.glob i hi h5)⟩

variable {rk : Kd} (P : Prog) (pg : Pg rk)

/-- a call of `F` on `v` (at `pv`) runs within `K` bytes of stack -/
def BodyOK (K : Nat) (v : C) (pv : BitVec 64) : Prop :=
  ∀ (a bp : BitVec 64) (b : C) (g : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    HI W h → Rp W h pv v → Rp W h bp b → h + 4 * pg.al v a b ≤ W.length → g 5 = BitVec.ofNat 64 h →
    ∃ E' W', CExec P K (fFn pg).body ⟨callEnv g [pv, a, bp], H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a b) g E' ∧ RelK W' (h + 4 * pg.al v a b) rk (E' 12) (pg.sem v a b)

variable {P pg}

theorem call_body {f : Nat} (hf : f < P.length) {K K' : Nat} (hK : P[f].frame + K' ≤ K) {d : Nat}
    {args : List BExp} (ha : args.length = P[f].nparams) {σ σ₁ : BState}
    (hb : CExec P K' P[f].body ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ σ₁) :
    CExec P K (.call d f args) σ ⟨(retEnv σ.env σ₁.env).set d (P[f].ret.denote σ₁.env), σ₁.heap, σ₁.wheap⟩ :=
  .call hf ha hK hb

/-- the closures `Pg.sem` / `Pg.al` pass to the arms -/
def selfS (pg : Pg rk) (l r : C) : Bool → BitVec 64 → C → rk.den := fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b'
def selfA (pg : Pg rk) (l r : C) : Bool → BitVec 64 → C → Nat := fun ch a' b' => if ch then pg.al r a' b' else pg.al l a' b'

/-- the state an arm runs in -/
structure Cx (K' : Nat) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) (env : BEnv) (W : List (BitVec 64))
    (h : Nat) : Prop where
  hi : HI W h
  e5 : env 5 = BitVec.ofNat 64 h
  ex : env 14 = x
  ea : env 9 = a
  rl : Rp W h (env 15) l
  rr : Rp W h (env 16) r
  rb : Rp W h (env 10) b
  okl : BodyOK P pg K' l (env 15)
  okr : BodyOK P pg K' r (env 16)

theorem Cx.step {K' : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {env env' : BEnv}
    {W W' : List (BitVec 64)} {h h' : Nat} (c : Cx (P := P) (pg := pg) K' x l r a b env W h) (p : Post W h W' h' env env')
    (hk : ∀ i, i ∈ [9, 10, 14, 15, 16] → env' i = env i) : Cx (P := P) (pg := pg) K' x l r a b env' W' h' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k9, k10, k14, k15, k16⟩ := hk
  exact ⟨p.hi, p.e5, by rw [k14]; exact c.ex, by rw [k9]; exact c.ea, by rw [k15]; exact c.rl.mono p.hle p.agr,
    by rw [k16]; exact c.rr.mono p.hle p.agr, by rw [k10]; exact c.rb.mono p.hle p.agr, by rw [k15]; exact c.okl,
    by rw [k16]; exact c.okr⟩

theorem post_set {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {env : BEnv} (h5 : env 5 = BitVec.ofNat 64 h)
    {d : Nat} (hd : 8 ≤ d) (y : BitVec 64) : Post W h W h env (env.set d y) :=
  ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, by rw [set_ne' _ _ (by omega)]; exact h5,
    fun i hi _ => set_ne' _ _ (by omega)⟩

theorem fFn_body (pg : Pg rk) : (fFn pg).body = .seq (.base (asg 11 (kE 1))) (fLoop pg) := rfl

theorem call_ok (hP3 : ∃ hf : 3 < P.length, P[3] = fFn pg) {K K' : Nat} (hK : 136 + K' ≤ K) {v b' : C}
    {pv a' bp : BitVec 64} {d pvar avar bvar : Nat} (ok : BodyOK P pg K' v pv) {env : BEnv} {H : Heap}
    {W : List (BitVec 64)} {h : Nat} (hi : HI W h) (h5 : env 5 = BitVec.ofNat 64 h) (hp : env pvar = pv)
    (ha : env avar = a') (hb : env bvar = bp) (rv : Rp W h pv v) (rb : Rp W h bp b')
    (cap : h + 4 * pg.al v a' b' ≤ W.length) (hd : 8 ≤ d) :
    ∃ E' W', CExec P K (.call d 3 [vE pvar, vE avar, vE bvar]) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a' b') env E' ∧ (∀ i, 8 ≤ i → i ≠ d → E' i = env i) ∧
      RelK W' (h + 4 * pg.al v a' b') rk (E' d) (pg.sem v a' b') := by
  obtain ⟨hf3, hP⟩ := hP3
  obtain ⟨E'', W', hx, hpost, hrel⟩ := ok a' bp b' env H W h hi rv rb cap h5
  have hargs : [vE pvar, vE avar, vE bvar].map (·.denote env) = [pv, a', bp] := by
    simp [vE, BExp.denote, hp, ha, hb]
  have hc := call_body (P := P) (f := 3) (K := K) (K' := K') hf3 (by rw [hP]; exact hK) (d := d)
    (args := [vE pvar, vE avar, vE bvar]) (by rw [hP]; rfl) (σ := ⟨env, H, [W]⟩) (σ₁ := ⟨E'', H, [W']⟩)
    (by rw [hP]; simp only [hargs]; exact hx)
  rw [hP] at hc
  refine ⟨_, W', hc, ⟨hpost.len, hpost.agr, hpost.hi, hpost.hle, ?_, fun i hi h5' => ?_⟩, fun i hi hid => ?_, ?_⟩
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos (show 5 < 8 by omega)]; exact hpost.e5
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos hi]; exact hpost.glob i hi h5'
  · simp only; rw [set_ne' _ _ hid]; simp only [retEnv, if_neg (show ¬ i < 8 by omega)]
  · simp only; rw [set_eq']; exact hrel

theorem selfS_eq (pg : Pg rk) (l r : C) (ch : Bool) (a' : BitVec 64) (b' : C) :
    selfS pg l r ch a' b' = pg.sem (if ch then r else l) a' b' := by cases ch <;> rfl
theorem selfA_eq (pg : Pg rk) (l r : C) (ch : Bool) (a' : BitVec 64) (b' : C) :
    selfA pg l r ch a' b' = pg.al (if ch then r else l) a' b' := by cases ch <;> rfl

/-- **Expressions**: `comp e d n` leaves the value of `e` in `v_d`, allocates `alE e` cells, keeps the variables
below `n` other than `d` -/
theorem comp_ok (hP3 : ∃ hf : 3 < P.length, P[3] = fFn pg) {K K' : Nat} (hK : 136 + K' ≤ K)
    {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} :
    ∀ {k : Kd} (e : E rk k) (d n : Nat) (env : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
      8 ≤ d → d ∉ [9, 10, 14, 15, 16] → 17 ≤ n → e.tags < 256 → Cx (P := P) (pg := pg) K' x l r a b env W h →
      h + 4 * alE (selfS pg l r) (selfA pg l r) x l r a b e ≤ W.length →
      ∃ E' W', CExec P K (comp 3 e d n) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
        Post W h W' (h + 4 * alE (selfS pg l r) (selfA pg l r) x l r a b e) env E' ∧
        (∀ i, i < n → i ≠ d → 8 ≤ i → E' i = env i) ∧
        RelK W' (h + 4 * alE (selfS pg l r) (selfA pg l r) x l r a b e) k (E' d) (ev (selfS pg l r) x l r a b e) := by
  obtain ⟨hf3, hP⟩ := hP3
  intro k e
  induction e with
  | x | a | k _ | l | r | b | nul =>
    intro d n env H W h hd hdk hn htg c hcap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdk
    refine ⟨_, W, .base (asg_exec _ _ _), post_set c.hi c.e5 hd _, fun i _ hi _ => set_ne' _ _ hi, ?_⟩
    simp only [alE, Nat.mul_zero, Nat.add_zero, ev, set_eq', vE, kE, BExp.denote]
    first | exact c.ex | exact c.ea | rfl | exact c.rl | exact c.rr | exact c.rb | exact .z
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro d n env H W h hd hdk hn htg c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ih₁ n (n + 1) env H W h (by omega) (by simp; omega) (by omega) (by omega) c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₂ (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega) (by omega) (by omega) c₁
      (by have := p₁.len; omega)
    have p₂' := p₁.trans p₂
    refine ⟨_, W₂, .seq x₁ (.seq x₂ (.base (asg_exec _ _ _))), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₂'.trans (post_set p₂.hi p₂.e5 hd _)
    · dsimp only; rw [set_ne' _ _ hid, k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · simp only [RelK, ev, set_eq', vE, BExp.denote]
      rw [k₂ n (by omega) (by omega) (by omega)]
      simp only [RelK] at v₁ v₂; rw [v₁, v₂]
  | mk t ex el er ihx ihl ihr =>
    intro d n env H W h hd hdk hn htg c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ihx n (n + 1) env H W h (by omega) (by simp; omega) (by omega) (by omega) c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ihl (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega) (by omega) (by omega) c₁
      (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
    obtain ⟨E₃, W₃, x₃, p₃, k₃, v₃⟩ := ihr (n + 2) (n + 3) E₂ H W₂ _ (by omega) (by simp; omega) (by omega) (by omega) c₂
      (by have := p₁.len; have := p₂.len; omega)
    have p₃' := (p₁.trans p₂).trans p₃
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b ex = A1 at *
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b el = A2 at *
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b er = A3 at *
    have hb3 : h + 4 * A1 + 4 * A2 + 4 * A3 + 4 ≤ W₃.length := by rw [p₃'.len]; omega
    rw [show h + 4 * (A1 + A2 + A3 + 1) = h + 4 * A1 + 4 * A2 + 4 * A3 + 4 by omega]
    refine ⟨_, _, .seq x₁ (.seq x₂ (.seq x₃ (.base (alloc_exec _ _ _ _ d (by omega) p₃.e5 hb3 p₃.hi.big)))),
      ?_, fun i hi hid h8 => ?_, ?_⟩
    · refine ⟨by rw [put_length, p₃'.len], p₃'.agr.trans (put_agree W₃ _ _ _ _ _) p₃'.hle,
        HI_put p₃.hi hb3 _ _ _ _, by omega, by rw [set_eq'], fun i hi h5 => ?_⟩
      rw [set_ne' _ _ h5, set_ne' _ _ (by omega), p₃'.glob i hi h5]
    · rw [set_ne' _ _ (by omega), set_ne' _ _ hid, k₃ i (by omega) (by omega) h8, k₂ i (by omega) (by omega) h8,
        k₁ i (by omega) (by omega) h8]
    · simp only [RelK, ev]
      rw [set_ne' _ _ (by omega), set_eq']
      have e1 : E₃ n = ev (selfS pg l r) x l r a b ex := by
        rw [k₃ n (by omega) (by omega) (by omega), k₂ n (by omega) (by omega) (by omega)]; exact v₁
      have e2 := k₃ (n + 1) (by omega) (by omega) (by omega)
      have hkt : (kE t).denote E₃ = BitVec.ofNat 64 t := rfl
      rw [hkt, e1]
      have r2 : Rp W₃ (h + 4 * A1 + 4 * A2 + 4 * A3) (E₃ (n + 1)) (ev (selfS pg l r) x l r a b el) := by
        rw [e2]; exact v₂.mono p₃.hle p₃.agr
      exact Rp_put p₃.hi (by omega) hb3 (x := ev (selfS pg l r) x l r a b ex) r2 v₃
  | call ch ea eb iha ihb =>
    intro d n env H W h hd hdk hn htg c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := iha n (n + 1) env H W h (by omega) (by simp; omega) (by omega) (by omega) c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ihb (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega) (by omega) (by omega) c₁
      (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
    have p₂' := p₁.trans p₂
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b ea = A1 at *
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b eb = A2 at *
    rw [selfA_eq] at hcap ⊢; simp only [ev]; rw [selfS_eq]
    have hok : BodyOK P pg K' (if ch then r else l) (E₂ (if ch then 16 else 15)) := by cases ch <;>
      first | exact c₂.okl | exact c₂.okr
    have hrv : Rp W₂ (h + 4 * A1 + 4 * A2) (E₂ (if ch then 16 else 15)) (if ch then r else l) := by
      cases ch <;> first | exact c₂.rl | exact c₂.rr
    have ea' : E₂ n = ev (selfS pg l r) x l r a b ea := by
      rw [k₂ n (by omega) (by omega) (by omega)]; exact v₁
    have rb' : Rp W₂ (h + 4 * A1 + 4 * A2) (E₂ (n + 1)) (ev (selfS pg l r) x l r a b eb) := v₂
    obtain ⟨E₃, W₃, x₃, p₃, k₃, v₃⟩ := call_ok ⟨hf3, hP⟩ hK (d := d) hok p₂.hi p₂.e5 rfl ea' rfl hrv rb'
      (by rw [p₂'.len]; omega) hd
    refine ⟨_, W₃, .seq x₁ (.seq x₂ x₃), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r) x l r a b ea)
        (ev (selfS pg l r) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
        (ev (selfS pg l r) x l r a b ea) (ev (selfS pg l r) x l r a b eb) by omega]
      exact p₂'.trans p₃
    · rw [k₃ i h8 hid, k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r) x l r a b ea)
        (ev (selfS pg l r) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
        (ev (selfS pg l r) x l r a b ea) (ev (selfS pg l r) x l r a b eb) by omega]
      exact v₃
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    intro d n env H W h hd hdk hn htg cx hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ihc n (n + 1) env H W h (by omega) (by simp; omega) (by omega) (by omega) cx
      (by omega)
    have c₁ := cx.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
    simp only [RelK] at v₁
    simp only [ev]
    generalize alE (selfS pg l r) (selfA pg l r) x l r a b c = A1 at *
    by_cases hz : ev (selfS pg l r) x l r a b c = 0
    · rw [if_pos hz] at hcap ⊢; rw [if_pos hz]
      obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₂ d (n + 1) E₁ H W₁ _ hd hdk (by omega) (by omega) c₁
        (by have := p₁.len; omega)
      refine ⟨E₂, W₂, .seq x₁ (.iteF (by simp only [vE, BExp.denote]; rw [v₁, hz]) x₂), ?_, fun i hi hid h8 => ?_, ?_⟩
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans p₂
      · rw [k₂ i (by omega) hid h8, k₁ i (by omega) (by omega) h8]
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact v₂
    · rw [if_neg hz] at hcap ⊢; rw [if_neg hz]
      obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₁ d (n + 1) E₁ H W₁ _ hd hdk (by omega) (by omega) c₁
        (by have := p₁.len; omega)
      refine ⟨E₂, W₂, .seq x₁ (.iteT (by simp only [vE, BExp.denote]; rw [v₁]; exact hz) x₂), ?_, fun i hi hid h8 => ?_, ?_⟩
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans p₂
      · rw [k₂ i (by omega) hid h8, k₁ i (by omega) (by omega) h8]
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact v₂


/-! ## the function -/

theorem load64_exec {v : Nat} {i : BExp} {env : BEnv} {H : Heap} {W : List (BitVec 64)} {j : Nat} {w : BitVec 64}
    (hi : (i.denote env).toNat = j) (hw : W[j]? = some w) :
    BExec (.load64 v 0 i) ⟨env, H, [W]⟩ ⟨env.set v w, H, [W]⟩ := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hw
  have := BExec.load64 (v := v) (b := 0) (i := i) (σ := ⟨env, H, [W]⟩) (by simp) (by simp; omega)
  simp only [List.getElem_cons_zero, hi] at this
  exact this

theorem loads_exec {W : List (BitVec 64)} {h : Nat} {pv : BitVec 64} {v : C} (hi : HI W h) (rv : Rp W h pv v)
    {env : BEnv} {H : Heap} (hp : env 8 = pv) :
    ∃ pl pr, Rp W h pl v.lv ∧ Rp W h pr v.rv ∧ v.tag < 256 ∧
      BExec (loads 8 13 14 15 16) ⟨env, H, [W]⟩
        ⟨(((env.set 13 (BitVec.ofNat 64 v.tag)).set 14 v.xv).set 15 pl).set 16 pr, H, [W]⟩ := by
  obtain ⟨ht, e0, e1, ⟨pl, e2, rl⟩, ⟨pr, e3, rr⟩⟩ := rv.read hi.z0
  have hlt : pv.toNat < 2 ^ 60 := by
    rcases rv.lt with h1 | h1
    · have := hi.hle; have := hi.big; omega
    · subst h1; simp
  have d : ∀ (E : BEnv) (c : Nat), c < 4 → E 8 = pv → ((addE 8 c).denote E).toNat = pv.toNat + c := fun E c hc he => by
    simp only [addE, kE, BExp.denote, Op.eval, he, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨pl, pr, rl, rr, ht, .seq (load64_exec (by simp [vE, BExp.denote, hp]) e0)
    (.seq (load64_exec (d _ 1 (by omega) (by rw [set_ne' _ _ (by omega)]; exact hp)) e1)
    (.seq (load64_exec (d _ 2 (by omega) (by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact hp)) e2)
    (load64_exec (d _ 3 (by omega) (by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact hp)) e3)))⟩

theorem eqE_den (env : BEnv) (v i t : Nat) (he : env v = BitVec.ofNat 64 t) (ht : t < 256) (hi : i < 256) :
    (eqE v i).denote env = if t = i then 1 else 0 := by
  simp only [eqE, vE, kE, BExp.denote, Op.eval, he]
  by_cases h : t = i
  · simp [h]
  · rw [if_neg (fun e => h (by have := congrArg BitVec.toNat e; simp at this; omega)), if_neg h]

/-- the dispatch: the arm of tag `t`, else the default -/
theorem disp_ok {K : Nat} {t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (es : List (E rk rk)) (i : Nat), i ≤ t → i + es.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 13 = BitVec.ofNat 64 t →
      (∀ e, es[t - i]? = some e → ∃ σ', CExec P K (arm 3 e) ⟨env, H, Wh⟩ σ' ∧ Q σ') →
      (es[t - i]? = none → Q ⟨(env.set 12 0).set 11 0, H, Wh⟩) →
      ∃ σ', CExec P K (disp 3 es i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => ⟨_, .base (.seq (asg_exec _ _ _) (asg_exec _ _ _)), hn rfl⟩
  | e :: es, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨σ', hx, hq⟩ := hs e (by simp)
      exact ⟨σ', .iteT (by rw [eqE_den env 13 t t he ht ht, if_pos rfl]; decide) hx, hq⟩
    · obtain ⟨σ', hx, hq⟩ := disp_ok ht es (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .iteF (by show BExp.denote env (eqE 13 i) = 0; rw [eqE_den env 13 i t he ht (by omega), if_neg h]) hx, hq⟩

/-- a run of the loop of `F` on `v` within `K` bytes of stack -/
def LoopOK (P : Prog) (pg : Pg rk) (K : Nat) (v : C) : Prop :=
  ∀ (a bp : BitVec 64) (b : C) (pv : BitVec 64) (env : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    HI W h → env 8 = pv → Rp W h pv v → env 9 = a → env 10 = bp → Rp W h bp b → env 11 = 1 →
    env 5 = BitVec.ofNat 64 h → h + 4 * pg.al v a b ≤ W.length →
    ∃ E' W', CExec P K (fLoop pg) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a b) env E' ∧ RelK W' (h + 4 * pg.al v a b) rk (E' 12) (pg.sem v a b)

theorem bodyOK_of_loopOK {K : Nat} {v : C} (hl : LoopOK P pg K v) (pv : BitVec 64) : BodyOK P pg K v pv := by
  intro a bp b g H W h hi rv rb cap h5
  let env := callEnv g [pv, a, bp]
  have e5 : env 5 = BitVec.ofNat 64 h := by simp only [env, callEnv, if_pos (show 5 < 8 by omega)]; exact h5
  obtain ⟨E', W', hx, hp, hr⟩ := hl a bp b pv (env.set 11 ((kE 1).denote env)) H W h hi rfl rv rfl rfl rb
    (by rw [set_eq']; rfl) (by rw [set_ne' _ _ (by omega)]; exact e5) cap
  refine ⟨E', W', .seq (.base (asg_exec _ _ _)) hx, ⟨hp.len, hp.agr, hp.hi, hp.hle, hp.e5, fun i hi h5' => ?_⟩, hr⟩
  rw [hp.glob i hi h5', set_ne' _ _ (by omega)]
  simp only [env, callEnv, if_pos hi]

theorem bodyOK_mono {K K' : Nat} {v : C} {pv : BitVec 64} (h : BodyOK P pg K v pv) (hk : K ≤ K') :
    BodyOK P pg K' v pv := by
  intro a bp b g H W hh hi rv rb cap h5
  obtain ⟨E', W', hx, hp, hr⟩ := h a bp b g H W hh hi rv rb cap h5
  exact ⟨E', W', hx.mono hk, hp, hr⟩

theorem E.tail?_some {e : E rk rk} {ch : Bool} {ea : E rk .w} {eb : E rk .t}
    (h : e.tail? = some (ch, ea, eb)) : e = .call ch ea eb := by
  cases e <;> simp_all [E.tail?]

theorem sem_c (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {e : E rk rk}
    (he : pg.arms[t]? = some e) : pg.sem (.c t x l r) a b = ev (selfS pg l r) x l r a b e := by
  simp only [Pg.sem, he]; rfl
theorem al_c (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {e : E rk rk}
    (he : pg.arms[t]? = some e) : pg.al (.c t x l r) a b = alE (selfS pg l r) (selfA pg l r) x l r a b e := by
  simp only [Pg.al, he]; rfl
theorem sem_n (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C}
    (he : pg.arms[t]? = none) : pg.sem (.c t x l r) a b = rk.dflt := by simp only [Pg.sem, he]
theorem al_n (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C}
    (he : pg.arms[t]? = none) : pg.al (.c t x l r) a b = 0 := by simp only [Pg.al, he]

/-- the default exit of the loop -/
theorem loop_dflt {K : Nat} {env : BEnv} {H : Heap} {W : List (BitVec 64)} {h : Nat} (hi : HI W h)
    (h5 : env 5 = BitVec.ofNat 64 h) :
    ∃ E', CExec P K (fLoop pg) ⟨(env.set 12 0).set 11 0, H, [W]⟩ ⟨E', H, [W]⟩ ∧ Post W h W h env E' ∧
      RelK W h rk (E' 12) rk.dflt :=
  ⟨_, .loopF (by simp [vE, BExp.denote, set_eq']), ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _,
    by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), h5],
    fun i hi _ => by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]⟩,
    by rw [set_ne' _ _ (by omega), set_eq']; exact RelK.dflt _ _ _⟩

/-- **The function `F`**: the loop on `v` runs within `136 · depth v` bytes of stack -/
theorem loop_ok (hP3 : ∃ hf : 3 < P.length, P[3] = fFn pg) (hpg : pg.arms.length ≤ 255)
    (htg : ∀ e ∈ pg.arms, e.tags < 256) : ∀ v, LoopOK P pg (136 * v.depth) v := by
  intro v
  induction v with
  | z =>
    intro a bp b pv env H W h hi hp rv ha hb rb hgo h5 cap
    obtain ⟨pl, pr, -, -, ht, hld⟩ := loads_exec hi rv hp (H := H)
    let env4 := (((env.set 13 (BitVec.ofNat 64 C.z.tag)).set 14 C.z.xv).set 15 pl).set 16 pr
    have k4 : ∀ i, i < 13 → env4 i = env i := fun i hi' => by
      simp only [env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
        set_ne' _ _ (by omega)]
    obtain ⟨σ', hx, E', W', hl, hpost, hrel⟩ := disp_ok (P := P) (K := 0) (Q := fun σ' =>
        ∃ E' W', CExec P 0 (fLoop pg) σ' ⟨E', H, [W']⟩ ∧ Post W h W' h env E' ∧ RelK W' h rk (E' 12) rk.dflt)
      ht pg.arms 0 (Nat.zero_le _) (by omega) env4 H [W] (by simp [env4, set_ne', set_eq'])
      (fun e he => absurd he (by simp only [C.tag]; rw [List.getElem?_eq_none (by omega)]; simp))
      (fun _ => by
        obtain ⟨E', hx, hp', hr⟩ := loop_dflt (P := P) (pg := pg) (K := 0) (env := env4) (H := H) hi
          (by rw [k4 5 (by omega)]; exact h5)
        refine ⟨E', W, hx, ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, hp'.e5, fun i hi' h5' => ?_⟩, hr⟩
        rw [hp'.glob i hi' h5', k4 i (by omega)])
    refine ⟨E', W', .loopT (by simp [vE, BExp.denote, hgo]) (.seq (.base hld) hx) hl, ?_, ?_⟩
    · simpa [Pg.al] using hpost
    · simpa [Pg.al, Pg.sem] using hrel
  | c t x l r ihl ihr =>
    intro a bp b pv env H W h hi hp rv ha hb rb hgo h5 cap
    obtain ⟨pl, pr, rl, rr, ht, hld⟩ := loads_exec hi rv hp (H := H)
    simp only [C.tag, C.xv, C.lv, C.rv] at rl rr ht hld
    let env4 := (((env.set 13 (BitVec.ofNat 64 t)).set 14 x).set 15 pl).set 16 pr
    have k4 : ∀ i, i < 13 → env4 i = env i := fun i hi' => by
      simp only [env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
        set_ne' _ _ (by omega)]
    have K1 : 136 * (C.c t x l r).depth = 136 + 136 * max l.depth r.depth := by simp only [C.depth]; omega
    have okl : BodyOK P pg (136 * max l.depth r.depth) l pl :=
      bodyOK_mono (bodyOK_of_loopOK ihl pl) (by omega)
    have okr : BodyOK P pg (136 * max l.depth r.depth) r pr :=
      bodyOK_mono (bodyOK_of_loopOK ihr pr) (by omega)
    have cx : Cx (P := P) (pg := pg) (136 * max l.depth r.depth) x l r a b env4 W h :=
      ⟨hi, by rw [k4 5 (by omega)]; exact h5, by simp [env4, set_eq', set_ne'], by rw [k4 9 (by omega)]; exact ha,
        by simp only [env4]; rw [set_ne' _ _ (by omega), set_eq']; exact rl, by simp only [env4]; rw [set_eq']; exact rr,
        by rw [k4 10 (by omega), hb]; exact rb, by simp only [env4]; rw [set_ne' _ _ (by omega), set_eq']; exact okl,
        by simp only [env4]; rw [set_eq']; exact okr⟩
    have harm : ∀ e, pg.arms[t - 0]? = some e → ∃ σ', CExec P (136 * (C.c t x l r).depth) (arm 3 e) ⟨env4, H, [W]⟩ σ' ∧
        (∃ E' W', CExec P (136 * (C.c t x l r).depth) (fLoop pg) σ' ⟨E', H, [W']⟩ ∧
          Post W h W' (h + 4 * pg.al (.c t x l r) a b) env E' ∧
          RelK W' (h + 4 * pg.al (.c t x l r) a b) rk (E' 12) (pg.sem (.c t x l r) a b)) := by
      intro e he
      rw [Nat.sub_zero] at he
      have htge := htg e (List.mem_of_getElem? he)
      rw [al_c pg he] at cap ⊢; rw [sem_c pg he]
      match hta : e.tail? with
      | none =>
        simp only [arm, hta]
        obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hP3 (K := 136 * (C.c t x l r).depth) (by omega) e 12 17 env4 H W h
          (by omega) (by simp) (by omega) htge cx cap
        refine ⟨_, .seq x₁ (.base (asg_exec _ _ _)), E₁.set 11 ((kE 0).denote _), W₁, .loopF (by simp [vE, BExp.denote, set_eq', kE]),
          ⟨p₁.len, p₁.agr, p₁.hi, p₁.hle, by rw [set_ne' _ _ (by omega)]; exact p₁.e5, fun i hi' h5' => ?_⟩, ?_⟩
        · rw [set_ne' _ _ (by omega), p₁.glob i hi' h5', k4 i (by omega)]
        · rw [set_ne' _ _ (by omega)]; exact v₁
      | some (ch, ea, eb) =>
        have hee := E.tail?_some hta
        subst hee
        simp only [arm, hta]
        simp only [E.tags] at htge
        simp only [alE] at cap ⊢
        simp only [ev]
        obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hP3 (K := 136 * (C.c t x l r).depth) (by omega) ea 17 18 env4 H W h
          (by omega) (by simp) (by omega) (by omega) cx (by omega)
        have c₁ := cx.step p₁ (by intro i hi'; simp at hi'; exact k₁ i (by omega) (by omega) (by omega))
        obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := comp_ok hP3 (K := 136 * (C.c t x l r).depth) (by omega) eb 18 19 E₁ H W₁ _
          (by omega) (by simp) (by omega) (by omega) c₁ (by have := p₁.len; omega)
        have c₂ := c₁.step p₂ (by intro i hi'; simp at hi'; exact k₂ i (by omega) (by omega) (by omega))
        have p₂' := p₁.trans p₂
        generalize alE (selfS pg l r) (selfA pg l r) x l r a b ea = A1 at *
        generalize alE (selfS pg l r) (selfA pg l r) x l r a b eb = A2 at *
        rw [selfA_eq] at cap ⊢; rw [selfS_eq]
        let E₃ := ((E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)).set 9 ((vE 17).denote (E₂.set 8
          ((vE (if ch then 16 else 15)).denote E₂)))).set 10 ((vE 18).denote ((E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)).set 9
          ((vE 17).denote (E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)))))
        have k3 : ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → E₃ i = E₂ i := fun i a1 a2 a3 => by
          simp only [E₃]; rw [set_ne' _ _ a3, set_ne' _ _ a2, set_ne' _ _ a1]
        have e8 : E₃ 8 = E₂ (if ch then 16 else 15) := by simp [E₃, set_ne', set_eq', vE, BExp.denote]
        have e9 : E₃ 9 = ev (selfS pg l r) x l r a b ea := by
          simp only [E₃]; rw [set_ne' _ _ (by omega), set_eq']; simp only [vE, BExp.denote]
          rw [set_ne' _ _ (by omega), k₂ 17 (by omega) (by omega) (by omega)]; exact v₁
        have e10 : E₃ 10 = E₂ 18 := by simp only [E₃]; rw [set_eq']; simp only [vE, BExp.denote]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
        have hgo3 : E₃ 11 = 1 := by
          rw [k3 11 (by omega) (by omega) (by omega), k₂ 11 (by omega) (by omega) (by omega),
            k₁ 11 (by omega) (by omega) (by omega)]
          simp [env4, set_ne', hgo]
        have h53 : E₃ 5 = BitVec.ofNat 64 (h + 4 * A1 + 4 * A2) := by rw [k3 5 (by omega) (by omega) (by omega)]; exact p₂.e5
        have hrv : Rp W₂ (h + 4 * A1 + 4 * A2) (E₂ (if ch then 16 else 15)) (if ch then r else l) := by
          cases ch <;> first | exact c₂.rl | exact c₂.rr
        have ihc : LoopOK P pg (136 * (C.c t x l r).depth) (if ch then r else l) := by
          cases ch
          · intro a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            obtain ⟨E', W', hx, hq, hr⟩ := ihl a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            exact ⟨E', W', hx.mono (by simp only [C.depth]; omega), hq, hr⟩
          · intro a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            obtain ⟨E', W', hx, hq, hr⟩ := ihr a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            exact ⟨E', W', hx.mono (by simp only [C.depth]; omega), hq, hr⟩
        obtain ⟨E', W', hl, hpost, hrel⟩ := ihc _ (E₂ 18) _ _ E₃ H W₂ _ p₂.hi e8 hrv e9 e10 (by rw [e10] at *; exact v₂)
          hgo3 h53 (by rw [p₂'.len]; omega)
        refine ⟨_, .seq x₁ (.seq x₂ (.base (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (asg_exec _ _ _))))), E', W', hl,
          ?_, ?_⟩
        · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r) x l r a b ea)
            (ev (selfS pg l r) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
            (ev (selfS pg l r) x l r a b ea) (ev (selfS pg l r) x l r a b eb) by omega]
          refine ⟨hpost.len.trans p₂'.len, p₂'.agr.trans hpost.agr p₂'.hle, hpost.hi, Nat.le_trans p₂'.hle hpost.hle,
            hpost.e5, fun i hi' h5' => ?_⟩
          rw [hpost.glob i hi' h5', k3 i (by omega) (by omega) (by omega), p₂'.glob i hi' h5', k4 i (by omega)]
        · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r) x l r a b ea)
            (ev (selfS pg l r) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
            (ev (selfS pg l r) x l r a b ea) (ev (selfS pg l r) x l r a b eb) by omega]
          exact hrel

    obtain ⟨σ', hx, E', W', hl, hpost, hrel⟩ := disp_ok (P := P) (K := 136 * (C.c t x l r).depth) (Q := fun σ' =>
        ∃ E' W', CExec P (136 * (C.c t x l r).depth) (fLoop pg) σ' ⟨E', H, [W']⟩ ∧
          Post W h W' (h + 4 * pg.al (.c t x l r) a b) env E' ∧
          RelK W' (h + 4 * pg.al (.c t x l r) a b) rk (E' 12) (pg.sem (.c t x l r) a b))
      ht pg.arms 0 (Nat.zero_le _) (by omega) env4 H [W] (by simp [env4, set_ne', set_eq'])
      harm
      (fun hn => by
        rw [Nat.sub_zero] at hn
        obtain ⟨E', hx, hp', hr⟩ := loop_dflt (P := P) (pg := pg) (K := 136 * (C.c t x l r).depth) (env := env4) (H := H) hi
          (by rw [k4 5 (by omega)]; exact h5)
        refine ⟨E', W, hx, ?_, ?_⟩
        · rw [al_n pg hn, Nat.mul_zero, Nat.add_zero]
          exact ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, hp'.e5, fun i hi' h5' => by
            rw [hp'.glob i hi' h5', k4 i (by omega)]⟩
        · rw [al_n pg hn, sem_n pg hn, Nat.mul_zero, Nat.add_zero]; exact hr)
    exact ⟨E', W', .loopT (by simp [vE, BExp.denote, hgo]) (.seq (.base hld) hx) hl, hpost, hrel⟩

end Proven.Mach.Ind

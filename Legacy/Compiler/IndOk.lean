/- Correctness of `indProg` (`Compiler/Ind.lean`) at the source level (`CExec`), once and for all. -/
import Legacy.Compiler.Ind
import Legacy.Compiler.Rec

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

/-- the body of the function at index `fi` -/
def fBody (fi : Nat) (pg : Pg rk) : CStmt := .seq (.base (asg 11 (kE 1))) (fLoopX fi pg)

/-- a call of `F` (index `fi`) on `v` (at `pv`) runs within `K` bytes of stack, in a word block of at most `Lw` words -/
def BodyOK (fi K Lw : Nat) (v : C) (pv : BitVec 64) : Prop :=
  ∀ (a bp : BitVec 64) (b : C) (g : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    W.length ≤ Lw → HI W h → Rp W h pv v → Rp W h bp b → h + 4 * pg.al v a b ≤ W.length → g 5 = BitVec.ofNat 64 h →
    ∃ E' W', CExec P K (fBody fi pg) ⟨callEnv g [pv, a, bp], H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a b) g E' ∧ RelK W' (h + 4 * pg.al v a b) rk (E' 12) (pg.sem v a b)

/-- a call of the function at index `q` (meaning `X`, cells `XA`, result kind `k`) within `K` bytes of stack -/
def XOK (K q : Nat) (k : Kd) (X : C → BitVec 64 → C → BitVec 64 × C) (XA : C → BitVec 64 → C → Nat) (Lw : Nat) :
    Prop :=
  ∀ (v b : C) (pv a bp : BitVec 64) (d pvar avar bvar : Nat) (env : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    8 ≤ d → W.length ≤ Lw → HI W h → env 5 = BitVec.ofNat 64 h → env pvar = pv → env avar = a → env bvar = bp →
    Rp W h pv v → Rp W h bp b → h + 4 * XA v a b ≤ W.length →
    ∃ E' W', CExec P K (.call d q [vE pvar, vE avar, vE bvar]) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * XA v a b) env E' ∧ (∀ i, 8 ≤ i → i ≠ d → E' i = env i) ∧
      RelK W' (h + 4 * XA v a b) k (E' d) (k.pick (X v a b))

variable {P pg}

theorem xok_mono {K K' q : Nat} {k : Kd} {X : C → BitVec 64 → C → BitVec 64 × C} {XA : C → BitVec 64 → C → Nat}
    {Lw : Nat} (h : XOK P K q k X XA Lw) (hk : K ≤ K') : XOK P K' q k X XA Lw := by
  intro v b pv a bp d pvar avar bvar env H W hh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  obtain ⟨E', W', hx, rest⟩ := h v b pv a bp d pvar avar bvar env H W hh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  exact ⟨E', W', hx.mono hk, rest⟩

theorem call_body {f : Nat} (hf : f < P.length) {K K' : Nat} (hK : P[f].frame + K' ≤ K) {d : Nat}
    {args : List BExp} (ha : args.length = P[f].nparams) {σ σ₁ : BState}
    (hb : CExec P K' P[f].body ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ σ₁) :
    CExec P K (.call d f args) σ ⟨(retEnv σ.env σ₁.env).set d (P[f].ret.denote σ₁.env), σ₁.heap, σ₁.wheap⟩ :=
  .call hf ha hK hb

/-- the closures `Pg.sem` / `Pg.al` pass to the arms -/
def selfS (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) : Cn rk :=
  ⟨fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b',
    fun c₁ c₂ a' b' => if c₁ then (match r with
        | .z => rk.dflt
        | .c _ _ rl rr => if c₂ then pg.sem rr a' b' else pg.sem rl a' b')
      else (match l with
        | .z => rk.dflt
        | .c _ _ ll lr => if c₂ then pg.sem lr a' b' else pg.sem ll a' b'), pg.X, me, ρ⟩
def selfA (pg : Pg rk) (l r : C) : Ca :=
  ⟨fun ch a' b' => if ch then pg.al r a' b' else pg.al l a' b',
   fun c₁ c₂ a' b' => if c₁ then (match r with
      | .z => 0
      | .c _ _ rl rr => if c₂ then pg.al rr a' b' else pg.al rl a' b')
    else (match l with
      | .z => 0
      | .c _ _ ll lr => if c₂ then pg.al lr a' b' else pg.al ll a' b'), pg.XA⟩

/-- the grandchild `c₂` of child `c₁` -/
def C.gch (l r : C) (c₁ c₂ : Bool) : C := if c₂ then (if c₁ then r else l).rv else (if c₁ then r else l).lv

theorem C.depth_lv (v : C) : v.lv.depth ≤ v.depth := by cases v <;> simp [C.lv, C.depth]; omega
theorem C.depth_rv (v : C) : v.rv.depth ≤ v.depth := by cases v <;> simp [C.rv, C.depth]; omega
theorem C.depth_gch (l r : C) (c₁ c₂ : Bool) : (C.gch l r c₁ c₂).depth ≤ max l.depth r.depth := by
  have := C.depth_lv l; have := C.depth_rv l; have := C.depth_lv r; have := C.depth_rv r
  cases c₁ <;> cases c₂ <;> simp only [C.gch, if_true, if_false, Bool.false_eq_true] <;> omega

/-- the state an arm runs in -/
structure Cx (fi K' KX Lw : Nat) (nx : List Kd) (me : C) (ρ : List (BitVec 64 × C)) (sl : List Nat) (ks : List Kd)
    (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) (env : BEnv) (W : List (BitVec 64)) (h : Nat) : Prop where
  hi : HI W h
  e5 : env 5 = BitVec.ofNat 64 h
  ex : env 14 = x
  ea : env 9 = a
  rl : Rp W h (env 15) l
  rr : Rp W h (env 16) r
  rb : Rp W h (env 10) b
  okl : BodyOK P pg fi K' Lw l (env 15)
  okr : BodyOK P pg fi K' Lw r (env 16)
  lw : W.length ≤ Lw
  rme : Rp W h (env 8) me
  sll : sl.length = ks.length
  ρl : ρ.length = ks.length
  rρ : ∀ i (h1 : i < ks.length) (h2 : i < sl.length) (h3 : i < ρ.length), RelK W h ks[i] (env sl[i]) (ks[i].pick ρ[i])
  okx : ∀ j k, nx[j]? = some k → XOK P KX (fi + 1 + j) k (pg.X j) (pg.XA j) Lw
  okg : ∀ c₁ c₂ pv, BodyOK P pg fi K' Lw (C.gch l r c₁ c₂) pv

theorem Cx.step {fi K' KX Lw : Nat} {nx : List Kd} {me : C} {ρ : List (BitVec 64 × C)} {sl : List Nat} {ks : List Kd}
    {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {env env' : BEnv}
    {W W' : List (BitVec 64)} {h h' : Nat} (c : Cx (P := P) (pg := pg) fi K' KX Lw nx me ρ sl ks x l r a b env W h)
    (p : Post W h W' h' env env')
    (hk : ∀ i, i ∈ [8, 9, 10, 14, 15, 16] → env' i = env i) (hs : ∀ s ∈ sl, env' s = env s) :
    Cx (P := P) (pg := pg) fi K' KX Lw nx me ρ sl ks x l r a b env' W' h' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k8, k9, k10, k14, k15, k16⟩ := hk
  exact ⟨p.hi, p.e5, by rw [k14]; exact c.ex, by rw [k9]; exact c.ea, by rw [k15]; exact c.rl.mono p.hle p.agr,
    by rw [k16]; exact c.rr.mono p.hle p.agr, by rw [k10]; exact c.rb.mono p.hle p.agr, by rw [k15]; exact c.okl,
    by rw [k16]; exact c.okr, by rw [p.len]; exact c.lw, by rw [k8]; exact c.rme.mono p.hle p.agr, c.sll, c.ρl,
    fun i h1 h2 h3 => by rw [hs _ (List.getElem_mem h2)]; exact (c.rρ i h1 h2 h3).mono p.hle p.agr, c.okx, c.okg⟩

theorem post_set {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {env : BEnv} (h5 : env 5 = BitVec.ofNat 64 h)
    {d : Nat} (hd : 8 ≤ d) (y : BitVec 64) : Post W h W h env (env.set d y) :=
  ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, by rw [set_ne' _ _ (by omega)]; exact h5,
    fun i hi _ => set_ne' _ _ (by omega)⟩

theorem fFn_frame (fi nl : Nat) (pg : Pg rk) : (fFn fi nl pg).frame = 8 * (nl + 1) := rfl

theorem call_ok {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) {K K' Lw : Nat}
    (hK : 8 * (nl + 1) + K' ≤ K) {v b' : C}
    {pv a' bp : BitVec 64} {d pvar avar bvar : Nat} (ok : BodyOK P pg fi K' Lw v pv) {env : BEnv} {H : Heap}
    {W : List (BitVec 64)} {h : Nat} (hw : W.length ≤ Lw) (hi : HI W h) (h5 : env 5 = BitVec.ofNat 64 h)
    (hp : env pvar = pv) (ha : env avar = a') (hb : env bvar = bp) (rv : Rp W h pv v) (rb : Rp W h bp b')
    (cap : h + 4 * pg.al v a' b' ≤ W.length) (hd : 8 ≤ d) :
    ∃ E' W', CExec P K (.call d fi [vE pvar, vE avar, vE bvar]) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a' b') env E' ∧ (∀ i, 8 ≤ i → i ≠ d → E' i = env i) ∧
      RelK W' (h + 4 * pg.al v a' b') rk (E' d) (pg.sem v a' b') := by
  obtain ⟨hf3, hP⟩ := hPf
  obtain ⟨E'', W', hx, hpost, hrel⟩ := ok a' bp b' env H W h hw hi rv rb cap h5
  have hargs : [vE pvar, vE avar, vE bvar].map (·.denote env) = [pv, a', bp] := by
    simp [vE, BExp.denote, hp, ha, hb]
  have hc := call_body (P := P) (f := fi) (K := K) (K' := K') hf3 (by rw [hP]; exact hK) (d := d)
    (args := [vE pvar, vE avar, vE bvar]) (by rw [hP]; rfl) (σ := ⟨env, H, [W]⟩) (σ₁ := ⟨E'', H, [W']⟩)
    (by rw [hP]; simp only [hargs]; exact hx)
  rw [hP] at hc
  refine ⟨_, W', hc, ⟨hpost.len, hpost.agr, hpost.hi, hpost.hle, ?_, fun i hi h5' => ?_⟩, fun i hi hid => ?_, ?_⟩
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos (show 5 < 8 by omega)]; exact hpost.e5
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos hi]; exact hpost.glob i hi h5'
  · simp only; rw [set_ne' _ _ hid]; simp only [retEnv, if_neg (show ¬ i < 8 by omega)]
  · simp only; rw [set_eq']; exact hrel

theorem selfS_eq (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) (ch : Bool) (a' : BitVec 64) (b' : C) :
    (selfS pg l r me ρ).f ch a' b' = pg.sem (if ch then r else l) a' b' := by cases ch <;> rfl
theorem selfA_eq (pg : Pg rk) (l r : C) (ch : Bool) (a' : BitVec 64) (b' : C) :
    (selfA pg l r).f ch a' b' = pg.al (if ch then r else l) a' b' := by cases ch <;> rfl
theorem selfS_g (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) (c₁ c₂ : Bool) (a' : BitVec 64) (b' : C) :
    (selfS pg l r me ρ).g c₁ c₂ a' b' = pg.sem (C.gch l r c₁ c₂) a' b' := by
  cases c₁ <;> cases c₂ <;> cases l <;> cases r <;> simp [selfS, C.gch, C.lv, C.rv, Pg.sem]
theorem selfA_g (pg : Pg rk) (l r : C) (c₁ c₂ : Bool) (a' : BitVec 64) (b' : C) :
    (selfA pg l r).g c₁ c₂ a' b' = pg.al (C.gch l r c₁ c₂) a' b' := by
  cases c₁ <;> cases c₂ <;> cases l <;> cases r <;> simp [selfA, C.gch, C.lv, C.rv, Pg.al]

/-- a grandchild's pointer is in its parent's cell -/
theorem gch_read {W : List (BitVec 64)} {h : Nat} (hz : Z0 W) {pl pr : BitVec 64} {l r : C} (rl : Rp W h pl l)
    (rr : Rp W h pr r) (c₁ c₂ : Bool) :
    ∃ w, W[(if c₁ then pr else pl).toNat + (if c₂ then 3 else 2)]? = some w ∧ Rp W h w (C.gch l r c₁ c₂) := by
  obtain ⟨_, _, _, ⟨pll, el, rll⟩, ⟨plr, er, rlr⟩⟩ := rl.read hz
  obtain ⟨_, _, _, ⟨prl, fl, rrl⟩, ⟨prr, fr, rrr⟩⟩ := rr.read hz
  cases c₁ <;> cases c₂
  · exact ⟨pll, by simpa using el, by simpa [C.gch] using rll⟩
  · exact ⟨plr, by simpa using er, by simpa [C.gch] using rlr⟩
  · exact ⟨prl, by simpa using fl, by simpa [C.gch] using rrl⟩
  · exact ⟨prr, by simpa using fr, by simpa [C.gch] using rrr⟩

theorem rp_toNat {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {v : C} (hi : HI W h) (rv : Rp W h p v) :
    p.toNat < 2 ^ 60 := by
  have := rv.lt4 hi.h4; have := hi.hle; have := hi.big; omega

theorem addE_ptr {env : BEnv} {n c : Nat} {p : BitVec 64} (hp : env n = p) (hl : p.toNat < 2 ^ 60) (hc : c < 4) :
    ((addE n c).denote env).toNat = p.toNat + c := by
  simp only [addE, kE, BExp.denote, Op.eval, hp, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem load64_exec {v : Nat} {i : BExp} {env : BEnv} {H : Heap} {W : List (BitVec 64)} {j : Nat} {w : BitVec 64}
    (hi : (i.denote env).toNat = j) (hw : W[j]? = some w) :
    BExec (.load64 v 0 i) ⟨env, H, [W]⟩ ⟨env.set v w, H, [W]⟩ := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hw
  have := BExec.load64 (v := v) (b := 0) (i := i) (σ := ⟨env, H, [W]⟩) (by simp) (by simp; omega)
  simp only [List.getElem_cons_zero, hi] at this
  exact this

theorem getD_eq {α : Type} (L : List α) (i : Nat) (d : α) (h : i < L.length) : L.getD i d = L[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem selfS_X (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) : (selfS pg l r me ρ).X = pg.X := rfl
theorem selfA_X (pg : Pg rk) (l r : C) : (selfA pg l r).X = pg.XA := rfl
theorem selfS_me (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) : (selfS pg l r me ρ).me = me := rfl
theorem selfS_ρ (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) : (selfS pg l r me ρ).ρ = ρ := rfl
theorem selfS_with (pg : Pg rk) (l r me : C) (ρ : List (BitVec 64 × C)) (q : BitVec 64 × C) :
    (⟨(selfS pg l r me ρ).f, (selfS pg l r me ρ).g, (selfS pg l r me ρ).X, (selfS pg l r me ρ).me,
      q :: (selfS pg l r me ρ).ρ⟩ : Cn rk) =
      selfS pg l r me (q :: ρ) := rfl

/-- **Expressions**: `comp e d n` leaves the value of `e` in `v_d`, allocates `alE e` cells, keeps the variables
below `n` other than `d` -/
theorem comp_ok {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) {K K' KX Lw : Nat}
    (hK : 8 * (nl + 1) + K' ≤ K) (hKX : KX ≤ K) {nx : List Kd}
    {x : BitVec 64} {l r me : C} {a : BitVec 64} {b : C} :
    ∀ {k : Kd} (e : E rk k) (ρ : List (BitVec 64 × C)) (sl : List Nat) (ks : List Kd) (d n : Nat) (env : BEnv)
      (H : Heap) (W : List (BitVec 64)) (h : Nat),
      8 ≤ d → d ∉ [8, 9, 10, 14, 15, 16] → d ∉ sl → d < n → 17 ≤ n → (∀ s ∈ sl, 17 ≤ s ∧ s < n) →
      e.tags < 256 → e.okc ks nx = true →
      Cx (P := P) (pg := pg) fi K' KX Lw nx me ρ sl ks x l r a b env W h →
      h + 4 * alE (selfS pg l r me ρ) (selfA pg l r) x l r a b e ≤ W.length →
      ∃ E' W', CExec P K (comp fi sl e d n) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
        Post W h W' (h + 4 * alE (selfS pg l r me ρ) (selfA pg l r) x l r a b e) env E' ∧
        (∀ i, i < n → i ≠ d → 8 ≤ i → E' i = env i) ∧
        RelK W' (h + 4 * alE (selfS pg l r me ρ) (selfA pg l r) x l r a b e) k (E' d)
          (ev (selfS pg l r me ρ) x l r a b e) := by
  obtain ⟨hf3, hP⟩ := hPf
  intro k e
  induction e with
  | x | a | k _ | l | r | b | nul | me =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdk
    refine ⟨_, W, .base (asg_exec _ _ _), post_set c.hi c.e5 hd _, fun i _ hi _ => set_ne' _ _ hi, ?_⟩
    simp only [alE, Nat.mul_zero, Nat.add_zero, ev, set_eq', vE, kE, BExp.denote, selfS_me]
    first | exact c.ex | exact c.ea | rfl | exact c.rl | exact c.rr | exact c.rb | exact .z | exact c.rme
  | var i kk =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [E.okc, beq_iff_eq] at hok
    have hi1 : i < ks.length := (List.getElem?_eq_some_iff.1 hok).1
    have hkk : ks[i] = kk := (List.getElem?_eq_some_iff.1 hok).2
    have hi2 : i < sl.length := by rw [c.sll]; exact hi1
    have hi3 : i < ρ.length := by rw [c.ρl]; exact hi1
    refine ⟨_, W, .base (asg_exec _ _ _), post_set c.hi c.e5 hd _, fun i' _ hi _ => set_ne' _ _ hi, ?_⟩
    simp only [alE, Nat.mul_zero, Nat.add_zero, ev, set_eq', vE, BExp.denote, selfS_ρ]
    rw [getD_eq sl i 0 hi2, getD_eq ρ i _ hi3]
    have := c.rρ i hi1 hi2 hi3
    rw [hkk] at this; exact this
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ih₁ ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₂ ρ sl ks (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.2 c₁ (by have := p₁.len; omega)
    have p₂' := p₁.trans p₂
    refine ⟨_, W₂, .seq x₁ (.seq x₂ (.base (asg_exec _ _ _))), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₂'.trans (post_set p₂.hi p₂.e5 hd _)
    · dsimp only; rw [set_ne' _ _ hid, k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · simp only [RelK, ev, set_eq', vE, BExp.denote]
      rw [k₂ n (by omega) (by omega) (by omega)]
      simp only [RelK] at v₁ v₂; rw [v₁, v₂]
  | mk t ex el er ihx ihl ihr =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ihx ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1.1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ihl ρ sl ks (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1.2 c₁ (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₂ s (by omega) (by omega) (by omega))
    obtain ⟨E₃, W₃, x₃, p₃, k₃, v₃⟩ := ihr ρ sl ks (n + 2) (n + 3) E₂ H W₂ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.2 c₂ (by have := p₁.len; have := p₂.len; omega)
    have p₃' := (p₁.trans p₂).trans p₃
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b ex = A1 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b el = A2 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b er = A3 at *
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
      have e1 : E₃ n = ev (selfS pg l r me ρ) x l r a b ex := by
        rw [k₃ n (by omega) (by omega) (by omega), k₂ n (by omega) (by omega) (by omega)]; exact v₁
      have e2 := k₃ (n + 1) (by omega) (by omega) (by omega)
      have hkt : (kE t).denote E₃ = BitVec.ofNat 64 t := rfl
      rw [hkt, e1]
      have r2 : Rp W₃ (h + 4 * A1 + 4 * A2 + 4 * A3) (E₃ (n + 1)) (ev (selfS pg l r me ρ) x l r a b el) := by
        rw [e2]; exact v₂.mono p₃.hle p₃.agr
      exact Rp_put p₃.hi (by omega) hb3 (x := ev (selfS pg l r me ρ) x l r a b ex) r2 v₃
  | call ch ea eb iha ihb =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := iha ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ihb ρ sl ks (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.2 c₁ (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₂ s (by omega) (by omega) (by omega))
    have p₂' := p₁.trans p₂
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b ea = A1 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b eb = A2 at *
    rw [selfA_eq] at hcap ⊢; simp only [ev]; rw [selfS_eq]
    have hok' : BodyOK P pg fi K' Lw (if ch then r else l) (E₂ (if ch then 16 else 15)) := by cases ch <;>
      first | exact c₂.okl | exact c₂.okr
    have hrv : Rp W₂ (h + 4 * A1 + 4 * A2) (E₂ (if ch then 16 else 15)) (if ch then r else l) := by
      cases ch <;> first | exact c₂.rl | exact c₂.rr
    have ea' : E₂ n = ev (selfS pg l r me ρ) x l r a b ea := by
      rw [k₂ n (by omega) (by omega) (by omega)]; exact v₁
    have rb' : Rp W₂ (h + 4 * A1 + 4 * A2) (E₂ (n + 1)) (ev (selfS pg l r me ρ) x l r a b eb) := v₂
    obtain ⟨E₃, W₃, x₃, p₃, k₃, v₃⟩ := call_ok ⟨hf3, hP⟩ hK (d := d) hok' c₂.lw p₂.hi p₂.e5 rfl ea' rfl hrv rb'
      (by rw [p₂'.len]; omega) hd
    refine ⟨_, W₃, .seq x₁ (.seq x₂ x₃), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
        (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb) by omega]
      exact p₂'.trans p₃
    · rw [k₃ i h8 hid, k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · rw [show h + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
        (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb) by omega]
      exact v₃
  | call2 c₁' c₂' ea eb iha ihb =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := iha ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ihb ρ sl ks (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.2 c₁ (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₂ s (by omega) (by omega) (by omega))
    have p₂' := p₁.trans p₂
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b ea = A1 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b eb = A2 at *
    rw [selfA_g] at hcap ⊢; simp only [ev]; rw [selfS_g]
    -- the grandchild's pointer into `v_{n+2}`
    obtain ⟨w, hw, rw'⟩ := gch_read p₂.hi.z0 c₂.rl c₂.rr c₁' c₂'
    have hp : (if c₁' then E₂ 16 else E₂ 15) = E₂ (if c₁' then 16 else 15) := by cases c₁' <;> rfl
    rw [hp] at hw
    have hl := rp_toNat p₂.hi (show Rp W₂ _ (E₂ (if c₁' then 16 else 15)) (if c₁' then r else l) by
      cases c₁' <;> first | exact c₂.rl | exact c₂.rr)
    have xl := load64_exec (v := n + 2) (H := H) (addE_ptr rfl hl (by split <;> omega)) hw
    have p₃ := post_set p₂.hi p₂.e5 (d := n + 2) (by omega) w
    have ea' : (E₂.set (n + 2) w) n = ev (selfS pg l r me ρ) x l r a b ea := by
      rw [set_ne' _ _ (by omega), k₂ n (by omega) (by omega) (by omega)]; exact v₁
    have eb' : (E₂.set (n + 2) w) (n + 1) = E₂ (n + 1) := set_ne' _ _ (by omega)
    have rb' : Rp W₂ (h + 4 * A1 + 4 * A2) ((E₂.set (n + 2) w) (n + 1)) (ev (selfS pg l r me ρ) x l r a b eb) := by
      rw [eb']; exact v₂
    obtain ⟨E₃, W₃, x₃, p₄, k₃, v₃⟩ := call_ok ⟨hf3, hP⟩ hK (d := d) (c₂.okg c₁' c₂' w) c₂.lw p₂.hi p₃.e5 (set_eq' _ _ _) ea'
      rfl rw' rb' (by rw [p₂'.len]; omega) hd
    refine ⟨_, W₃, .seq x₁ (.seq x₂ (.seq (.base xl) x₃)), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [show h + 4 * (A1 + A2 + pg.al (C.gch l r c₁' c₂') (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (C.gch l r c₁' c₂')
        (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb) by omega]
      exact (p₂'.trans p₃).trans p₄
    · rw [k₃ i h8 hid, set_ne' _ _ (by omega), k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · rw [show h + 4 * (A1 + A2 + pg.al (C.gch l r c₁' c₂') (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * pg.al (C.gch l r c₁' c₂')
        (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb) by omega]
      exact v₃
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok cx hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ihc ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1.1 cx (by omega)
    have c₁ := cx.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    simp only [RelK] at v₁
    simp only [ev]
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b c = A1 at *
    by_cases hz : ev (selfS pg l r me ρ) x l r a b c = 0
    · rw [if_pos hz] at hcap ⊢; rw [if_pos hz]
      obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₂ ρ sl ks d (n + 1) E₁ H W₁ _ hd hdk hds (by omega) (by omega)
        (fun s hs => by have := hsl s hs; omega) (by omega) hok.2 c₁ (by have := p₁.len; omega)
      refine ⟨E₂, W₂, .seq x₁ (.iteF (by simp only [vE, BExp.denote]; rw [v₁, hz]) x₂), ?_, fun i hi hid h8 => ?_, ?_⟩
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans p₂
      · rw [k₂ i (by omega) hid h8, k₁ i (by omega) (by omega) h8]
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact v₂
    · rw [if_neg hz] at hcap ⊢; rw [if_neg hz]
      obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₁ ρ sl ks d (n + 1) E₁ H W₁ _ hd hdk hds (by omega) (by omega)
        (fun s hs => by have := hsl s hs; omega) (by omega) hok.1.2 c₁ (by have := p₁.len; omega)
      refine ⟨E₂, W₂, .seq x₁ (.iteT (by simp only [vE, BExp.denote]; rw [v₁]; exact hz) x₂), ?_,
        fun i hi hid h8 => ?_, ?_⟩
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans p₂
      · rw [k₂ i (by omega) hid h8, k₁ i (by omega) (by omega) h8]
      · rw [Nat.mul_add, ← Nat.add_assoc]; exact v₂
  | fw i e ih =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ih ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok c hcap
    simp only [RelK] at v₁
    obtain ⟨_, e0, e1, -, -⟩ := v₁.read p₁.hi.z0
    have hl := rp_toNat p₁.hi v₁
    have hw : W₁[(E₁ n).toNat + (if i then 1 else 0)]? = some (ev (selfS pg l r me ρ) x l r a b (.fw i e)) := by
      cases i
      · simpa [ev] using e0
      · simpa [ev] using e1
    refine ⟨_, W₁, .seq x₁ (.base (load64_exec (addE_ptr rfl hl (by split <;> omega)) hw)), ?_,
      fun i' hi' hid h8 => ?_, ?_⟩
    · exact p₁.trans (post_set p₁.hi p₁.e5 hd _)
    · rw [set_ne' _ _ hid, k₁ i' (by omega) (by omega) h8]
    · simp only [RelK]; rw [set_eq']
  | ft ch e ih =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc] at hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := ih ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok c hcap
    simp only [RelK] at v₁
    obtain ⟨_, _, _, ⟨pl, e2, rl'⟩, ⟨pr, e3, rr'⟩⟩ := v₁.read p₁.hi.z0
    have hl := rp_toNat p₁.hi v₁
    obtain ⟨w, hw, rw'⟩ : ∃ w, W₁[(E₁ n).toNat + (if ch then 3 else 2)]? = some w ∧
        Rp W₁ (h + 4 * alE (selfS pg l r me ρ) (selfA pg l r) x l r a b e) w
          (ev (selfS pg l r me ρ) x l r a b (.ft ch e)) := by
      cases ch
      · exact ⟨pl, by simpa using e2, by simpa [ev] using rl'⟩
      · exact ⟨pr, by simpa using e3, by simpa [ev] using rr'⟩
    refine ⟨_, W₁, .seq x₁ (.base (load64_exec (addE_ptr rfl hl (by split <;> omega)) hw)), ?_,
      fun i' hi' hid h8 => ?_, ?_⟩
    · exact p₁.trans (post_set p₁.hi p₁.e5 hd _)
    · rw [set_ne' _ _ hid, k₁ i' (by omega) (by omega) h8]
    · simp only [RelK]; rw [set_eq']; exact rw'
  | ext j kk et ea eb iht iha ihb =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hj, hok1⟩, hok2⟩, hok3⟩ := hok
    obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := iht ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁ s (by omega) (by omega) (by omega))
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := iha ρ sl ks (n + 1) (n + 2) E₁ H W₁ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok2 c₁ (by have := p₁.len; omega)
    have c₂ := c₁.step p₂ (by intro i hi; simp at hi; exact k₂ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₂ s (by omega) (by omega) (by omega))
    obtain ⟨E₃, W₃, x₃, p₃, k₃, v₃⟩ := ihb ρ sl ks (n + 2) (n + 3) E₂ H W₂ _ (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok3 c₂ (by have := p₁.len; have := p₂.len; omega)
    have c₃ := c₂.step p₃ (by intro i hi; simp at hi; exact k₃ i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₃ s (by omega) (by omega) (by omega))
    have p₃' := (p₁.trans p₂).trans p₃
    rw [selfA_X] at hcap ⊢; simp only [ev]; rw [selfS_X]
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b et = A1 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b ea = A2 at *
    generalize alE (selfS pg l r me ρ) (selfA pg l r) x l r a b eb = A3 at *
    have et' : Rp W₃ (h + 4 * A1 + 4 * A2 + 4 * A3) (E₃ n) (ev (selfS pg l r me ρ) x l r a b et) := by
      rw [k₃ n (by omega) (by omega) (by omega), k₂ n (by omega) (by omega) (by omega)]
      exact (v₁.mono p₂.hle p₂.agr).mono p₃.hle p₃.agr
    have ea' : E₃ (n + 1) = ev (selfS pg l r me ρ) x l r a b ea := by
      rw [k₃ (n + 1) (by omega) (by omega) (by omega)]; exact v₂
    obtain ⟨E₄, W₄, x₄, p₄, k₄, v₄⟩ := c₃.okx j kk hj _ _ _ _ _ d n (n + 1) (n + 2) E₃ H W₃ _ hd c₃.lw p₃.hi p₃.e5
      rfl ea' rfl et' v₃ (by rw [p₃'.len]; omega)
    refine ⟨_, W₄, .seq x₁ (.seq x₂ (.seq x₃ (x₄.mono hKX))), ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [show h + 4 * (A1 + A2 + A3 + pg.XA j (ev (selfS pg l r me ρ) x l r a b et) (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * A3 + 4 * pg.XA j
        (ev (selfS pg l r me ρ) x l r a b et) (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb)
        by omega]
      exact p₃'.trans p₄
    · rw [k₄ i h8 hid, k₃ i (by omega) (by omega) h8, k₂ i (by omega) (by omega) h8, k₁ i (by omega) (by omega) h8]
    · rw [show h + 4 * (A1 + A2 + A3 + pg.XA j (ev (selfS pg l r me ρ) x l r a b et) (ev (selfS pg l r me ρ) x l r a b ea)
        (ev (selfS pg l r me ρ) x l r a b eb)) = h + 4 * A1 + 4 * A2 + 4 * A3 + 4 * pg.XA j
        (ev (selfS pg l r me ρ) x l r a b et) (ev (selfS pg l r me ρ) x l r a b ea) (ev (selfS pg l r me ρ) x l r a b eb)
        by omega]
      exact v₄
  | @bind k₁ k e₁ e₂ ih₁ ih₂ =>
    intro ρ sl ks d n env H W h hd hdk hds hdn hn hsl htg hok c hcap
    simp only [alE] at hcap ⊢
    simp only [E.tags] at htg
    simp only [E.okc, Bool.and_eq_true] at hok
    simp only [ev]
    rw [selfS_with] at hcap ⊢
    obtain ⟨E₁, W₁, x₁, p₁, k₁', v₁⟩ := ih₁ ρ sl ks n (n + 1) env H W h (by omega) (by simp; omega)
      (fun h' => by have := hsl _ h'; omega) (by omega) (by omega) (fun s hs => by have := hsl s hs; omega) (by omega)
      hok.1 c (by omega)
    have c₁ := c.step p₁ (by intro i hi; simp at hi; exact k₁' i (by omega) (by omega) (by omega))
      (fun s hs => by have := hsl s hs; exact k₁' s (by omega) (by omega) (by omega))
    have c₁' : Cx (P := P) (pg := pg) fi K' KX Lw nx me (k₁.pair (ev (selfS pg l r me ρ) x l r a b e₁) :: ρ) (n :: sl)
        (k₁ :: ks) x l r a b E₁ W₁ (h + 4 * alE (selfS pg l r me ρ) (selfA pg l r) x l r a b e₁) :=
      { c₁ with
        sll := by simp [c₁.sll]
        ρl := by simp [c₁.ρl]
        rρ := fun i h1 h2 h3 => by
          cases i with
          | zero => simp only [List.getElem_cons_zero, Kd.pick_pair]; exact v₁
          | succ i =>
            simp only [List.getElem_cons_succ]
            exact c₁.rρ i (by simp at h1; omega) (by simp at h2; omega) (by simp at h3; omega) }
    obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := ih₂ _ (n :: sl) (k₁ :: ks) d (n + 1) E₁ H W₁ _ hd hdk
      (fun h' => by
        rcases List.mem_cons.1 h' with h' | h'
        · omega
        · exact hds h')
      (by omega) (by omega)
      (fun s hs => by
        rcases List.mem_cons.1 hs with hs | hs
        · omega
        · have := hsl s hs; omega)
      (by omega) hok.2 c₁' (by have := p₁.len; omega)
    refine ⟨E₂, W₂, .seq x₁ x₂, ?_, fun i hi hid h8 => ?_, ?_⟩
    · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans p₂
    · rw [k₂ i (by omega) hid h8, k₁' i (by omega) (by omega) h8]
    · rw [Nat.mul_add, ← Nat.add_assoc]; exact v₂

/-! ## the function -/

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
theorem disp_ok {fi K : Nat} {t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (es : List (E rk rk)) (i : Nat), i ≤ t → i + es.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 13 = BitVec.ofNat 64 t →
      (∀ e, es[t - i]? = some e → ∃ σ', CExec P K (armT fi 8 e) ⟨env, H, Wh⟩ σ' ∧ Q σ') →
      (es[t - i]? = none → Q ⟨(env.set 12 0).set 11 0, H, Wh⟩) →
      ∃ σ', CExec P K (disp fi es i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
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

/-- a run of the loop of `F` (index `fi`) on `v` within `K` bytes of stack -/
def LoopOK (P : Prog) (fi : Nat) (pg : Pg rk) (K Lw : Nat) (v : C) : Prop :=
  ∀ (a bp : BitVec 64) (b : C) (pv : BitVec 64) (env : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    W.length ≤ Lw → HI W h → env 8 = pv → Rp W h pv v → env 9 = a → env 10 = bp → Rp W h bp b → env 11 = 1 →
    env 5 = BitVec.ofNat 64 h → h + 4 * pg.al v a b ≤ W.length →
    ∃ E' W', CExec P K (fLoop fi pg) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a b) env E' ∧ RelK W' (h + 4 * pg.al v a b) rk (E' 12) (pg.sem v a b)

theorem fLoopX_f {fi : Nat} (hst : pg.st = false) : fLoopX fi pg = fLoop fi pg := by simp [fLoopX, hst]
theorem fLoopX_t {fi : Nat} (hst : pg.st = true) : fLoopX fi pg = fLoopS fi pg := by simp [fLoopX, hst]

theorem bodyOK_of_loopOK {fi K Lw : Nat} {v : C} (hst : pg.st = false) (hl : LoopOK P fi pg K Lw v) (pv : BitVec 64) :
    BodyOK P pg fi K Lw v pv := by
  intro a bp b g H W h hw hi rv rb cap h5
  let env := callEnv g [pv, a, bp]
  have e5 : env 5 = BitVec.ofNat 64 h := by simp only [env, callEnv, if_pos (show 5 < 8 by omega)]; exact h5
  obtain ⟨E', W', hx, hp, hr⟩ := hl a bp b pv (env.set 11 ((kE 1).denote env)) H W h hw hi rfl rv rfl rfl rb
    (by rw [set_eq']; rfl) (by rw [set_ne' _ _ (by omega)]; exact e5) cap
  refine ⟨E', W', .seq (.base (asg_exec _ _ _)) (by rw [fLoopX_f hst]; exact hx),
    ⟨hp.len, hp.agr, hp.hi, hp.hle, hp.e5, fun i hi h5' => ?_⟩, hr⟩
  rw [hp.glob i hi h5', set_ne' _ _ (by omega)]
  simp only [env, callEnv, if_pos hi]

theorem bodyOK_mono {fi K K' Lw : Nat} {v : C} {pv : BitVec 64} (h : BodyOK P pg fi K Lw v pv) (hk : K ≤ K') :
    BodyOK P pg fi K' Lw v pv := by
  intro a bp b g H W hw hh hi rv rb cap h5
  obtain ⟨E', W', hx, hp, hr⟩ := h a bp b g H W hw hh hi rv rb cap h5
  exact ⟨E', W', hx.mono hk, hp, hr⟩

theorem E.tail?_some {e : E rk rk} {ch : Bool} {ea : E rk .w} {eb : E rk .t}
    (h : e.tail? = some (ch, ea, eb)) : e = .call ch ea eb := by
  cases e <;> simp_all [E.tail?]

theorem E.ite?_some {k : Kd} {e : E rk k} {c : E rk .w} {e₁ e₂ : E rk k}
    (h : e.ite? = some (c, e₁, e₂)) : e = .ite c e₁ e₂ := by
  cases e <;> simp_all [E.ite?]

theorem sem_c (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {e : E rk rk}
    (he : pg.arms[t]? = some e) : pg.sem (.c t x l r) a b = ev (selfS pg l r (.c t x l r) []) x l r a b e := by
  simp only [Pg.sem, he]; rfl
theorem al_c (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C} {e : E rk rk}
    (he : pg.arms[t]? = some e) :
    pg.al (.c t x l r) a b = alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e := by
  simp only [Pg.al, he]; rfl
theorem sem_n (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C}
    (he : pg.arms[t]? = none) : pg.sem (.c t x l r) a b = rk.dflt := by simp only [Pg.sem, he]
theorem al_n (pg : Pg rk) {t : Nat} {x : BitVec 64} {l r : C} {a : BitVec 64} {b : C}
    (he : pg.arms[t]? = none) : pg.al (.c t x l r) a b = 0 := by simp only [Pg.al, he]

/-- the default exit of the loop -/
theorem loop_dflt {fi K : Nat} {env : BEnv} {H : Heap} {W : List (BitVec 64)} {h : Nat} (hi : HI W h)
    (h5 : env 5 = BitVec.ofNat 64 h) :
    ∃ E', CExec P K (fLoop fi pg) ⟨(env.set 12 0).set 11 0, H, [W]⟩ ⟨E', H, [W]⟩ ∧ Post W h W h env E' ∧
      RelK W h rk (E' 12) rk.dflt :=
  ⟨_, .loopF (by simp [vE, BExp.denote, set_eq']), ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _,
    by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), h5],
    fun i hi _ => by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]⟩,
    by rw [set_ne' _ _ (by omega), set_eq']; exact RelK.dflt _ _ _⟩

/-- **The function `F`** (index `fi`, `nl` locals, the later functions' kinds `nx`): the loop on `v` runs within
`8 (nl + 1) · depth v + KX` bytes of stack, `KX` the stack of a call of a later function -/
theorem loop_ok3 {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) (hst : pg.st = false)
    (hpg : pg.arms.length ≤ 255)
    {nx : List Kd} (htg : ∀ e ∈ pg.arms, e.tags < 256 ∧ e.okc [] nx = true) {KX Lw : Nat}
    (okx : ∀ j k, nx[j]? = some k → XOK P KX (fi + 1 + j) k (pg.X j) (pg.XA j) Lw) :
    ∀ v, LoopOK P fi pg (8 * (nl + 1) * v.depth + KX) Lw v ∧ LoopOK P fi pg (8 * (nl + 1) * v.lv.depth + KX) Lw v.lv ∧
      LoopOK P fi pg (8 * (nl + 1) * v.rv.depth + KX) Lw v.rv := by
  intro v
  induction v with
  | z =>
    have hz : LoopOK P fi pg (8 * (nl + 1) * C.z.depth + KX) Lw C.z := by
      intro a bp b pv env H W h hw hi hp rv ha hb rb hgo h5 cap
      obtain ⟨pl, pr, -, -, ht, hld⟩ := loads_exec hi rv hp (H := H)
      let env4 := (((env.set 13 (BitVec.ofNat 64 C.z.tag)).set 14 C.z.xv).set 15 pl).set 16 pr
      have k4 : ∀ i, i < 13 → env4 i = env i := fun i hi' => by
        simp only [env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
          set_ne' _ _ (by omega)]
      obtain ⟨σ', hx, E', W', hl, hpost, hrel⟩ := disp_ok (P := P) (fi := fi) (K := 0) (Q := fun σ' =>
          ∃ E' W', CExec P 0 (fLoop fi pg) σ' ⟨E', H, [W']⟩ ∧ Post W h W' h env E' ∧ RelK W' h rk (E' 12) rk.dflt)
        ht pg.arms 0 (Nat.zero_le _) (by omega) env4 H [W] (by simp [env4, set_ne', set_eq'])
        (fun e he => absurd he (by simp only [C.tag]; rw [List.getElem?_eq_none (by omega)]; simp))
        (fun _ => by
          obtain ⟨E', hx, hp', hr⟩ := loop_dflt (P := P) (pg := pg) (fi := fi) (K := 0) (env := env4) (H := H) hi
            (by rw [k4 5 (by omega)]; exact h5)
          refine ⟨E', W, hx, ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, hp'.e5, fun i hi' h5' => ?_⟩, hr⟩
          rw [hp'.glob i hi' h5', k4 i (by omega)])
      refine ⟨E', W', .loopT (by simp [vE, BExp.denote, hgo]) (.seq (.base hld) (hx.mono (Nat.zero_le _)))
        (hl.mono (Nat.zero_le _)), ?_, ?_⟩
      · simpa [Pg.al] using hpost
      · simpa [Pg.al, Pg.sem] using hrel
    exact ⟨hz, hz, hz⟩
  | c t x l r ihl ihr =>
    refine ⟨?_, ihl.1, ihr.1⟩
    intro a bp b pv env H W h hw hi hp rv ha hb rb hgo h5 cap
    obtain ⟨pl, pr, rl, rr, ht, hld⟩ := loads_exec hi rv hp (H := H)
    simp only [C.tag, C.xv, C.lv, C.rv] at rl rr ht hld
    let env4 := (((env.set 13 (BitVec.ofNat 64 t)).set 14 x).set 15 pl).set 16 pr
    have k4 : ∀ i, i < 13 → env4 i = env i := fun i hi' => by
      simp only [env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
        set_ne' _ _ (by omega)]
    generalize hfr : 8 * (nl + 1) = fr at *
    have K1 : fr * (C.c t x l r).depth + KX = fr + (fr * max l.depth r.depth + KX) := by
      simp only [C.depth]; rw [Nat.mul_add, Nat.mul_one]; omega
    have okl : BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw l pl :=
      bodyOK_mono (bodyOK_of_loopOK hst ihl.1 pl) (by have := Nat.mul_le_mul_left fr (Nat.le_max_left l.depth r.depth); omega)
    have okr : BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw r pr :=
      bodyOK_mono (bodyOK_of_loopOK hst ihr.1 pr) (by have := Nat.mul_le_mul_left fr (Nat.le_max_right l.depth r.depth); omega)
    have okg : ∀ c₁ c₂ pv, BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw (C.gch l r c₁ c₂) pv := by
      intro c₁ c₂ pv
      have hd := Nat.mul_le_mul_left fr (C.depth_gch l r c₁ c₂)
      have hg : LoopOK P fi pg (fr * (C.gch l r c₁ c₂).depth + KX) Lw (C.gch l r c₁ c₂) := by
        cases c₁ <;> cases c₂
        · exact ihl.2.1
        · exact ihl.2.2
        · exact ihr.2.1
        · exact ihr.2.2
      exact bodyOK_mono (bodyOK_of_loopOK hst hg pv) (by omega)
    have cx : Cx (P := P) (pg := pg) fi (fr * max l.depth r.depth + KX) KX Lw nx (.c t x l r) [] [] [] x l r a b env4 W h :=
      ⟨hi, by rw [k4 5 (by omega)]; exact h5, by simp [env4, set_eq', set_ne'], by rw [k4 9 (by omega)]; exact ha,
        by simp only [env4]; rw [set_ne' _ _ (by omega), set_eq']; exact rl, by simp only [env4]; rw [set_eq']; exact rr,
        by rw [k4 10 (by omega), hb]; exact rb, by simp only [env4]; rw [set_ne' _ _ (by omega), set_eq']; exact okl,
        by simp only [env4]; rw [set_eq']; exact okr, hw, by rw [k4 8 (by omega), hp]; exact rv, rfl, rfl,
        fun i h1 => absurd h1 (by simp), okx, okg⟩
    -- one arm (no split)
    have harm1 : ∀ (e : E rk rk) (env' : BEnv) (W' : List (BitVec 64)) (h' : Nat), e.tags < 256 → e.okc [] nx = true →
        Cx (P := P) (pg := pg) fi (fr * max l.depth r.depth + KX) KX Lw nx (.c t x l r) [] [] [] x l r a b env' W' h' →
        env' 11 = 1 → h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e ≤ W'.length →
        ∃ σ', CExec P (fr * (C.c t x l r).depth + KX) (arm fi e) ⟨env', H, [W']⟩ σ' ∧
          ∃ E' W'', CExec P (fr * (C.c t x l r).depth + KX) (fLoop fi pg) σ' ⟨E', H, [W'']⟩ ∧
            Post W' h' W'' (h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e) env' E' ∧
            RelK W'' (h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e) rk (E' 12) (ev (selfS pg l r (.c t x l r) []) x l r a b e) := by
      intro e env' W' h' htge hoke cx' hgo cap
      match hta : e.tail? with
      | none =>
        simp only [arm, hta]
        obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hPf (K := fr * (C.c t x l r).depth + KX) (by omega) (by omega)
          e [] [] [] 12 17 env' H W' h' (by omega) (by simp) (by simp) (by omega) (by omega) (by simp) htge hoke cx' cap
        refine ⟨_, .seq x₁ (.base (asg_exec _ _ _)), E₁.set 11 ((kE 0).denote _), W₁, .loopF (by simp [vE, BExp.denote, set_eq', kE]),
          ⟨p₁.len, p₁.agr, p₁.hi, p₁.hle, by rw [set_ne' _ _ (by omega)]; exact p₁.e5, fun i hi' h5' => ?_⟩, ?_⟩
        · rw [set_ne' _ _ (by omega), p₁.glob i hi' h5']
        · rw [set_ne' _ _ (by omega)]; exact v₁
      | some (ch, ea, eb) =>
        have hee := E.tail?_some hta
        subst hee
        simp only [arm, hta]
        simp only [E.tags] at htge
        simp only [E.okc, Bool.and_eq_true] at hoke
        simp only [alE] at cap ⊢
        simp only [ev]
        obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hPf (K := fr * (C.c t x l r).depth + KX) (by omega) (by omega)
          ea [] [] [] 17 18 env' H W' h'
          (by omega) (by simp) (by simp) (by omega) (by omega) (by simp) (by omega) hoke.1 cx' (by omega)
        have c₁ := cx'.step p₁ (by intro i hi'; simp at hi'; exact k₁ i (by omega) (by omega) (by omega)) (by simp)
        obtain ⟨E₂, W₂, x₂, p₂, k₂, v₂⟩ := comp_ok hPf (K := fr * (C.c t x l r).depth + KX) (by omega) (by omega)
          eb [] [] [] 18 19 E₁ H W₁ _
          (by omega) (by simp) (by simp) (by omega) (by omega) (by simp) (by omega) hoke.2 c₁ (by have := p₁.len; omega)
        have c₂ := c₁.step p₂ (by intro i hi'; simp at hi'; exact k₂ i (by omega) (by omega) (by omega)) (by simp)
        have p₂' := p₁.trans p₂
        generalize alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b ea = A1 at *
        generalize alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b eb = A2 at *
        rw [selfA_eq] at cap ⊢; rw [selfS_eq]
        let E₃ := ((E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)).set 9 ((vE 17).denote (E₂.set 8
          ((vE (if ch then 16 else 15)).denote E₂)))).set 10 ((vE 18).denote ((E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)).set 9
          ((vE 17).denote (E₂.set 8 ((vE (if ch then 16 else 15)).denote E₂)))))
        have k3 : ∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → E₃ i = E₂ i := fun i a1 a2 a3 => by
          simp only [E₃]; rw [set_ne' _ _ a3, set_ne' _ _ a2, set_ne' _ _ a1]
        have e8 : E₃ 8 = E₂ (if ch then 16 else 15) := by simp [E₃, set_ne', set_eq', vE, BExp.denote]
        have e9 : E₃ 9 = ev (selfS pg l r (.c t x l r) []) x l r a b ea := by
          simp only [E₃]; rw [set_ne' _ _ (by omega), set_eq']; simp only [vE, BExp.denote]
          rw [set_ne' _ _ (by omega), k₂ 17 (by omega) (by omega) (by omega)]; exact v₁
        have e10 : E₃ 10 = E₂ 18 := by simp only [E₃]; rw [set_eq']; simp only [vE, BExp.denote]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
        have hgo3 : E₃ 11 = 1 := by
          rw [k3 11 (by omega) (by omega) (by omega), k₂ 11 (by omega) (by omega) (by omega),
            k₁ 11 (by omega) (by omega) (by omega)]
          exact hgo
        have h53 : E₃ 5 = BitVec.ofNat 64 (h' + 4 * A1 + 4 * A2) := by rw [k3 5 (by omega) (by omega) (by omega)]; exact p₂.e5
        have hrv : Rp W₂ (h' + 4 * A1 + 4 * A2) (E₂ (if ch then 16 else 15)) (if ch then r else l) := by
          cases ch <;> first | exact c₂.rl | exact c₂.rr
        have ihc : LoopOK P fi pg (fr * (C.c t x l r).depth + KX) Lw (if ch then r else l) := by
          cases ch
          · intro a1 b1 c1 d1 e1 f1 g1 h1 w1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            obtain ⟨E', W', hx, hq, hr⟩ := ihl.1 a1 b1 c1 d1 e1 f1 g1 h1 w1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            exact ⟨E', W', hx.mono (by have := Nat.mul_le_mul_left fr (show l.depth ≤ (C.c t x l r).depth by
              simp only [C.depth]; omega); omega), hq, hr⟩
          · intro a1 b1 c1 d1 e1 f1 g1 h1 w1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            obtain ⟨E', W', hx, hq, hr⟩ := ihr.1 a1 b1 c1 d1 e1 f1 g1 h1 w1 i1 j1 k1 l1 m1 n1 o1 p1 q1
            exact ⟨E', W', hx.mono (by have := Nat.mul_le_mul_left fr (show r.depth ≤ (C.c t x l r).depth by
              simp only [C.depth]; omega); omega), hq, hr⟩
        obtain ⟨E', W', hl, hpost, hrel⟩ := ihc _ (E₂ 18) _ _ E₃ H W₂ _ c₂.lw p₂.hi e8 hrv e9 e10 (by rw [e10] at *; exact v₂)
          hgo3 h53 (by rw [p₂'.len]; omega)
        refine ⟨_, .seq x₁ (.seq x₂ (.base (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (asg_exec _ _ _))))), E', W', hl,
          ?_, ?_⟩
        · rw [show h' + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r (.c t x l r) []) x l r a b ea)
            (ev (selfS pg l r (.c t x l r) []) x l r a b eb)) = h' + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
            (ev (selfS pg l r (.c t x l r) []) x l r a b ea) (ev (selfS pg l r (.c t x l r) []) x l r a b eb) by omega]
          refine ⟨hpost.len.trans p₂'.len, p₂'.agr.trans hpost.agr p₂'.hle, hpost.hi, Nat.le_trans p₂'.hle hpost.hle,
            hpost.e5, fun i hi' h5' => ?_⟩
          rw [hpost.glob i hi' h5', k3 i (by omega) (by omega) (by omega), p₂'.glob i hi' h5']
        · rw [show h' + 4 * (A1 + A2 + pg.al (if ch then r else l) (ev (selfS pg l r (.c t x l r) []) x l r a b ea)
            (ev (selfS pg l r (.c t x l r) []) x l r a b eb)) = h' + 4 * A1 + 4 * A2 + 4 * pg.al (if ch then r else l)
            (ev (selfS pg l r (.c t x l r) []) x l r a b ea) (ev (selfS pg l r (.c t x l r) []) x l r a b eb) by omega]
          exact hrel
    -- an arm, split at its `ite`s (a call in a branch continues the loop)
    have harmT : ∀ (f : Nat) (e : E rk rk) (env' : BEnv) (W' : List (BitVec 64)) (h' : Nat), e.tags < 256 → e.okc [] nx = true →
        Cx (P := P) (pg := pg) fi (fr * max l.depth r.depth + KX) KX Lw nx (.c t x l r) [] [] [] x l r a b env' W' h' →
        env' 11 = 1 → h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e ≤ W'.length →
        ∃ σ', CExec P (fr * (C.c t x l r).depth + KX) (armT fi f e) ⟨env', H, [W']⟩ σ' ∧
          ∃ E' W'', CExec P (fr * (C.c t x l r).depth + KX) (fLoop fi pg) σ' ⟨E', H, [W'']⟩ ∧
            Post W' h' W'' (h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e) env' E' ∧
            RelK W'' (h' + 4 * alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b e) rk (E' 12) (ev (selfS pg l r (.c t x l r) []) x l r a b e) := by
      intro f
      induction f with
      | zero => intro e env' W' h' a1 a2 a3 a4 a5; exact harm1 e env' W' h' a1 a2 a3 a4 a5
      | succ f ih =>
        intro e env' W' h' htge hoke cx' hgo' cap
        match hti : e.ite? with
        | none =>
          simp only [armT, hti]; exact harm1 e env' W' h' htge hoke cx' hgo' cap
        | some (c, e₁, e₂) =>
          have hee := E.ite?_some hti
          subst hee
          simp only [armT, hti]
          simp only [E.tags] at htge
          simp only [E.okc, Bool.and_eq_true] at hoke
          simp only [alE] at cap ⊢
          simp only [ev]
          obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hPf (K := (fr * (C.c t x l r).depth + KX)) (by omega) (by omega)
            c [] [] [] 17 18 env' H W' h'
            (by omega) (by simp) (by simp) (by omega) (by omega) (by simp) (by omega) hoke.1.1 cx' (by omega)
          have c₁ := cx'.step p₁ (by intro i hi'; simp at hi'; exact k₁ i (by omega) (by omega) (by omega)) (by simp)
          have hgo1 : E₁ 11 = 1 := by rw [k₁ 11 (by omega) (by omega) (by omega)]; exact hgo'
          simp only [RelK] at v₁
          generalize alE (selfS pg l r (.c t x l r) []) (selfA pg l r) x l r a b c = A1 at *
          by_cases hz : ev (selfS pg l r (.c t x l r) []) x l r a b c = 0
          · rw [if_pos hz] at cap ⊢; rw [if_pos hz]
            obtain ⟨σ', x₂, E', W'', hl, hpost, hrel⟩ := ih e₂ E₁ W₁ _ (by omega) hoke.2 c₁ hgo1
              (by have := p₁.len; omega)
            refine ⟨σ', .seq x₁ (.iteF (by simp only [vE, BExp.denote]; rw [v₁, hz]) x₂), E', W'', hl, ?_, ?_⟩
            · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans hpost
            · rw [Nat.mul_add, ← Nat.add_assoc]; exact hrel
          · rw [if_neg hz] at cap ⊢; rw [if_neg hz]
            obtain ⟨σ', x₂, E', W'', hl, hpost, hrel⟩ := ih e₁ E₁ W₁ _ (by omega) hoke.1.2 c₁ hgo1
              (by have := p₁.len; omega)
            refine ⟨σ', .seq x₁ (.iteT (by simp only [vE, BExp.denote]; rw [v₁]; exact hz) x₂), E', W'', hl, ?_, ?_⟩
            · rw [Nat.mul_add, ← Nat.add_assoc]; exact p₁.trans hpost
            · rw [Nat.mul_add, ← Nat.add_assoc]; exact hrel
    have harm : ∀ e, pg.arms[t - 0]? = some e → ∃ σ', CExec P (fr * (C.c t x l r).depth + KX) (armT fi 8 e) ⟨env4, H, [W]⟩ σ' ∧
        (∃ E' W', CExec P (fr * (C.c t x l r).depth + KX) (fLoop fi pg) σ' ⟨E', H, [W']⟩ ∧
          Post W h W' (h + 4 * pg.al (.c t x l r) a b) env E' ∧
          RelK W' (h + 4 * pg.al (.c t x l r) a b) rk (E' 12) (pg.sem (.c t x l r) a b)) := by
      intro e he
      rw [Nat.sub_zero] at he
      obtain ⟨htge, hoke⟩ := htg e (List.mem_of_getElem? he)
      rw [al_c pg he] at cap ⊢; rw [sem_c pg he]
      obtain ⟨σ', hx, E', W', hl, hpost, hrel⟩ := harmT 8 e env4 W h htge hoke cx (by simp [env4, set_ne', hgo]) cap
      exact ⟨σ', hx, E', W', hl, ⟨hpost.len, hpost.agr, hpost.hi, hpost.hle, hpost.e5, fun i hi' h5' => by
        rw [hpost.glob i hi' h5', k4 i (by omega)]⟩, hrel⟩

    obtain ⟨σ', hx, E', W', hl, hpost, hrel⟩ := disp_ok (P := P) (fi := fi) (K := fr * (C.c t x l r).depth + KX) (Q := fun σ' =>
        ∃ E' W', CExec P (fr * (C.c t x l r).depth + KX) (fLoop fi pg) σ' ⟨E', H, [W']⟩ ∧
          Post W h W' (h + 4 * pg.al (.c t x l r) a b) env E' ∧
          RelK W' (h + 4 * pg.al (.c t x l r) a b) rk (E' 12) (pg.sem (.c t x l r) a b))
      ht pg.arms 0 (Nat.zero_le _) (by omega) env4 H [W] (by simp [env4, set_ne', set_eq'])
      harm
      (fun hn => by
        rw [Nat.sub_zero] at hn
        obtain ⟨E', hx, hp', hr⟩ := loop_dflt (P := P) (pg := pg) (fi := fi) (K := fr * (C.c t x l r).depth + KX)
          (env := env4) (H := H) hi (by rw [k4 5 (by omega)]; exact h5)
        refine ⟨E', W, hx, ?_, ?_⟩
        · rw [al_n pg hn, Nat.mul_zero, Nat.add_zero]
          exact ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, hp'.e5, fun i hi' h5' => by
            rw [hp'.glob i hi' h5', k4 i (by omega)]⟩
        · rw [al_n pg hn, sem_n pg hn, Nat.mul_zero, Nat.add_zero]; exact hr)
    exact ⟨E', W', .loopT (by simp [vE, BExp.denote, hgo]) (.seq (.base hld) hx) hl, hpost, hrel⟩

/-- **The function `F`** (index `fi`, `nl` locals, the later functions' kinds `nx`): the loop on `v` runs within
`8 (nl + 1) · depth v + KX` bytes of stack, `KX` the stack of a call of a later function -/
theorem loop_ok {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) (hst : pg.st = false)
    (hpg : pg.arms.length ≤ 255)
    {nx : List Kd} (htg : ∀ e ∈ pg.arms, e.tags < 256 ∧ e.okc [] nx = true) {KX Lw : Nat}
    (okx : ∀ j k, nx[j]? = some k → XOK P KX (fi + 1 + j) k (pg.X j) (pg.XA j) Lw) :
    ∀ v, LoopOK P fi pg (8 * (nl + 1) * v.depth + KX) Lw v := fun v => (loop_ok3 hPf hst hpg htg okx v).1

/-! ## the straight-line body (`Pg.st`) -/

theorem set_same (env : BEnv) (v : Nat) : env.set v (env v) = env := by
  funext i; simp only [BEnv.set]; split <;> simp_all


/-- a run of the straight-line body of `F` on `v` -/
def LoopOKS (P : Prog) (fi : Nat) (pg : Pg rk) (K Lw : Nat) (v : C) : Prop :=
  ∀ (a bp : BitVec 64) (b : C) (pv : BitVec 64) (env : BEnv) (H : Heap) (W : List (BitVec 64)) (h : Nat),
    W.length ≤ Lw → HI W h → env 8 = pv → Rp W h pv v → env 9 = a → env 10 = bp → Rp W h bp b →
    env 5 = BitVec.ofNat 64 h → h + 4 * pg.al v a b ≤ W.length →
    ∃ E' W', CExec P K (fLoopS fi pg) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      Post W h W' (h + 4 * pg.al v a b) env E' ∧ RelK W' (h + 4 * pg.al v a b) rk (E' 12) (pg.sem v a b)

theorem bodyOK_of_loopOKS {fi K Lw : Nat} {v : C} (hst : pg.st = true) (hl : LoopOKS P fi pg K Lw v)
    (pv : BitVec 64) : BodyOK P pg fi K Lw v pv := by
  intro a bp b g H W h hw hi rv rb cap h5
  let env := callEnv g [pv, a, bp]
  have e5 : env 5 = BitVec.ofNat 64 h := by simp only [env, callEnv, if_pos (show 5 < 8 by omega)]; exact h5
  obtain ⟨E', W', hx, hp, hr⟩ := hl a bp b pv (env.set 11 ((kE 1).denote env)) H W h hw hi rfl rv rfl rfl rb
    (by rw [set_ne' _ _ (by omega)]; exact e5) cap
  refine ⟨E', W', .seq (.base (asg_exec _ _ _)) (by rw [fLoopX_t hst]; exact hx),
    ⟨hp.len, hp.agr, hp.hi, hp.hle, hp.e5, fun i hi h5' => ?_⟩, hr⟩
  rw [hp.glob i hi h5', set_ne' _ _ (by omega)]
  simp only [env, callEnv, if_pos hi]

theorem dispS_skip {fi K t : Nat} (ht : t < 256) :
    ∀ (es : List (E rk rk)) (i : Nat), t < i → i + es.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 13 = BitVec.ofNat 64 t → CExec P K (dispS fi es i) ⟨env, H, Wh⟩ ⟨env, H, Wh⟩
  | [], i, _, _, env, H, Wh, _ => by
    have := CExec.base (P := P) (k := K) (asg_exec 12 (vE 12) ⟨env, H, Wh⟩)
    simp [vE, BExp.denote, set_same] at this; exact this
  | e :: es, i, hi, hl, env, H, Wh, he => by
    simp only [List.length_cons] at hl
    have hn := CExec.base (P := P) (k := K) (asg_exec 12 (vE 12) ⟨env, H, Wh⟩)
    simp only [vE, BExp.denote, set_same] at hn
    exact .seq (.iteF (by show BExp.denote env (eqE 13 i) = 0; rw [eqE_den env 13 i t he ht (by omega), if_neg (by omega)]) hn)
      (dispS_skip ht es (i + 1) (by omega) (by omega) env H Wh he)

theorem dispS_ok {fi K t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (es : List (E rk rk)) (i : Nat), i ≤ t → i + es.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 13 = BitVec.ofNat 64 t →
      (∀ e, es[t - i]? = some e → ∃ σ', CExec P K (armN fi e) ⟨env, H, Wh⟩ σ' ∧ Q σ' ∧ σ'.env 13 = env 13) →
      (es[t - i]? = none → Q ⟨env, H, Wh⟩) →
      ∃ σ', CExec P K (dispS fi es i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => by
    have := CExec.base (P := P) (k := K) (asg_exec 12 (vE 12) ⟨env, H, Wh⟩)
    simp only [vE, BExp.denote, set_same] at this
    exact ⟨_, this, hn rfl⟩
  | e :: es, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨⟨E', H', Wh'⟩, hx, hq, h13⟩ := hs e (by simp)
      exact ⟨_, .seq (.iteT (by rw [eqE_den env 13 t t he ht ht, if_pos rfl]; decide) hx)
        (dispS_skip ht es (t + 1) (by omega) (by omega) E' H' Wh' (by simp only at h13; rw [h13, he])), hq⟩
    · have hnop := CExec.base (P := P) (k := K) (asg_exec 12 (vE 12) ⟨env, H, Wh⟩)
      simp only [vE, BExp.denote, set_same] at hnop
      obtain ⟨σ', hx, hq⟩ := dispS_ok ht es (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .seq (.iteF (by show BExp.denote env (eqE 13 i) = 0; rw [eqE_den env 13 i t he ht (by omega), if_neg h]) hnop) hx, hq⟩

/-- **The function `F`, straight-line** (`pg.st`): as `loop_ok3`, every call a real call -/
theorem straight_ok3 {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) (hst : pg.st = true)
    (hpg : pg.arms.length ≤ 255)
    {nx : List Kd} (htg : ∀ e ∈ pg.arms, e.tags < 256 ∧ e.okc [] nx = true) {KX Lw : Nat}
    (okx : ∀ j k, nx[j]? = some k → XOK P KX (fi + 1 + j) k (pg.X j) (pg.XA j) Lw) :
    ∀ v, LoopOKS P fi pg (8 * (nl + 1) * v.depth + KX) Lw v ∧ LoopOKS P fi pg (8 * (nl + 1) * v.lv.depth + KX) Lw v.lv ∧
      LoopOKS P fi pg (8 * (nl + 1) * v.rv.depth + KX) Lw v.rv := by
  intro v
  induction v with
  | z =>
    have hz : LoopOKS P fi pg (8 * (nl + 1) * C.z.depth + KX) Lw C.z := by
      intro a bp b pv env H W h hw hi hp rv ha hb rb h5 cap
      obtain ⟨pl, pr, -, -, ht, hld⟩ := loads_exec hi rv hp (H := H)
      let env5 := ((((env.set 13 (BitVec.ofNat 64 C.z.tag)).set 14 C.z.xv).set 15 pl).set 16 pr).set 12 ((kE 0).denote
        ((((env.set 13 (BitVec.ofNat 64 C.z.tag)).set 14 C.z.xv).set 15 pl).set 16 pr))
      have k5 : ∀ i, i < 12 → env5 i = env i := fun i hi' => by
        simp only [env5]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
          set_ne' _ _ (by omega)]
      obtain ⟨σ', hx, hq⟩ := dispS_ok (P := P) (fi := fi) (K := 8 * (nl + 1) * C.z.depth + KX)
        (Q := fun σ' => σ' = ⟨env5, H, [W]⟩) ht pg.arms 0 (Nat.zero_le _) (by omega) env5 H [W]
        (by simp [env5, set_ne', set_eq'])
        (fun e he => absurd he (by simp only [C.tag]; rw [List.getElem?_eq_none (by omega)]; simp))
        (fun _ => rfl)
      subst hq
      refine ⟨env5, W, .seq (.base (.seq hld (asg_exec _ _ _))) hx, ?_, ?_⟩
      · simp only [Pg.al, Nat.mul_zero, Nat.add_zero]
        exact ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, by rw [k5 5 (by omega)]; exact h5, fun i hi' _ => k5 i (by omega)⟩
      · simp only [Pg.al, Pg.sem, Nat.mul_zero, Nat.add_zero]
        have : env5 12 = 0 := by simp [env5, set_eq', kE, BExp.denote]
        rw [this]; exact RelK.dflt _ _ _
    exact ⟨hz, hz, hz⟩
  | c t x l r ihl ihr =>
    refine ⟨?_, ihl.1, ihr.1⟩
    intro a bp b pv env H W h hw hi hp rv ha hb rb h5 cap
    obtain ⟨pl, pr, rl, rr, ht, hld⟩ := loads_exec hi rv hp (H := H)
    simp only [C.tag, C.xv, C.lv, C.rv] at rl rr ht hld
    let env4 := (((env.set 13 (BitVec.ofNat 64 t)).set 14 x).set 15 pl).set 16 pr
    let env5 := env4.set 12 ((kE 0).denote env4)
    have k5 : ∀ i, i < 12 → env5 i = env i := fun i hi' => by
      simp only [env5, env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
        set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
    generalize hfr : 8 * (nl + 1) = fr at *
    have K1 : fr * (C.c t x l r).depth + KX = fr + (fr * max l.depth r.depth + KX) := by
      simp only [C.depth]; rw [Nat.mul_add, Nat.mul_one]; omega
    have okl : BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw l pl :=
      bodyOK_mono (bodyOK_of_loopOKS hst ihl.1 pl) (by have := Nat.mul_le_mul_left fr (Nat.le_max_left l.depth r.depth); omega)
    have okr : BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw r pr :=
      bodyOK_mono (bodyOK_of_loopOKS hst ihr.1 pr) (by have := Nat.mul_le_mul_left fr (Nat.le_max_right l.depth r.depth); omega)
    have okg : ∀ c₁ c₂ pv, BodyOK P pg fi (fr * max l.depth r.depth + KX) Lw (C.gch l r c₁ c₂) pv := by
      intro c₁ c₂ pv
      have hd := Nat.mul_le_mul_left fr (C.depth_gch l r c₁ c₂)
      have hg : LoopOKS P fi pg (fr * (C.gch l r c₁ c₂).depth + KX) Lw (C.gch l r c₁ c₂) := by
        cases c₁ <;> cases c₂
        · exact ihl.2.1
        · exact ihl.2.2
        · exact ihr.2.1
        · exact ihr.2.2
      exact bodyOK_mono (bodyOK_of_loopOKS hst hg pv) (by omega)
    have cx : Cx (P := P) (pg := pg) fi (fr * max l.depth r.depth + KX) KX Lw nx (.c t x l r) [] [] [] x l r a b env5 W h :=
      ⟨hi, by rw [k5 5 (by omega)]; exact h5, by simp [env5, env4, set_eq', set_ne'], by rw [k5 9 (by omega)]; exact ha,
        by simp only [env5, env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_eq']; exact rl,
        by simp only [env5, env4]; rw [set_ne' _ _ (by omega), set_eq']; exact rr,
        by rw [k5 10 (by omega), hb]; exact rb,
        by simp only [env5, env4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_eq']; exact okl,
        by simp only [env5, env4]; rw [set_ne' _ _ (by omega), set_eq']; exact okr, hw,
        by rw [k5 8 (by omega), hp]; exact rv, rfl, rfl, fun i h1 => absurd h1 (by simp), okx, okg⟩
    have e13 : env5 13 = BitVec.ofNat 64 t := by simp [env5, env4, set_ne', set_eq']
    obtain ⟨σ', hx, E', W', hq, hpost, hrel⟩ := dispS_ok (P := P) (fi := fi) (K := fr * (C.c t x l r).depth + KX)
      (Q := fun σ' => ∃ E' W', σ' = ⟨E', H, [W']⟩ ∧ Post W h W' (h + 4 * pg.al (.c t x l r) a b) env E' ∧
        RelK W' (h + 4 * pg.al (.c t x l r) a b) rk (E' 12) (pg.sem (.c t x l r) a b))
      ht pg.arms 0 (Nat.zero_le _) (by omega) env5 H [W] e13
      (fun e he => by
        rw [Nat.sub_zero] at he
        obtain ⟨htge, hoke⟩ := htg e (List.mem_of_getElem? he)
        rw [al_c pg he] at cap; rw [al_c pg he, sem_c pg he]
        obtain ⟨E₁, W₁, x₁, p₁, k₁, v₁⟩ := comp_ok hPf (K := fr * (C.c t x l r).depth + KX) (by omega) (by omega)
          e [] [] [] 12 17 env5 H W h (by omega) (by simp) (by simp) (by omega) (by omega) (by simp) htge hoke cx cap
        refine ⟨_, .seq x₁ (.base (asg_exec _ _ _)), ⟨E₁.set 11 ((kE 0).denote E₁), W₁, rfl,
          ⟨p₁.len, p₁.agr, p₁.hi, p₁.hle, by rw [set_ne' _ _ (by omega)]; exact p₁.e5, fun i hi' h5' => ?_⟩, ?_⟩, ?_⟩
        · rw [set_ne' _ _ (by omega), p₁.glob i hi' h5', k5 i (by omega)]
        · rw [set_ne' _ _ (by omega)]; exact v₁
        · simp only; rw [set_ne' _ _ (by omega), k₁ 13 (by omega) (by omega) (by omega)])
      (fun hn => by
        rw [Nat.sub_zero] at hn
        refine ⟨env5, W, rfl, ?_, ?_⟩
        · rw [al_n pg hn, Nat.mul_zero, Nat.add_zero]
          exact ⟨rfl, Agree.refl _ _, hi, Nat.le_refl _, by rw [k5 5 (by omega)]; exact h5, fun i hi' _ => k5 i (by omega)⟩
        · rw [al_n pg hn, sem_n pg hn, Nat.mul_zero, Nat.add_zero]
          have : env5 12 = 0 := by simp [env5, set_eq', kE, BExp.denote]
          rw [this]; exact RelK.dflt _ _ _)
    subst hq
    exact ⟨E', W', .seq (.base (.seq hld (asg_exec _ _ _))) hx, hpost, hrel⟩

/-- a call of `F` as a later function: its meaning and cells, within `8 (nl + 1) (Lw + 1) + KX` bytes of stack -/
theorem xok_of {fi nl : Nat} (hPf : ∃ hf : fi < P.length, P[fi] = fFn fi nl pg) (hpg : pg.arms.length ≤ 255)
    {nx : List Kd} (htg : ∀ e ∈ pg.arms, e.tags < 256 ∧ e.okc [] nx = true) {KX Lw : Nat}
    (okx : ∀ j k, nx[j]? = some k → XOK P KX (fi + 1 + j) k (pg.X j) (pg.XA j) Lw) :
    XOK P (8 * (nl + 1) * (Lw + 1) + KX) fi rk (fun v a b => rk.pair (pg.sem v a b)) pg.al Lw := by
  intro v b pv a bp d pvar avar bvar env H W h hd hw hi h5 hp ha hb rv rb cap
  obtain ⟨-, hdep⟩ := rv.depth
  have hlt := rv.lt4 hi.h4
  have hdl : v.depth ≤ Lw := by have := hi.hle; omega
  have bok : BodyOK P pg fi (8 * (nl + 1) * v.depth + KX) Lw v pv := by
    cases hst : pg.st
    · exact bodyOK_of_loopOK hst (loop_ok hPf hst hpg htg okx v) pv
    · exact bodyOK_of_loopOKS hst (straight_ok3 hPf hst hpg htg okx v).1 pv
  have hK : 8 * (nl + 1) + (8 * (nl + 1) * v.depth + KX) ≤ 8 * (nl + 1) * (Lw + 1) + KX := by
    have := Nat.mul_le_mul_left (8 * (nl + 1)) (Nat.succ_le_succ hdl)
    simp only [Nat.mul_add_one, Nat.mul_succ] at this ⊢; omega
  obtain ⟨E', W', hx, hp', hk, hr⟩ := call_ok hPf (K := 8 * (nl + 1) * (Lw + 1) + KX) hK bok hw hi h5 hp ha hb rv rb
    cap hd
  exact ⟨E', W', hx, hp', hk, by rw [Kd.pick_pair]; exact hr⟩

theorem semX_cons (k : Kd) (p : Pg k) (ps : List (Σ k : Kd, Pg k)) (j : Nat) :
    semX (⟨k, p⟩ :: ps) (j + 1) = semX ps j := rfl
theorem alX_cons (k : Kd) (p : Pg k) (ps : List (Σ k : Kd, Pg k)) (j : Nat) :
    alX (⟨k, p⟩ :: ps) (j + 1) = alX ps j := rfl

/-- **The functions of a program** (`ps` at indices `q, q + 1, …`, each calling only later ones): each call runs
within `8 (nl + 1) (Lw + 1)` bytes of stack per function from it to the end -/
theorem chain_ok {nl Lw : Nat} : ∀ (ps : List (Σ k : Kd, Pg k)) (q : Nat),
    (∀ i (hi : i < ps.length), P[q + i]? = some (fFn (q + i) nl ps[i].2)) → Chain ps →
    (∀ i (hi : i < ps.length), ps[i].2.arms.length ≤ 255 ∧
      ∀ e : E ps[i].1 ps[i].1, e ∈ ps[i].2.arms → e.tags < 256 ∧ e.okc [] ((ps.drop (i + 1)).map (·.1)) = true) →
    ∀ j (hj : j < ps.length), XOK P (8 * (nl + 1) * (Lw + 1) * (ps.length - j)) (q + j) ps[j].1 (semX ps j) (alX ps j) Lw
  | [], _, _, _, _, j, hj => absurd hj (by simp)
  | ⟨k, p⟩ :: ps, q, hP, hc, hw, j, hj => by
    obtain ⟨hXX, hc'⟩ := hc
    have ih := chain_ok (Lw := Lw) ps (q + 1) (fun i hi => by
        have := hP (i + 1) (by simp; omega)
        rw [show q + 1 + i = q + (i + 1) by omega]; simpa using this) hc'
      (fun i hi => by
        have := hw (i + 1) (by simp; omega)
        simpa using this)
    cases j with
    | zero =>
      have hP0 := hP 0 (by simp)
      have hw0 := hw 0 (by simp)
      simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, Nat.add_zero] at hw0 hP0
      have hP0' : ∃ hf : q < P.length, P[q] = fFn q nl p := List.getElem?_eq_some_iff.1 hP0
      have := xok_of hP0' hw0.1 hw0.2 (KX := 8 * (nl + 1) * (Lw + 1) * ps.length) (Lw := Lw) (fun j' k' hj' => by
        obtain ⟨hlt, hk'⟩ := List.getElem?_eq_some_iff.1 hj'
        simp only [List.length_map] at hlt
        have := ih j' hlt
        simp only [List.getElem_map] at hk'
        rw [hk', ← (hXX j' hlt).1, ← (hXX j' hlt).2] at this
        refine xok_mono (by rw [show q + 1 + j' = q + 1 + j' from rfl] at this; exact this) ?_
        exact Nat.mul_le_mul_left _ (by omega))
      simp only [List.getElem_cons_zero, List.length_cons, Nat.sub_zero, Nat.add_zero]
      refine xok_mono this ?_
      rw [Nat.mul_succ (8 * (nl + 1) * (Lw + 1)) ps.length]; omega
    | succ j =>
      have := ih j (by simp at hj; omega)
      simp only [List.getElem_cons_succ, List.length_cons]
      rw [semX_cons, alX_cons, show q + (j + 1) = q + 1 + j by omega, show ps.length + 1 - (j + 1) = ps.length - j by omega]
      exact this

end Proven.Mach.Ind

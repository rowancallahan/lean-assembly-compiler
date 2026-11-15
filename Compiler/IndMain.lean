/- The whole program `indProg` (`Compiler/Ind.lean`): from the input bytes to the output bytes, once and for all. -/
import Compiler.IndDec

set_option linter.unusedVariables false

namespace Proven.Mach.Ind
open Proven.Mach

/-! ## bounds -/

variable {rk : Kd}

theorem alE_le (self : Bool → BitVec 64 → C → rk.den) (sal : Bool → BitVec 64 → C → Nat) (x : BitVec 64)
    (l r : C) (a : BitVec 64) (b : C) (Bl Br : Nat) (hl : ∀ a' b', sal false a' b' ≤ Bl)
    (hr : ∀ a' b', sal true a' b' ≤ Br) :
    ∀ {k : Kd} (e : E rk k), alE self sal x l r a b e ≤ e.mks + e.calls false * Bl + e.calls true * Br := by
  intro k e
  induction e with
  | x | a | k _ | l | r | b | nul => simp [alE, E.mks, E.calls]
  | bin op e₁ e₂ ih₁ ih₂ => simp only [alE, E.mks, E.calls, Nat.add_mul]; omega
  | mk t ex el er ihx ihl ihr => simp only [alE, E.mks, E.calls, Nat.add_mul]; omega
  | call ch ea eb iha ihb =>
    simp only [alE, E.mks, E.calls, Nat.add_mul]
    cases ch
    · have := hl (ev self x l r a b ea) (ev self x l r a b eb); simp; omega
    · have := hr (ev self x l r a b ea) (ev self x l r a b eb); simp; omega
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    simp only [alE, E.mks, E.calls]
    have m1 := Nat.mul_le_mul_right Bl (Nat.le_max_left (e₁.calls false) (e₂.calls false))
    have m2 := Nat.mul_le_mul_right Bl (Nat.le_max_right (e₁.calls false) (e₂.calls false))
    have m3 := Nat.mul_le_mul_right Br (Nat.le_max_left (e₁.calls true) (e₂.calls true))
    have m4 := Nat.mul_le_mul_right Br (Nat.le_max_right (e₁.calls true) (e₂.calls true))
    have := Nat.le_max_left e₁.mks e₂.mks; have := Nat.le_max_right e₁.mks e₂.mks
    rw [Nat.add_mul, Nat.add_mul]
    split <;> omega

theorem mks_le (pg : Pg rk) {e : E rk rk} (he : e ∈ pg.arms) : e.mks ≤ pg.M := by
  unfold Pg.M
  generalize pg.arms = es at he
  induction es with
  | nil => simp at he
  | cons e' es ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | h
    · omega
    · have := ih h; omega

/-- every arm calls each child at most once -/
def Pg.lin (pg : Pg rk) : Prop := ∀ e ∈ pg.arms, e.calls false ≤ 1 ∧ e.calls true ≤ 1

theorem al_le (pg : Pg rk) (hl : pg.lin) : ∀ (v : C) (a : BitVec 64) (b : C), pg.al v a b ≤ pg.M * v.nodes := by
  intro v
  induction v with
  | z => intro a b; simp [Pg.al]
  | c t x l r ihl ihr =>
    intro a b
    simp only [C.nodes]
    match he : pg.arms[t]? with
    | none => simp [Pg.al, he]
    | some e =>
      rw [al_c pg he]
      have hm := List.mem_of_getElem? he
      have h1 := alE_le (selfS pg l r) (selfA pg l r) x l r a b (pg.M * l.nodes) (pg.M * r.nodes)
        (fun a' b' => by simp only [selfA]; exact ihl a' b') (fun a' b' => by simp only [selfA]; exact ihr a' b') e
      have m1 := mks_le pg hm
      obtain ⟨c1, c2⟩ := hl e hm
      have e1 := Nat.mul_le_mul_right (pg.M * l.nodes) c1
      have e2 := Nat.mul_le_mul_right (pg.M * r.nodes) c2
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega

theorem flat_one {f : Fld → List UInt8} : ∀ {fs : List Fld} {a : Fld}, a ∈ fs →
    (f a).length ≤ (fs.flatMap f).length
  | c :: fs, a, ha => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 ha with rfl | ha'
    · omega
    · have := flat_one (f := f) ha'; omega

theorem flat_two {f : Fld → List UInt8} : ∀ {fs : List Fld} {a b : Fld}, a ∈ fs → b ∈ fs → a ≠ b →
    (f a).length + (f b).length ≤ (fs.flatMap f).length
  | c :: fs, a, b, ha, hb, hab => by
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · have := flat_one (f := f) hb'; omega
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have := flat_one (f := f) ha'; omega
      · have := flat_two (f := f) ha' hb' hab; omega

theorem nodes_le (sh : Shape) : ∀ v : C, v.wf sh → v.nodes ≤ (v.enc sh).length ∧ v.depth ≤ v.nodes
  | .z, h => absurd h id
  | .c t x l r, ⟨_, _, hl, hr⟩ => by
    simp only [C.nodes, C.depth, C.enc, List.length_cons]
    by_cases ml : Fld.l ∈ sh.getD t [] <;> by_cases mr : Fld.r ∈ sh.getD t [] <;> simp only [ml, mr, if_true, if_false] at hl hr
    · have := nodes_le sh l hl; have := nodes_le sh r hr
      have := flat_two (f := encF x (l.enc sh) (r.enc sh)) ml mr (by decide); simp only [encF] at this; omega
    · subst hr; have := nodes_le sh l hl
      have := flat_one (f := encF x (l.enc sh) (C.enc sh .z)) ml; simp only [encF] at this; simp only [C.nodes, C.depth]; omega
    · subst hl; have := nodes_le sh r hr
      have := flat_one (f := encF x (C.enc sh .z) (r.enc sh)) mr; simp only [encF] at this; simp only [C.nodes, C.depth]; omega
    · subst hl; subst hr; simp [C.nodes, C.depth]

/-! ## the whole program -/

theorem At.map (L : List UInt8) : At (L.map (·.toBitVec)) 0 L := fun i hi => by simp

theorem init_exec (env : BEnv) (H : Heap) (W : List (BitVec 64)) (hW : 8 ≤ W.length) (hW' : W.length < 2 ^ 60) :
    ∃ W₁, BExec (.seq (asg 4 (kE 0)) (.seq (asg 5 (kE 4)) (.seq (.store64 0 (kE 0) (kE 255))
      (.seq (.store64 0 (kE 1) (kE 0)) (.seq (.store64 0 (kE 2) (kE 0)) (.store64 0 (kE 3) (kE 0)))))))
      ⟨env, H, [W]⟩ ⟨(env.set 4 0).set 5 4, H, [W₁]⟩ ∧ W₁.length = W.length ∧ HI W₁ 4 := by
  have st : ∀ (E : BEnv) (V : List (BitVec 64)) (i c : Nat), i < 8 → i < V.length →
      BExec (.store64 0 (kE i) (kE c)) ⟨E, H, [V]⟩ ⟨E, H, [V.set i (BitVec.ofNat 64 c)]⟩ := fun E V i c h8 hi => by
    have e : (BitVec.ofNat 64 i).toNat = i := toNat_h (by omega)
    have := BExec.store64 (b := 0) (i := kE i) (e := kE c) (σ := ⟨E, H, [V]⟩) (by simp) (by
      show (BitVec.ofNat 64 i).toNat < V.length; rw [e]; exact hi)
    simp only [List.getElem_cons_zero, kE, BExp.denote, e, List.set_cons_zero] at this
    exact this
  refine ⟨_, .seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (.seq (st _ _ 0 255 (by omega) (by omega))
    (.seq (st _ _ 1 0 (by omega) (by simp; omega)) (.seq (st _ _ 2 0 (by omega) (by simp; omega))
    (st _ _ 3 0 (by omega) (by simp; omega)))))), by simp,
    ⟨⟨?_, ?_, ?_, ?_⟩, by omega, by omega, by simp; omega, by simp; omega⟩⟩ <;>
    simp [List.getElem?_set] <;> first | omega | (intro h; simp [h] at hW)

/-- the code of the second argument -/
def biC : BIn → CStmt
  | .inp => .call 9 1 []
  | .ctor t => .base (.seq (asg 11 (kE 0)) (alloc (kE t) 11 11 11 9))
  | .none => .base (asg 9 (kE 0))

def biLen (sh : Shape) : BIn → C → Nat
  | .inp, v₂ => (v₂.enc sh).length
  | _, _ => 1

theorem bi_ok {P : Prog} {sh : Shape} (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) (hsh : sh.length < 255)
    (bi : BIn) (v₂ : C) {K : Nat} (hK : bi = .inp → 48 + 48 * v₂.depth ≤ K) (hbi : ∀ t, bi = .ctor t → t < 256)
    (h2 : bi = .inp → v₂.wf sh) {env : BEnv} {I O : List (BitVec 8)} {W : List (BitVec 64)} {h c : Nat}
    (hI : I.length < 2 ^ 60) (hi : HI W h) (h5 : env 5 = BitVec.ofNat 64 h) (h4 : env 4 = BitVec.ofNat 64 c)
    (hA : bi = .inp → At I c (v₂.enc sh)) (cap : h + 4 * biLen sh bi v₂ ≤ W.length) :
    ∃ E' W' h', CExec P K (biC bi) ⟨env, [I, O], [W]⟩ ⟨E', [I, O], [W']⟩ ∧ W'.length = W.length ∧ Agree W W' h ∧
      HI W' h' ∧ h ≤ h' ∧ h' ≤ h + 4 * biLen sh bi v₂ ∧ E' 5 = BitVec.ofNat 64 h' ∧
      (∀ i, i ∉ [4, 5, 9, 11] → E' i = env i) ∧ Rp W' h' (E' 9) (bi.val v₂) := by
  cases bi with
  | inp =>
    simp only [biLen] at cap ⊢
    obtain ⟨E', W', h', x, l1, a1, i1, b1, b2, e5, -, gl, rv⟩ := dcall_ok hP1 (K' := 48 * v₂.depth) (hK rfl)
      (dec_ok hP1 hsh v₂ (h2 rfl)) (d := 9) (by omega) (H := [I, O]) rfl hI (hA rfl) hi h4 h5 cap
    exact ⟨E', W', h', x, l1, a1, i1, b1, b2, e5, fun i hi' => gl i (by simp at hi'; omega) (by simp at hi'; omega)
      (by simp at hi'; omega), rv⟩
  | ctor t =>
    simp only [biLen] at cap ⊢
    have ht := hbi t rfl
    have x := alloc_exec (H := [I, O]) (env := env.set 11 ((kE 0).denote env)) (kE t) 11 11 11 9 (by omega)
      (by rw [set_ne' _ _ (by omega)]; exact h5) (by omega) hi.big
    refine ⟨_, _, h + 4, .base (.seq (asg_exec _ _ _) x), by rw [put_length], put_agree W h _ _ _ _, HI_put hi (by omega) _ _ _ _,
      by omega, by omega, by rw [set_eq'], fun i hi' => ?_, ?_⟩
    · simp at hi'; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
    · show Rp _ _ (BEnv.set _ 5 _ 9) _
      rw [set_ne' _ _ (show (9 : Nat) ≠ 5 by omega), set_eq']
      simp only [set_eq', kE, BExp.denote, BIn.val]
      exact Rp_put hi ht (by omega) .z .z
  | none =>
    simp only [biLen] at cap ⊢
    refine ⟨_, W, h, .base (asg_exec _ _ _), rfl, Agree.refl _ _, hi, by omega, by omega, by
      rw [set_ne' _ _ (by omega)]; exact h5, fun i hi' => by simp at hi'; rw [set_ne' _ _ (by omega)], ?_⟩
    rw [set_eq']; exact .z

/-- the code of the output -/
def outC (rk : Kd) (nb : Nat) : CStmt :=
  if decide (rk = .t) = true then .seq (.base (asg 6 (kE 0))) (.call 13 2 [vE 10]) else .base (.seq (asg 6 (kE 0)) (wrB nb))

theorem out_ok {P : Prog} {sh : Shape} (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) (hsh : sh.length < 255)
    (nb : Nat) (hnb : nb ≤ 8) {K : Nat} {W : List (BitVec 64)} {h : Nat} (hK : 56 + 56 * W.length ≤ K) (hi : HI W h)
    {y : rk.den} {E : BEnv} (hy : RelK W h rk (E 10) y) {I O : List (BitVec 8)} (hO : O.length < 2 ^ 60)
    (hout : (Kd.out sh nb rk y).length ≤ O.length) :
    ∃ E', CExec P K (outC rk nb) ⟨E, [I, O], [W]⟩ ⟨E', [I, wr O 0 (Kd.out sh nb rk y)], [W]⟩ ∧
      (rk = .t → E' 6 = BitVec.ofNat 64 (Kd.out sh nb rk y).length) ∧ ∀ i, i < 8 → i ≠ 6 → E' i = E i := by
  cases rk with
  | t =>
    simp only [outC, decide_true, if_true, Kd.out] at hout ⊢
    have hd := hy.depth; have hl := hy.lt4 hi.h4; have := hi.hle
    obtain ⟨E', x, e6, k⟩ := ecall_ok hP2 (K := K) (K' := 56 * y.depth) (by omega) (enc_ok hP2 hsh y) hO hi hy
      (pvar := 10) (env := E.set 6 ((kE 0).denote E)) (j := 0) (I := I)
      (by rw [set_ne' _ _ (by omega)]) (by rw [set_eq']; rfl) (by omega)
    exact ⟨E', .seq (.base (asg_exec _ _ _)) x, fun _ => by rw [e6, Nat.zero_add],
      fun i hi' n6 => by rw [k i n6 (by omega), set_ne' _ _ n6]⟩
  | w =>
    simp only [outC, Kd.out, show decide (Kd.w = Kd.t) = false from rfl, Bool.false_eq_true, if_false] at hout ⊢
    have hl : (List.take nb (leN 8 (BitVec.toNat y))).length = nb := by simp [leN_length]; omega
    have := wrB_ok y 0 I O hO nb hnb (by omega) (E.set 6 ((kE 0).denote E)) [W] (by rw [set_eq']; rfl)
      (by rw [set_ne' _ _ (by omega)]; exact hy)
    exact ⟨_, .base (.seq (asg_exec _ _ _) this), ⟨(fun h => by cases h), fun i hi' n6 => set_ne' _ _ n6⟩⟩

variable (sh : Shape) (pg : Pg rk) (bi : BIn) (a0 : BitVec 64) (nb : Nat)

/-- **The whole program**: on the bytes of `v₁` (and `v₂`), `main` leaves the bytes of `F v₁ a0 b` in the output
block (`b` = `v₂`, a fresh nullary constructor, or `z`), using `56 + 136 (1 + n + |W|)` bytes of stack for `n` input
bytes and a word block `W` of at least `8 + 4 (M + 1) n` words (`M` = cells allocated per call) -/
theorem ind_ok (hsh : sh.length < 255) (hn : pg.arms.length ≤ 255) (htg : ∀ e ∈ pg.arms, e.tags < 256)
    (hlin : pg.lin) (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (v₁ v₂ : C) (h1 : v₁.wf sh) (h2 : bi = .inp → v₂.wf sh) (O : List (BitVec 8)) (W₀ : List (BitVec 64))
    (env : BEnv) (res : Nat) (hres : res < 8)
    (hI : (inBytes sh bi v₁ v₂).length < 2 ^ 59) (hW : W₀.length < 2 ^ 60)
    (cap : 8 + 4 * (pg.M + 1) * (inBytes sh bi v₁ v₂).length ≤ W₀.length) (hO : O.length < 2 ^ 60)
    (hout : (Kd.out sh nb rk (pg.sem v₁ a0 (bi.val v₂))).length ≤ O.length) :
    ∃ σ', CExec (indProg sh pg bi a0 nb) (56 + 136 * (1 + (inBytes sh bi v₁ v₂).length + W₀.length)) (.call res 0 [])
        ⟨env, [(inBytes sh bi v₁ v₂).map (·.toBitVec), O], [W₀]⟩ σ' ∧
      σ'.heap = [(inBytes sh bi v₁ v₂).map (·.toBitVec), wr O 0 (Kd.out sh nb rk (pg.sem v₁ a0 (bi.val v₂)))] ∧
      (rk = .t → σ'.env res = BitVec.ofNat 64 (Kd.out sh nb rk (pg.sem v₁ a0 (bi.val v₂))).length) := by
  have hP1 : ∃ hf : 1 < (indProg sh pg bi a0 nb).length, (indProg sh pg bi a0 nb)[1] = decFn sh := ⟨by simp [indProg], rfl⟩
  have hP2 : ∃ hf : 2 < (indProg sh pg bi a0 nb).length, (indProg sh pg bi a0 nb)[2] = encFn sh := ⟨by simp [indProg], rfl⟩
  have hP3 : ∃ hf : 3 < (indProg sh pg bi a0 nb).length, (indProg sh pg bi a0 nb)[3] = fFn pg := ⟨by simp [indProg], rfl⟩
  have hP0 : ∃ hf : 0 < (indProg sh pg bi a0 nb).length, (indProg sh pg bi a0 nb)[0] = mainFn bi a0 (rk = .t) nb :=
    ⟨by simp [indProg], rfl⟩
  generalize indProg sh pg bi a0 nb = P at hP0 hP1 hP2 hP3
  obtain ⟨hf0, hP0⟩ := hP0
  -- the input
  have hIl : (inBytes sh bi v₁ v₂).length = (v₁.enc sh).length + (if bi = .inp then (v₂.enc sh).length else 0) := by
    cases bi <;> simp [inBytes]
  have hA1 : At ((inBytes sh bi v₁ v₂).map (·.toBitVec)) 0 (v₁.enc sh) := by
    cases bi
    · exact (At.app (At.map _)).1
    all_goals exact At.map _
  have hA2 : bi = .inp → At ((inBytes sh bi v₁ v₂).map (·.toBitVec)) (0 + (v₁.enc sh).length) (v₂.enc sh) := by
    intro h; subst h; exact (At.app (At.map _)).2
  have hbl : (v₁.enc sh).length + biLen sh bi v₂ ≤ (inBytes sh bi v₁ v₂).length + 1 := by
    cases bi <;> simp [inBytes, biLen]
  have hd2 : bi = .inp → v₂.depth ≤ (inBytes sh bi v₁ v₂).length := by
    intro h; have := nodes_le sh v₂ (h2 h); subst h; simp [inBytes]; omega
  have hn1 := nodes_le sh v₁ h1
  have hal := al_le pg hlin v₁ a0 (bi.val v₂)
  have hMI : pg.M * v₁.nodes ≤ pg.M * (inBytes sh bi v₁ v₂).length := Nat.mul_le_mul_left _ (by omega)
  have hcap : 4 * (pg.M + 1) * (inBytes sh bi v₁ v₂).length =
      4 * (pg.M * (inBytes sh bi v₁ v₂).length) + 4 * (inBytes sh bi v₁ v₂).length := by
    rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
  generalize inBytes sh bi v₁ v₂ = I at *
  have hIB : (I.map (·.toBitVec)).length = I.length := by simp
  generalize hK : 136 * (1 + I.length + W₀.length) = K
  -- the run of `main`
  let g := callEnv env []
  obtain ⟨W₁, xi, l1, hi1⟩ := init_exec g [I.map (·.toBitVec), O] W₀ (by omega) hW
  obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, b21, b22, e25, e24, gl2, rv1⟩ := dcall_ok hP1 (K := K) (K' := 48 * v₁.depth)
    (by omega) (dec_ok hP1 hsh v₁ h1) (d := 8) (by omega) (env := (g.set 4 0).set 5 4) (H := [I.map (·.toBitVec), O])
    rfl (by omega) hA1 hi1 (by rw [set_ne' _ _ (by omega), set_eq']; rfl) (by rw [set_eq']; rfl) (by rw [l1]; omega)
  obtain ⟨E₃, W₃, h₃, x₃, l3, a3, i3, b31, b32, e35, gl3, rv2⟩ := bi_ok hP1 hsh bi v₂ (K := K)
    (fun h => by have := hd2 h; omega) hbi h2 (I := I.map (·.toBitVec)) (O := O) (by omega) i2 e25 e24 hA2
    (by rw [l2]; omega)
  let E₄ := E₃.set 11 ((BExp.const a0).denote E₃)
  have e48 : E₄ 8 = E₂ 8 := by simp only [E₄]; rw [set_ne' _ _ (by omega), gl3 8 (by simp)]
  have e49 : E₄ 9 = E₃ 9 := by simp only [E₄]; rw [set_ne' _ _ (by omega)]
  have bok := bodyOK_of_loopOK (loop_ok hP3 hn htg v₁) (E₄ 8)
  obtain ⟨E₅, W₅, x₅, p₅, k₅, v₅⟩ := call_ok hP3 (K := K) (K' := 136 * v₁.depth) (by omega) bok (d := 10)
    (pvar := 8) (avar := 11) (bvar := 9) (a' := a0) (b' := bi.val v₂) (v := v₁) (env := E₄) (H := [I.map (·.toBitVec), O]) i3
    (by simp only [E₄]; rw [set_ne' _ _ (by omega)]; exact e35) rfl (by simp only [E₄]; rw [set_eq']; first | rfl | skip) rfl
    (by rw [e48]; exact rv1.mono b31 a3) (by rw [e49]; exact rv2) (by rw [l3, l2, l1]; omega) (by omega)
  obtain ⟨E₆, x₆, e6, k₆⟩ := out_ok hP2 hsh nb hnb (K := K) (W := W₅) (by rw [p₅.len, l3, l2, l1]; omega) p₅.hi v₅
    (I := I.map (·.toBitVec)) hO hout
  have hb : CExec P K P[0].body ⟨callEnv env (([] : List BExp).map (·.denote env)), [I.map (·.toBitVec), O], [W₀]⟩
      ⟨E₆, [I.map (·.toBitVec), wr O 0 (Kd.out sh nb rk (pg.sem v₁ a0 (bi.val v₂)))], [W₅]⟩ := by
    rw [hP0]
    exact .seq (.base xi) (.seq x₂ (.seq x₃ (.seq (.base (asg_exec _ _ _)) (.seq x₅ x₆))))
  refine ⟨_, CExec.call hf0 (by rw [hP0]; rfl) (by rw [hP0]; show 56 + K ≤ _; omega) hb, rfl, fun ht => ?_⟩
  simp only [set_eq']
  rw [hP0]; subst ht
  simp only [mainFn, vE]
  exact e6 rfl

end Proven.Mach.Ind

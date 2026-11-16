/- The whole program `indProg` (`Compiler/Ind.lean`): from the input bytes to the output bytes, once and for all. -/
import Compiler.IndDec

set_option linter.unusedVariables false

namespace Proven.Mach.Ind
open Proven.Mach

/-! ## bounds -/

variable {rk : Kd}

theorem alE_le (sal : Ca) (x : BitVec 64)
    (l r : C) (a : BitVec 64) (b : C) (Bl Br : Nat) (hl : ∀ a' b', sal.f false a' b' ≤ Bl)
    (hr : ∀ a' b', sal.f true a' b' ≤ Br) :
    ∀ {k : Kd} (e : E rk k) (self : Cn rk), e.exts = 0 →
      alE self sal x l r a b e ≤ e.mks + e.calls false * Bl + e.calls true * Br := by
  intro k e
  induction e with
  | x | a | k _ | l | r | b | nul | me | var _ _ => intro self _; simp [alE, E.mks, E.calls]
  | bin op e₁ e₂ ih₁ ih₂ =>
    intro self hx; simp only [E.exts] at hx
    have := ih₁ self (by omega); have := ih₂ self (by omega)
    simp only [alE, E.mks, E.calls, Nat.add_mul]; omega
  | mk t ex el er ihx ihl ihr =>
    intro self hx; simp only [E.exts] at hx
    have := ihx self (by omega); have := ihl self (by omega); have := ihr self (by omega)
    simp only [alE, E.mks, E.calls, Nat.add_mul]; omega
  | call ch ea eb iha ihb =>
    intro self hx; simp only [E.exts] at hx
    have := iha self (by omega); have := ihb self (by omega)
    simp only [alE, E.mks, E.calls, Nat.add_mul]
    cases ch
    · have := hl (ev self x l r a b ea) (ev self x l r a b eb); simp; omega
    · have := hr (ev self x l r a b ea) (ev self x l r a b eb); simp; omega
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    intro self hx; simp only [E.exts] at hx
    have := ihc self (by omega); have := ih₁ self (by omega); have := ih₂ self (by omega)
    simp only [alE, E.mks, E.calls]
    have m1 := Nat.mul_le_mul_right Bl (Nat.le_max_left (e₁.calls false) (e₂.calls false))
    have m2 := Nat.mul_le_mul_right Bl (Nat.le_max_right (e₁.calls false) (e₂.calls false))
    have m3 := Nat.mul_le_mul_right Br (Nat.le_max_left (e₁.calls true) (e₂.calls true))
    have m4 := Nat.mul_le_mul_right Br (Nat.le_max_right (e₁.calls true) (e₂.calls true))
    have := Nat.le_max_left e₁.mks e₂.mks; have := Nat.le_max_right e₁.mks e₂.mks
    rw [Nat.add_mul, Nat.add_mul]
    split <;> omega
  | fw _ e ih => intro self hx; simp only [E.exts] at hx; have := ih self hx; simp only [alE, E.mks, E.calls]; omega
  | ft _ e ih => intro self hx; simp only [E.exts] at hx; have := ih self hx; simp only [alE, E.mks, E.calls]; omega
  | ext _ _ _ _ _ => intro self hx; simp [E.exts] at hx
  | call2 _ _ _ _ _ _ => intro self hx; simp [E.exts] at hx
  | @bind k₁ _ e₁ e₂ ih₁ ih₂ =>
    intro self hx; simp only [E.exts] at hx
    have := ih₁ self (by omega)
    have := ih₂ ⟨self.f, self.g, self.X, self.me, k₁.pair (ev self x l r a b e₁) :: self.ρ⟩ (by omega)
    simp only [alE, E.mks, E.calls, Nat.add_mul]; omega

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

/-- every arm calls each child at most once, and no later function; the kinds of its `var`s agree -/
def Pg.lin (pg : Pg rk) : Prop := ∀ e ∈ pg.arms, e.calls false ≤ 1 ∧ e.calls true ≤ 1 ∧ e.exts = 0 ∧ e.okc [] [] = true

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
      obtain ⟨c1, c2, c3, -⟩ := hl e hm
      have h1 := alE_le (selfA pg l r) x l r a b (pg.M * l.nodes) (pg.M * r.nodes)
        (fun a' b' => by simp only [selfA]; exact ihl a' b') (fun a' b' => by simp only [selfA]; exact ihr a' b') e
        (selfS pg l r (.c t x l r) []) c3
      have m1 := mks_le pg hm
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

theorem str_le (st : Nat) (v : C) (h : v.IsStr st) : v.nodes ≤ v.senc.length ∧ v.depth ≤ v.nodes := by
  obtain ⟨L, rfl, hs⟩ := IsStr.senc h
  have := str_nodes st L
  rw [hs]; simp [leN_length]; omega

/-- the nodes of a child in a slot (`f` the child, `fs'` the string): at most the bytes of its field -/
theorem slot_le (sh : Shape) (fs : List Fld) (f fs' : Fld) (v : C) (ev : List UInt8) (ih : v.wf sh → v.nodes ≤ ev.length ∧ v.depth ≤ v.nodes)
    (h : (f ∈ fs → v.wf sh) ∧ (fs' ∈ fs → v.IsStr (sTag sh)) ∧ (f ∉ fs → fs' ∉ fs → v = .z)) :
    v = .z ∨ ∃ g, g ∈ fs ∧ (g = f ∨ g = fs') ∧ (v.nodes ≤ (if g = f then ev else v.senc).length ∧ v.depth ≤ v.nodes) := by
  by_cases m : f ∈ fs
  · exact .inr ⟨f, m, .inl rfl, by simpa using ih (h.1 m)⟩
  · by_cases ms : fs' ∈ fs
    · right; refine ⟨fs', ms, .inr rfl, ?_⟩
      have : fs' ≠ f := fun e => m (e ▸ ms)
      simpa [this] using str_le _ v (h.2.1 ms)
    · exact .inl (h.2.2 m ms)

theorem nodes_le (sh : Shape) : ∀ v : C, v.wf sh → v.nodes ≤ (v.enc sh).length ∧ v.depth ≤ v.nodes
  | .z, h => absurd h id
  | .c t x l r, ⟨_, _, hl, hr⟩ => by
    simp only [C.nodes, C.depth, C.enc, List.length_cons]
    have kl := slot_le sh _ .l .sl l (l.enc sh) (nodes_le sh l) hl
    have kr := slot_le sh _ .r .sr r (r.enc sh) (nodes_le sh r) hr
    rcases kl with rfl | ⟨g, mg, eg, ng⟩ <;> rcases kr with rfl | ⟨g', mg', eg', ng'⟩
    · simp [C.nodes, C.depth]
    · have := flat_one (f := encF x (C.enc sh .z) (r.enc sh) C.z.senc r.senc) mg'
      rcases eg' with rfl | rfl <;> simp only [encF, if_true, if_false, reduceCtorEq] at this ng' <;>
        simp only [C.nodes, C.depth] <;> omega
    · have := flat_one (f := encF x (l.enc sh) (C.enc sh .z) l.senc C.z.senc) mg
      rcases eg with rfl | rfl <;> simp only [encF, if_true, if_false, reduceCtorEq] at this ng <;>
        simp only [C.nodes, C.depth] <;> omega
    · have := flat_two (f := encF x (l.enc sh) (r.enc sh) l.senc r.senc) mg mg'
        (by rcases eg with rfl | rfl <;> rcases eg' with rfl | rfl <;> decide)
      rcases eg with rfl | rfl <;> rcases eg' with rfl | rfl <;>
        simp only [encF, if_true, if_false, reduceCtorEq] at this ng ng' <;> omega

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
    (bi : BIn) (v₂ : C) {K : Nat} (hK : bi = .inp → 64 + 64 * v₂.depth ≤ K) (hbi : ∀ t, bi = .ctor t → t < 256)
    (h2 : bi = .inp → v₂.wf sh) {env : BEnv} {I O : List (BitVec 8)} {W : List (BitVec 64)} {h c : Nat}
    (hI : I.length < 2 ^ 60) (hi : HI W h) (h5 : env 5 = BitVec.ofNat 64 h) (h4 : env 4 = BitVec.ofNat 64 c)
    (hA : bi = .inp → At I c (v₂.enc sh)) (cap : h + 4 * biLen sh bi v₂ ≤ W.length) :
    ∃ E' W' h', CExec P K (biC bi) ⟨env, [I, O], [W]⟩ ⟨E', [I, O], [W']⟩ ∧ W'.length = W.length ∧ Agree W W' h ∧
      HI W' h' ∧ h ≤ h' ∧ h' ≤ h + 4 * biLen sh bi v₂ ∧ E' 5 = BitVec.ofNat 64 h' ∧
      (∀ i, i ∉ [4, 5, 9, 11] → E' i = env i) ∧ Rp W' h' (E' 9) (bi.val v₂) ∧
      E' 4 = BitVec.ofNat 64 (c + if bi = .inp then (v₂.enc sh).length else 0) := by
  cases bi with
  | inp =>
    simp only [biLen] at cap ⊢
    obtain ⟨E', W', h', x, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dcall_ok hP1 (K' := 64 * v₂.depth) (hK rfl)
      (dec_ok hP1 hsh v₂ (h2 rfl)) (d := 9) (by omega) (H := [I, O]) rfl hI (hA rfl) hi h4 h5 cap
    exact ⟨E', W', h', x, l1, a1, i1, b1, b2, e5, fun i hi' => gl i (by simp at hi'; omega) (by simp at hi'; omega)
      (by simp at hi'; omega), rv, by simpa using e4⟩
  | ctor t =>
    simp only [biLen] at cap ⊢
    have ht := hbi t rfl
    have x := alloc_exec (H := [I, O]) (env := env.set 11 ((kE 0).denote env)) (kE t) 11 11 11 9 (by omega)
      (by rw [set_ne' _ _ (by omega)]; exact h5) (by omega) hi.big
    refine ⟨_, _, h + 4, .base (.seq (asg_exec _ _ _) x), by rw [put_length], put_agree W h _ _ _ _, HI_put hi (by omega) _ _ _ _,
      by omega, by omega, by rw [set_eq'], fun i hi' => ?_, ?_, ?_⟩
    · simp at hi'; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
    · show Rp _ _ (BEnv.set _ 5 _ 9) _
      rw [set_ne' _ _ (show (9 : Nat) ≠ 5 by omega), set_eq']
      simp only [set_eq', kE, BExp.denote, BIn.val]
      exact Rp_put hi ht (by omega) .z .z
    · rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; simpa using h4
  | none =>
    simp only [biLen] at cap ⊢
    refine ⟨_, W, h, .base (asg_exec _ _ _), rfl, Agree.refl _ _, hi, by omega, by omega, by
      rw [set_ne' _ _ (by omega)]; exact h5, fun i hi' => by simp at hi'; rw [set_ne' _ _ (by omega)], ?_, ?_⟩
    · rw [set_eq']; exact .z
    · rw [set_ne' _ _ (by omega)]; simpa using h4

/-- the code of the output -/
def outC (rk : Kd) (nb : Nat) : CStmt :=
  if decide (rk = .t) = true then .seq (.base (asg 6 (kE 0))) (.call 13 2 [vE 10]) else .base (.seq (asg 6 (kE 0)) (wrB nb))

theorem out_ok {P : Prog} {sh : Shape} (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) (hsh : sh.length < 255)
    (nb : Nat) (hnb : nb ≤ 8) {K : Nat} {W : List (BitVec 64)} {h : Nat} (hK : 72 + 72 * W.length ≤ K) (hi : HI W h)
    {y : rk.den} {E : BEnv} (hy : RelK W h rk (E 10) y) {I O : List (BitVec 8)} (hO : O.length < 2 ^ 60)
    (hout : (Kd.out sh nb rk y).length ≤ O.length) :
    ∃ E', CExec P K (outC rk nb) ⟨E, [I, O], [W]⟩ ⟨E', [I, wr O 0 (Kd.out sh nb rk y)], [W]⟩ ∧
      (rk = .t → E' 6 = BitVec.ofNat 64 (Kd.out sh nb rk y).length) ∧ ∀ i, i < 8 → i ≠ 6 → E' i = E i := by
  cases rk with
  | t =>
    simp only [outC, decide_true, if_true, Kd.out] at hout ⊢
    have hd := hy.depth; have hl := hy.lt4 hi.h4; have := hi.hle
    obtain ⟨E', x, e6, k⟩ := ecall_ok hP2 (K := K) (K' := 72 * y.depth) (by omega) (enc_ok hP2 hsh y) hO hi hy
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

/-- the functions' well-formedness as a `Bool` (checked by `decide`): at most 255 arms, constructor tags below 256,
the kinds of `var` / `ext` agree (`E.okc`, with the kinds of the functions after each one) -/
def okL : List (Σ k : Kd, Pg k) → Bool
  | [] => true
  | ⟨_, p⟩ :: ps => decide (p.arms.length ≤ 255) &&
      p.arms.all (fun e => decide (e.tags < 256) && e.okc [] (ps.map (·.1))) && okL ps

theorem okL_spec : ∀ (fs : List (Σ k : Kd, Pg k)), okL fs = true → ∀ i (hi : i < fs.length),
    fs[i].2.arms.length ≤ 255 ∧
      ∀ e : E fs[i].1 fs[i].1, e ∈ fs[i].2.arms → e.tags < 256 ∧ e.okc [] ((fs.drop (i + 1)).map (·.1)) = true
  | [], _, i, hi => absurd hi (by simp)
  | ⟨k, p⟩ :: ps, h, i, hi => by
    simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero => exact ⟨h1, fun e he => by have := h2 e he; simpa using this⟩
    | succ i => have := okL_spec ps h3 i (by simp at hi; omega); simpa using this

theorem indProgM_get (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (nb nl : Nat) : ∀ i (hi : i < (⟨rk, pg⟩ :: hs).length),
    (indProgM sh shO pg hs bi ain a0 nb nl)[3 + i]? = some (fFn (3 + i) nl (⟨rk, pg⟩ :: hs)[i].2)
  | 0, _ => rfl
  | i + 1, hi => by
    simp only [List.length_cons] at hi
    simp only [indProgM, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil, List.getElem?_mapIdx, show 3 + (i + 1) - (0 + 1 + 1 + 1 + 1) = i by omega,
      List.getElem?_eq_getElem (show i < hs.length by omega), Option.map_some, show 4 + i = 3 + (i + 1) by omega]

/-- the word argument -/
theorem aC_exec (ain : Bool) (a0 av : BitVec 64) (env : BEnv) (I O : List (BitVec 8)) (Wh : WHeap) (c : Nat)
    (h4 : env 4 = BitVec.ofNat 64 c) (hA : ain = true → At I c (leN 8 av.toNat)) (hc : c + 8 < 2 ^ 60) :
    ∃ E', BExec (aC ain a0) ⟨env, [I, O], Wh⟩ ⟨E', [I, O], Wh⟩ ∧ E' 11 = (if ain then av else a0) ∧
      ∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → E' i = env i := by
  cases ain with
  | false =>
    exact ⟨_, asg_exec _ _ _, by simp [set_eq', BExp.denote], fun i h _ _ => set_ne' _ _ h⟩
  | true =>
    obtain ⟨E₁, x₁, e9, k₁⟩ := rdB_ok (leN 8 av.toNat) (leN_length 8 _) c I (hA rfl) hc 8 (Nat.le_refl _)
      (env.set 13 ((vE 9).denote env)) [I, O] Wh rfl (by rw [set_ne' _ _ (by omega)]; exact h4)
    have hv : BitVec.ofNat 64 (unle (List.drop (8 - 8) (leN 8 av.toNat))) = av := by
      rw [Nat.sub_self, List.drop_zero, unle_leN, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl,
        Nat.mod_eq_of_lt av.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨_, .seq (asg_exec _ _ _) (.seq x₁ (.seq (asg_exec _ _ _) (asg_exec _ _ _))), ?_, fun i h11 h12 h13 => ?_⟩
    · simp only [if_true]; rw [set_ne' _ _ (by omega), set_eq']; simp only [vE, BExp.denote]; rw [e9, hv]
    · simp only
      by_cases h9 : i = 9
      · subst h9; rw [set_eq']; simp only [vE, BExp.denote]
        rw [set_ne' _ _ (by omega), k₁ 13 (by omega) (by omega), set_eq']; rfl
      · rw [set_ne' _ _ h9, set_ne' _ _ h11, k₁ i h9 h12, set_ne' _ _ h13]

/-- **The whole program** (several functions): on the bytes of `v₁` (then `v₂`, then the word `av` when `ain`),
`main` leaves the bytes of `F v₁ a b` in the output block (`F` the entry `pg`, `a` = `av` or the literal `a0`, `b` =
`v₂`, a fresh nullary constructor, or `z`), using `56 + 8 (nl + 1) (n + m (1 + |W|))` bytes of stack for `n` input
bytes, `m` functions and a word block `W` of at least `8 + 4 n + 4 · (cells allocated)` words -/
theorem ind_okM (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool) (a0 : BitVec 64)
    (nb nl : Nat) (hsh : sh.length < 255) (hshO : shO.length < 255) (hnl : 16 ≤ nl)
    (hch : Chain (⟨rk, pg⟩ :: hs)) (hok : okL (⟨rk, pg⟩ :: hs) = true)
    (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (v₁ v₂ : C) (av : BitVec 64) (h1 : v₁.wf sh) (h2 : bi = .inp → v₂.wf sh) (O : List (BitVec 8))
    (W₀ : List (BitVec 64)) (env : BEnv) (res : Nat) (hres : res < 8)
    (hI : (inBytesA sh bi ain v₁ v₂ av).length < 2 ^ 59) (hW : W₀.length < 2 ^ 60)
    (cap : 8 + 4 * (inBytesA sh bi ain v₁ v₂ av).length + 4 * pg.al v₁ (if ain then av else a0) (bi.val v₂) ≤
      W₀.length) (hO : O.length < 2 ^ 60)
    (hout : (Kd.out shO nb rk (pg.sem v₁ (if ain then av else a0) (bi.val v₂))).length ≤ O.length) :
    ∃ σ', CExec (indProgM sh shO pg hs bi ain a0 nb nl)
        (56 + 8 * (nl + 1) * ((inBytesA sh bi ain v₁ v₂ av).length + (1 + hs.length) * (1 + W₀.length)))
        (.call res 0 []) ⟨env, [(inBytesA sh bi ain v₁ v₂ av).map (·.toBitVec), O], [W₀]⟩ σ' ∧
      σ'.heap = [(inBytesA sh bi ain v₁ v₂ av).map (·.toBitVec),
        wr O 0 (Kd.out shO nb rk (pg.sem v₁ (if ain then av else a0) (bi.val v₂)))] ∧
      (rk = .t → σ'.env res =
        BitVec.ofNat 64 (Kd.out shO nb rk (pg.sem v₁ (if ain then av else a0) (bi.val v₂))).length) := by
  have hP1 : ∃ hf : 1 < (indProgM sh shO pg hs bi ain a0 nb nl).length,
      (indProgM sh shO pg hs bi ain a0 nb nl)[1] = decFn sh := ⟨by simp [indProgM], rfl⟩
  have hP2 : ∃ hf : 2 < (indProgM sh shO pg hs bi ain a0 nb nl).length,
      (indProgM sh shO pg hs bi ain a0 nb nl)[2] = encFn shO := ⟨by simp [indProgM], rfl⟩
  have hP0 : ∃ hf : 0 < (indProgM sh shO pg hs bi ain a0 nb nl).length,
      (indProgM sh shO pg hs bi ain a0 nb nl)[0] = mainFn bi ain a0 (rk = .t) nb := ⟨by simp [indProgM], rfl⟩
  have xok := chain_ok (P := indProgM sh shO pg hs bi ain a0 nb nl) (nl := nl) (Lw := W₀.length) (⟨rk, pg⟩ :: hs) 3
    (indProgM_get sh shO pg hs bi ain a0 nb nl) hch (okL_spec _ hok) 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.add_zero, List.length_cons, Nat.sub_zero] at xok
  generalize indProgM sh shO pg hs bi ain a0 nb nl = P at hP0 hP1 hP2 xok
  obtain ⟨hf0, hP0⟩ := hP0
  generalize haa : (if ain then av else a0) = aa at *
  -- the input
  have hIA : inBytesA sh bi ain v₁ v₂ av = inBytes sh bi v₁ v₂ ++ (if ain then leN 8 av.toNat else []) := rfl
  have hAll := At.map (inBytesA sh bi ain v₁ v₂ av)
  rw [hIA] at hAll
  obtain ⟨hAb, hAt⟩ := At.app hAll
  rw [← hIA] at hAb hAt
  have hIl : (inBytes sh bi v₁ v₂).length = (v₁.enc sh).length + (if bi = .inp then (v₂.enc sh).length else 0) := by
    cases bi <;> simp [inBytes]
  have hA1 : At ((inBytesA sh bi ain v₁ v₂ av).map (·.toBitVec)) 0 (v₁.enc sh) := by
    cases bi
    · exact (At.app hAb).1
    all_goals exact hAb
  have hA2 : bi = .inp → At ((inBytesA sh bi ain v₁ v₂ av).map (·.toBitVec)) (0 + (v₁.enc sh).length) (v₂.enc sh) := by
    intro h; subst h; exact (At.app hAb).2
  have hA3 : ain = true → At ((inBytesA sh bi ain v₁ v₂ av).map (·.toBitVec)) (0 + (inBytes sh bi v₁ v₂).length)
      (leN 8 av.toNat) := by
    intro h; subst h; simpa using hAt
  have hIAl : (inBytesA sh bi ain v₁ v₂ av).length = (inBytes sh bi v₁ v₂).length + (if ain then 8 else 0) := by
    rw [hIA]; cases ain <;> simp [leN_length]
  have hbl : (v₁.enc sh).length + biLen sh bi v₂ ≤ (inBytes sh bi v₁ v₂).length + 1 := by
    cases bi <;> simp [inBytes, biLen]
  have hd2 : bi = .inp → v₂.depth ≤ (inBytes sh bi v₁ v₂).length := by
    intro h; have := nodes_le sh v₂ (h2 h); subst h; simp [inBytes]; omega
  have hn1 := nodes_le sh v₁ h1
  generalize hIb : inBytes sh bi v₁ v₂ = Ib at *
  generalize inBytesA sh bi ain v₁ v₂ av = I at *
  have hIB : (I.map (·.toBitVec)).length = I.length := by simp
  generalize hfr : 8 * (nl + 1) = fr at *
  have hfr16 : 136 ≤ fr := by omega
  generalize hK : fr * (I.length + (1 + hs.length) * (1 + W₀.length)) = K
  have hKI : fr * I.length ≤ K := by rw [← hK, Nat.mul_add]; omega
  have hKW : fr * (W₀.length + 1) * (hs.length + 1) ≤ K := by
    have e : (W₀.length + 1) * (hs.length + 1) = (1 + hs.length) * (1 + W₀.length) := by
      rw [Nat.mul_comm, Nat.add_comm 1 hs.length, Nat.add_comm 1 W₀.length]
    rw [← hK, Nat.mul_assoc, e]
    exact Nat.mul_le_mul_left fr (Nat.le_add_left _ _)
  have hKW1 : fr * (1 + W₀.length) ≤ K := by
    have := Nat.le_mul_of_pos_right (fr * (W₀.length + 1)) (show 0 < hs.length + 1 by omega)
    rw [Nat.add_comm 1]; omega
  have hK48 : 64 + 64 * I.length ≤ K := by
    have := Nat.mul_le_mul_right I.length hfr16
    have : 136 ≤ fr * (1 + W₀.length) := by
      have := Nat.mul_le_mul hfr16 (show 1 ≤ 1 + W₀.length by omega); omega
    omega
  have hK56 : 72 + 72 * W₀.length ≤ K := by
    have := Nat.mul_le_mul hfr16 (Nat.le_refl (1 + W₀.length)); rw [Nat.mul_add, Nat.mul_one] at this; omega
  -- the run of `main`
  let g := callEnv env []
  obtain ⟨W₁, xi, l1, hi1⟩ := init_exec g [I.map (·.toBitVec), O] W₀ (by omega) hW
  obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, b21, b22, e25, e24, gl2, rv1⟩ := dcall_ok hP1 (K := K) (K' := 64 * v₁.depth)
    (by omega) (dec_ok hP1 hsh v₁ h1) (d := 8) (by omega) (env := (g.set 4 0).set 5 4) (H := [I.map (·.toBitVec), O])
    rfl (by omega) hA1 hi1 (by rw [set_ne' _ _ (by omega), set_eq']; rfl) (by rw [set_eq']; rfl) (by rw [l1]; omega)
  obtain ⟨E₃, W₃, h₃, x₃, l3, a3, i3, b31, b32, e35, gl3, rv2, e34⟩ := bi_ok hP1 hsh bi v₂ (K := K)
    (fun h => by have := hd2 h; omega) hbi h2 (I := I.map (·.toBitVec)) (O := O) (by omega) i2 e25 e24 hA2
    (by rw [l2]; omega)
  have hc3 : (0 + (v₁.enc sh).length + if bi = .inp then (v₂.enc sh).length else 0) = 0 + Ib.length := by omega
  rw [hc3] at e34
  obtain ⟨E₄, x₄, e411, k₄⟩ := aC_exec ain a0 av E₃ (I.map (·.toBitVec)) O [W₃] (0 + Ib.length) e34
    (fun h => by rw [← haa] at *; exact hA3 h) (by omega)
  rw [haa] at e411
  have e48 : E₄ 8 = E₂ 8 := by rw [k₄ 8 (by omega) (by omega) (by omega), gl3 8 (by simp)]
  have e49 : E₄ 9 = E₃ 9 := k₄ 9 (by omega) (by omega) (by omega)
  have e45 : E₄ 5 = BitVec.ofNat 64 h₃ := by rw [k₄ 5 (by omega) (by omega) (by omega)]; exact e35
  obtain ⟨E₅, W₅, x₅, p₅, k₅, v₅⟩ := xok v₁ (bi.val v₂) (E₄ 8) aa (E₄ 9) 10 8 11 9 E₄ [I.map (·.toBitVec), O] W₃ h₃
    (by omega) (by rw [l3, l2, l1]; exact Nat.le_refl _) i3 e45 rfl e411 rfl (by rw [e48]; exact rv1.mono b31 a3) (by rw [e49]; exact rv2)
    (by show h₃ + 4 * pg.al v₁ aa (bi.val v₂) ≤ W₃.length; rw [l3, l2, l1]; omega)
  simp only [semX, Kd.pick_pair] at v₅
  simp only [alX] at p₅ v₅
  obtain ⟨E₆, x₆, e6, k₆⟩ := out_ok hP2 hshO nb hnb (K := K) (W := W₅) (by rw [p₅.len, l3, l2, l1]; omega) p₅.hi v₅
    (I := I.map (·.toBitVec)) hO hout
  have hb : CExec P K P[0].body ⟨callEnv env (([] : List BExp).map (·.denote env)), [I.map (·.toBitVec), O], [W₀]⟩
      ⟨E₆, [I.map (·.toBitVec), wr O 0 (Kd.out shO nb rk (pg.sem v₁ aa (bi.val v₂)))], [W₅]⟩ := by
    rw [hP0]
    exact .seq (.base xi) (.seq x₂ (.seq x₃ (.seq (.base x₄) (.seq (x₅.mono (by omega)) x₆))))
  refine ⟨_, CExec.call hf0 (by rw [hP0]; rfl) (by rw [hP0]; show 56 + K ≤ _; omega) hb, rfl, fun ht => ?_⟩
  simp only [set_eq']
  rw [hP0]; subst ht
  simp only [mainFn, vE]
  exact e6 rfl

/-- **The whole program** (one function, the first input format; the statement of section 17) -/
theorem ind_ok (sh : Shape) (pg : Pg rk) (bi : BIn) (a0 : BitVec 64) (nb : Nat)
    (hsh : sh.length < 255) (hn : pg.arms.length ≤ 255) (htg : ∀ e ∈ pg.arms, e.tags < 256)
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
  have hal := al_le pg hlin v₁ a0 (bi.val v₂)
  have hn1 := nodes_le sh v₁ h1
  have hI' : v₁.nodes ≤ (inBytes sh bi v₁ v₂).length := by cases bi <;> simp [inBytes] <;> omega
  have hMI : pg.M * v₁.nodes ≤ pg.M * (inBytes sh bi v₁ v₂).length := Nat.mul_le_mul_left _ hI'
  have hcap : 4 * (pg.M + 1) * (inBytes sh bi v₁ v₂).length =
      4 * (pg.M * (inBytes sh bi v₁ v₂).length) + 4 * (inBytes sh bi v₁ v₂).length := by
    rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
  have hIA : inBytesA sh bi false v₁ v₂ 0 = inBytes sh bi v₁ v₂ := by simp [inBytesA]
  have := ind_okM sh sh pg [] bi false a0 nb 16 hsh hsh (by omega) ⟨fun j hj => absurd hj (by simp), trivial⟩
    (by simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hn, fun e he => ⟨htg e he, by simpa using (hlin e he).2.2.2⟩⟩, trivial⟩)
    hbi hnb v₁ v₂ 0 h1 h2 O W₀ env res hres (by rw [hIA]; exact hI) hW
    (by rw [hIA]; simp only [Bool.false_eq_true, if_false]; omega) hO (by simpa using hout)
  simp only [hIA, Bool.false_eq_true, if_false, List.length_nil, Nat.add_zero] at this
  obtain ⟨σ', hx, hh, hr⟩ := this
  exact ⟨σ', hx.mono (by omega), hh, hr⟩

end Proven.Mach.Ind

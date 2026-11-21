/- The meaning of structured code (`SC`, `TC`) as big-step relations over the registers and memory of one frame,
with calls as `Returns` (the callee's run to a `ret`), and the correctness of the flattening into blocks
(`flatS_ok`, `flatT_ok`): a big-step run of the structured code is a run of the flattened blocks. -/
import Legacy.Compiler.Ir.Struct

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- many ordinary steps -/
inductive Star (P : Prog VReg) : State VReg → State VReg → Prop
  | refl (s : State VReg) : Star P s s
  | step {s s' s'' : State VReg} : step P s = .next s' → Star P s' s'' → Star P s s''

theorem Star.trans {P : Prog VReg} {s₁ s₂ s₃ : State VReg} (h₁ : Star P s₁ s₂) (h₂ : Star P s₂ s₃) : Star P s₁ s₃ := by
  induction h₁ with
  | refl => exact h₂
  | step e _ ih => exact .step e (ih h₂)

theorem Star.run {P : Prog VReg} {s s' : State VReg} {r : Result} (h : Star P s s') (hd : Ir.step P s' = .done r) :
    ∃ n, run P n s = some r := by
  induction h with
  | refl => exact ⟨1, by rw [run_succ, hd]⟩
  | step e _ ih => obtain ⟨n, hn⟩ := ih hd; exact ⟨n + 1, by rw [run_succ, e]; exact hn⟩

/-- a frame of function `f` goes from `(l, pc)` to `(l', pc')`, whatever is below it -/
def Reach (P : Prog VReg) (f : FId) (l pc : Nat) (g : VReg → Val) (m : Mem) (l' pc' : Nat) (g' : VReg → Val)
    (m' : Mem) : Prop :=
  ∀ (dst : List VReg) (rest : List (Frame VReg)) (ev : List MemEvent), ∃ ev',
    Star P ⟨⟨f, l, pc, g, dst⟩ :: rest, m, ev⟩ ⟨⟨f, l', pc', g', dst⟩ :: rest, m', ev'⟩

theorem Reach.refl {P : Prog VReg} {f : FId} {l pc : Nat} {g : VReg → Val} {m : Mem} : Reach P f l pc g m l pc g m :=
  fun _ _ ev => ⟨ev, .refl _⟩

theorem Reach.trans {P : Prog VReg} {f : FId} {l pc l' pc' l'' pc'' : Nat} {g g' g'' : VReg → Val} {m m' m'' : Mem}
    (h₁ : Reach P f l pc g m l' pc' g' m') (h₂ : Reach P f l' pc' g' m' l'' pc'' g'' m'') :
    Reach P f l pc g m l'' pc'' g'' m'' := fun dst rest ev =>
  let ⟨ev₁, s₁⟩ := h₁ dst rest ev
  let ⟨ev₂, s₂⟩ := h₂ dst rest ev₁
  ⟨ev₂, s₁.trans s₂⟩

/-- a call of `f` with the arguments `args` returns `vs` -/
def Returns (P : Prog VReg) (f : FId) (args : List Val) (m : Mem) (vs : List Val) (m' : Mem) : Prop :=
  ∃ G, P.funcs[f]? = some G ∧ args.length = G.params.length ∧ ∃ l pc g' B rvs,
    Reach P f G.entry 0 (setMany (fun _ => .w 0) G.params args) m l pc g' m' ∧ G.blocks.lookup l = some B ∧
    B.body[pc]? = none ∧ B.term = .ret rvs ∧ rvs.map (Arg.eval g') = vs

/-- **the meaning of straight-line code** in the frame of a function of `P` -/
inductive SC.Ex (P : Prog VReg) : SC → (VReg → Val) → Mem → (VReg → Val) → Mem → Prop
  | nop {g m} : SC.Ex P .nop g m g m
  | i {x g m g' m' e} : (∀ ds f as, x ≠ .call ds f as) → x.exec m g = some (g', m', e) → SC.Ex P (.i x) g m g' m'
  | call {ds f as g m vs m'} : Returns P f (as.map (Arg.eval g)) m vs m' → vs.length = ds.length →
      SC.Ex P (.i (.call ds f as)) g m (setMany g ds vs) m'
  | seq {a b g m g₁ m₁ g₂ m₂} : SC.Ex P a g m g₁ m₁ → SC.Ex P b g₁ m₁ g₂ m₂ → SC.Ex P (.seq a b) g m g₂ m₂
  | iteT {t a b g m g' m'} : t.eval g = some true → SC.Ex P a g m g' m' → SC.Ex P (.ite t a b) g m g' m'
  | iteF {t a b g m g' m'} : t.eval g = some false → SC.Ex P b g m g' m' → SC.Ex P (.ite t a b) g m g' m'
  | loopF {t b g m} : t.eval g = some false → SC.Ex P (.loop t b) g m g m
  | loopT {t b g m g₁ m₁ g₂ m₂} : t.eval g = some true → SC.Ex P b g m g₁ m₁ → SC.Ex P (.loop t b) g₁ m₁ g₂ m₂ →
      SC.Ex P (.loop t b) g m g₂ m₂

/-- how code with a terminator ends: a return, or a jump to a block (its parameters assigned) -/
inductive Out where
  | ret (vs : List Val) (m : Mem)
  | go (l : Lbl) (g : VReg → Val) (m : Mem)

/-- **the meaning of code with a terminator** in the frame of `F` -/
inductive TC.Ex (P : Prog VReg) (F : Func VReg) : TC → (VReg → Val) → Mem → Out → Prop
  | seq {a t g m g₁ m₁ o} : SC.Ex P a g m g₁ m₁ → TC.Ex P F t g₁ m₁ o → TC.Ex P F (.seq a t) g m o
  | iteT {t a b g m o} : t.eval g = some true → TC.Ex P F a g m o → TC.Ex P F (.ite t a b) g m o
  | iteF {t a b g m o} : t.eval g = some false → TC.Ex P F b g m o → TC.Ex P F (.ite t a b) g m o
  | ret {vs g m} : TC.Ex P F (.term (.ret vs)) g m (.ret (vs.map (Arg.eval g)) m)
  | jmp {l as g m B} : F.blocks.lookup l = some B → as.length = B.params.length →
      TC.Ex P F (.term (.jmp l as)) g m (.go l (setMany g B.params (as.map (Arg.eval g))) m)
  | sw {x ls d g m k B} : g x = .w k → F.blocks.lookup (ls[k.toNat]?.getD d) = some B → B.params = [] →
      TC.Ex P F (.term (.switch x ls d)) g m (.go (ls[k.toNat]?.getD d) g m)

/-! ## single steps -/

section
variable {P : Prog VReg} {f : FId} {F : Func VReg} (hF : P.funcs[f]? = some F)
include hF

theorem reach_inst {l pc : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {x : Inst VReg}
    (hk : B.body[pc]? = some x) (hx : ∀ ds g as, x ≠ .call ds g as) {g g' : VReg → Val} {m m' : Mem}
    {e : List MemEvent} (he : x.exec m g = some (g', m', e)) : Reach P f l pc g m l (pc + 1) g' m' := by
  intro dst rest ev
  refine ⟨e ++ ev, .step ?_ (.refl _)⟩
  unfold step; simp only [hF, hB, hk]
  cases x with
  | call ds g as => exact absurd rfl (hx ds g as)
  | _ => simp only [he]

theorem reach_call {l pc : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {ds : List VReg} {g : FId}
    {as : List (Arg VReg)} (hk : B.body[pc]? = some (.call ds g as)) {regs : VReg → Val} {m m' : Mem}
    {vs : List Val} (hr : Returns P g (as.map (Arg.eval regs)) m vs m') (hl : vs.length = ds.length) :
    Reach P f l pc regs m l (pc + 1) (setMany regs ds vs) m' := by
  intro dst rest ev
  obtain ⟨G, hG, hla, l', pc', g', B', rvs, hR, hB', hk', ht', hv⟩ := hr
  simp only [List.length_map] at hla
  obtain ⟨ev₁, h₁⟩ := hR ds (⟨f, l, pc + 1, regs, dst⟩ :: rest) (.alloc (G.slots + 1) :: ev)
  refine ⟨.free (G.slots + 1) :: ev₁, .step ?_ (h₁.trans (.step ?_ (.refl _)))⟩
  · unfold step; simp only [hF, hB, hk, hG, hla, if_true]
  · unfold step; simp only [hG, hB', hk', ht', termStep, hv]
    rw [if_pos (by rw [← hl, ← hv, List.length_map])]

theorem reach_jmp {l : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {pc : Nat}
    (hk : B.body[pc]? = none) {l' : Lbl} {B' : Block VReg} (ht : B.term = .jmp l' [])
    (hB' : F.blocks.lookup l' = some B') (hp : B'.params = []) {g : VReg → Val} {m : Mem} :
    Reach P f l pc g m l' 0 g m := by
  intro dst rest ev
  refine ⟨ev, .step ?_ (.refl _)⟩
  unfold step; simp only [hF, hB, hk, ht, termStep, jump, hB', hp, List.map_nil, List.length_nil, if_true, setMany]

theorem reach_br {l : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {pc : Nat}
    (hk : B.body[pc]? = none) {t : Tst VReg} {l₁ l₂ : Lbl} (ht : B.term = .br t l₁ [] l₂ [])
    {g : VReg → Val} {bv : Bool} (hbv : t.eval g = some bv) {B' : Block VReg}
    (hB' : F.blocks.lookup (if bv then l₁ else l₂) = some B') (hp : B'.params = []) {m : Mem} :
    Reach P f l pc g m (if bv then l₁ else l₂) 0 g m := by
  intro dst rest ev
  refine ⟨ev, .step ?_ (.refl _)⟩
  unfold step; simp only [hF, hB, hk, ht, termStep, hbv]
  cases bv <;> simp only [Bool.false_eq_true, if_false, if_true] at hB' ⊢ <;>
    simp only [jump, hB', hp, List.map_nil, List.length_nil, if_true, setMany]

end

/-! ## the flattening -/

/-- the blocks made so far are blocks of `F`, and the open block is a block of `F` that starts with the
instructions so far -/
def GS.Ok (F : Func VReg) (gs : GS) : Prop :=
  (∀ lb ∈ gs.bs, F.blocks.lookup lb.1 = some lb.2) ∧
  ∃ B, F.blocks.lookup gs.cl = some B ∧ B.params = gs.cp ∧ gs.ci <+: B.body

theorem GS.Ok.close {F : Func VReg} {gs : GS} {t : Term VReg} (h : ∀ lb ∈ (gs.close t).bs, F.blocks.lookup lb.1 = some lb.2) :
    F.blocks.lookup gs.cl = some ⟨gs.cp, gs.ci, t⟩ := h (gs.cl, ⟨gs.cp, gs.ci, t⟩) (by simp [GS.close])

theorem close_bs (gs : GS) (t : Term VReg) : gs.bs <+: (gs.close t).bs := ⟨_, rfl⟩
theorem close_open_bs (gs : GS) (t : Term VReg) (l : Lbl) : gs.bs <+: ((gs.close t).open l).bs := ⟨_, rfl⟩

theorem flatS_bs (sc : SC) : ∀ gs : GS, gs.bs <+: (flatS sc gs).bs := by
  induction sc with
  | nop => intro gs; exact List.prefix_refl _
  | i x => intro gs; exact List.prefix_refl _
  | seq a b iha ihb => intro gs; exact (iha gs).trans (ihb _)
  | ite t a b iha ihb =>
    intro gs; simp only [flatS]
    exact (close_open_bs { gs with nl := gs.nl + 3 } _ _).trans ((iha _).trans ((close_open_bs _ _ _).trans
      ((ihb _).trans (close_open_bs _ _ _))))
  | loop t b ih =>
    intro gs; simp only [flatS]
    exact (close_open_bs { gs with nl := gs.nl + 3 } _ _).trans ((close_open_bs _ _ _).trans ((ih _).trans
      (close_open_bs _ _ _)))


theorem ok_mono {F : Func VReg} {gs gs' : GS} (h : gs.bs <+: gs'.bs) (h' : ∀ lb ∈ gs'.bs, F.blocks.lookup lb.1 = some lb.2) :
    ∀ lb ∈ gs.bs, F.blocks.lookup lb.1 = some lb.2 := fun lb hl => h' lb (h.subset hl)

/-- the block closed before an `open` -/
theorem ok_close_open {F : Func VReg} {gs : GS} {t : Term VReg} {l : Lbl} (h : GS.Ok F ((gs.close t).open l)) :
    (∀ lb ∈ gs.bs, F.blocks.lookup lb.1 = some lb.2) ∧ F.blocks.lookup gs.cl = some ⟨gs.cp, gs.ci, t⟩ :=
  ⟨ok_mono (close_bs gs t) h.1, GS.Ok.close h.1⟩

theorem ok_of_close_open {F : Func VReg} {gs : GS} {t : Term VReg} {l : Lbl} (h : GS.Ok F ((gs.close t).open l)) :
    GS.Ok F gs :=
  let ⟨h1, h2⟩ := ok_close_open h
  ⟨h1, _, h2, rfl, List.prefix_refl _⟩

theorem ok_nl {F : Func VReg} {gs : GS} {n : Nat} (h : GS.Ok F { gs with nl := n }) : GS.Ok F gs := h

theorem flatS_start {F : Func VReg} : ∀ (sc : SC) (gs : GS), GS.Ok F (flatS sc gs) → GS.Ok F gs
  | .nop, _, h => h
  | .i x, gs, ⟨h1, B, hB, hp, hpre⟩ => ⟨h1, B, hB, hp, (List.prefix_append _ _).trans hpre⟩
  | .seq a b, gs, h => flatS_start a gs (flatS_start b _ h)
  | .ite t a b, gs, h => by
    simp only [flatS] at h
    exact ok_nl (ok_of_close_open (flatS_start a _ (ok_of_close_open (flatS_start b _ (ok_of_close_open h)))))
  | .loop t b, gs, h => by
    simp only [flatS] at h
    exact ok_nl (ok_of_close_open (ok_of_close_open (flatS_start b _ (ok_of_close_open h))))

theorem prefix_get {l l' : List (Inst VReg)} {x : Inst VReg} (h : l ++ [x] <+: l') : l'[l.length]? = some x := by
  obtain ⟨t, rfl⟩ := h; simp

theorem prefix_none {B : Block VReg} {ci : List (Inst VReg)} (h : B.body = ci) : B.body[ci.length]? = none := by
  rw [h]; simp

theorem ok_open_block {F : Func VReg} {gs : GS} (h : GS.Ok F gs) : ∃ B, F.blocks.lookup gs.cl = some B ∧ B.params = gs.cp :=
  let ⟨_, B, hB, hp, _⟩ := h; ⟨B, hB, hp⟩

section
variable {P : Prog VReg} {f : FId} {F : Func VReg} (hF : P.funcs[f]? = some F)
include hF

theorem loop_reach {t : Tst VReg} {b : SC} {H Bd X : Lbl}
    (hH : F.blocks.lookup H = some ⟨[], [], .br t Bd [] X []⟩)
    (hBd : ∃ B, F.blocks.lookup Bd = some B ∧ B.params = [])
    (hX : ∃ B, F.blocks.lookup X = some B ∧ B.params = [])
    (hb : ∀ {g m g' m'}, SC.Ex P b g m g' m' → Reach P f Bd 0 g m H 0 g' m') :
    ∀ {sc : SC} {g m g' m'}, SC.Ex P sc g m g' m' → sc = .loop t b → Reach P f H 0 g m X 0 g' m' := by
  intro sc g m g' m' hx
  induction hx with
  | loopF ht =>
    intro e; cases e
    obtain ⟨B, hB, hp⟩ := hX
    exact reach_br hF hH (by simp) rfl ht (bv := false) hB hp
  | loopT ht hbx _ _ ih =>
    intro e; cases e
    obtain ⟨B, hB, hp⟩ := hBd
    exact (reach_br hF hH (by simp) rfl ht (bv := true) hB hp).trans ((hb hbx).trans (ih rfl))
  | _ => intro e; cases e

/-- **the flattening of straight-line code is correct** -/
theorem flatS_ok : ∀ (sc : SC) {g m g' m'}, SC.Ex P sc g m g' m' → ∀ gs, GS.Ok F (flatS sc gs) →
    Reach P f gs.cl gs.ci.length g m (flatS sc gs).cl (flatS sc gs).ci.length g' m'
  | .nop, g, m, g', m', hx, gs, _ => by cases hx; exact Reach.refl
  | .i x, g, m, g', m', hx, gs, ⟨_, B, hB, _, hpre⟩ => by
    have hk := prefix_get hpre
    cases hx with
    | i hc he =>
      have := reach_inst hF hB hk hc he
      simpa [flatS] using this
    | call hr hl =>
      have := reach_call hF hB hk hr hl
      simpa [flatS] using this
  | .seq a b, g, m, g', m', hx, gs, h => by
    cases hx with
    | seq ha hb =>
      exact (flatS_ok a ha gs (flatS_start b _ h)).trans (flatS_ok b hb _ h)
  | .ite t a b, g, m, g', m', hx, gs, h => by
    simp only [flatS] at h ⊢
    have hJ := ok_open_block h
    obtain ⟨hJ1, hbJ⟩ := ok_close_open h
    have hb0 := flatS_start b _ (ok_of_close_open h)
    obtain ⟨hL2, haJ⟩ := ok_close_open hb0
    have ha0 := flatS_start a _ (ok_of_close_open hb0)
    obtain ⟨_, hbr⟩ := ok_close_open ha0
    obtain ⟨B1, hB1, hp1⟩ := ok_open_block ha0
    obtain ⟨B2, hB2, hp2⟩ := ok_open_block hb0
    obtain ⟨BJ, hBJ, hpJ⟩ := hJ
    cases hx with
    | iteT ht hax =>
      refine (reach_br hF hbr (by simp) rfl ht (bv := true) hB1 hp1).trans ((flatS_ok a hax _ (ok_of_close_open hb0)).trans ?_)
      exact reach_jmp hF haJ (by simp) rfl hBJ hpJ
    | iteF ht hbx =>
      refine (reach_br hF hbr (by simp) rfl ht (bv := false) hB2 hp2).trans ((flatS_ok b hbx _ (ok_of_close_open h)).trans ?_)
      exact reach_jmp hF hbJ (by simp) rfl hBJ hpJ
  | .loop t b, g, m, g', m', hx, gs, h => by
    simp only [flatS] at h ⊢
    obtain ⟨BX, hBX, hpX⟩ := ok_open_block h
    obtain ⟨-, hbH⟩ := ok_close_open h
    have hb0 := flatS_start b _ (ok_of_close_open h)
    obtain ⟨-, hH⟩ := ok_close_open hb0
    obtain ⟨-, hj⟩ := ok_close_open (ok_of_close_open hb0)
    obtain ⟨BB, hBB, hpB⟩ := ok_open_block hb0
    obtain ⟨BH, hBH, hpH⟩ := ok_open_block (ok_of_close_open hb0)
    refine (reach_jmp hF hj (by simp) rfl hBH hpH).trans (loop_reach hF hH ⟨BB, hBB, hpB⟩ ⟨BX, hBX, hpX⟩
      (fun hbx => (flatS_ok b hbx _ (ok_of_close_open h)).trans (reach_jmp hF hbH (by simp) rfl hBH hpH)) hx rfl)

end


def GS.OkT (F : Func VReg) (gs : GS) : Prop := ∀ lb ∈ gs.bs, F.blocks.lookup lb.1 = some lb.2

theorem flatT_start {F : Func VReg} : ∀ (tc : TC) (gs : GS), GS.OkT F (flatT tc gs) → GS.Ok F gs
  | .seq a t, gs, h => flatS_start a gs (flatT_start t _ h)
  | .ite t a b, gs, h => by
    simp only [flatT] at h
    have hb := flatT_start b _ h
    have ha := flatT_start a _ hb.1
    exact ok_nl (ok_of_close_open ha)
  | .term t, gs, h => ⟨ok_mono (close_bs gs t) h, _, GS.Ok.close h, rfl, List.prefix_refl _⟩

/-- where code with a terminator ends -/
def EndsAt (P : Prog VReg) (f : FId) (F : Func VReg) (l pc : Nat) (g : VReg → Val) (m : Mem) : Out → Prop
  | .ret vs m' => ∃ l' pc' g' B rvs, Reach P f l pc g m l' pc' g' m' ∧ F.blocks.lookup l' = some B ∧
      B.body[pc']? = none ∧ B.term = .ret rvs ∧ rvs.map (Arg.eval g') = vs
  | .go l' g' m' => Reach P f l pc g m l' 0 g' m'

theorem EndsAt.pre {P : Prog VReg} {f : FId} {F : Func VReg} {l pc l₁ pc₁ : Nat} {g g₁ : VReg → Val} {m m₁ : Mem}
    {o : Out} (h₁ : Reach P f l pc g m l₁ pc₁ g₁ m₁) (h : EndsAt P f F l₁ pc₁ g₁ m₁ o) : EndsAt P f F l pc g m o := by
  cases o with
  | ret vs m' => obtain ⟨l', pc', g', B, rvs, hR, h2⟩ := h; exact ⟨l', pc', g', B, rvs, h₁.trans hR, h2⟩
  | go l' g' m' => exact h₁.trans h

section
variable {P : Prog VReg} {f : FId} {F : Func VReg} (hF : P.funcs[f]? = some F)
include hF

theorem reach_jmpA {l : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {pc : Nat}
    (hk : B.body[pc]? = none) {l' : Lbl} {as : List (Arg VReg)} (ht : B.term = .jmp l' as) {B' : Block VReg}
    (hB' : F.blocks.lookup l' = some B') (hl : as.length = B'.params.length) {g : VReg → Val} {m : Mem} :
    Reach P f l pc g m l' 0 (setMany g B'.params (as.map (Arg.eval g))) m := by
  intro dst rest ev
  refine ⟨ev, .step ?_ (.refl _)⟩
  unfold step; simp only [hF, hB, hk, ht, termStep, jump, hB', List.length_map, hl, if_true]

theorem reach_sw {l : Nat} {B : Block VReg} (hB : F.blocks.lookup l = some B) {pc : Nat}
    (hk : B.body[pc]? = none) {x : VReg} {ls : List Lbl} {d : Lbl} (ht : B.term = .switch x ls d) {g : VReg → Val}
    {k : BitVec 64} (hx : g x = .w k) {B' : Block VReg} (hB' : F.blocks.lookup (ls[k.toNat]?.getD d) = some B')
    (hp : B'.params = []) {m : Mem} : Reach P f l pc g m (ls[k.toNat]?.getD d) 0 g m := by
  intro dst rest ev
  refine ⟨ev, .step ?_ (.refl _)⟩
  unfold step; simp only [hF, hB, hk, ht, termStep, hx, jump, hB', hp, List.length_nil, if_true, setMany]

/-- **the flattening of code with a terminator is correct** -/
theorem flatT_ok : ∀ (tc : TC) {g m o}, TC.Ex P F tc g m o → ∀ gs, GS.OkT F (flatT tc gs) →
    EndsAt P f F gs.cl gs.ci.length g m o
  | .seq a t, g, m, o, hx, gs, h => by
    cases hx with
    | seq ha ht => exact EndsAt.pre (flatS_ok hF a ha gs (flatT_start t _ h)) (flatT_ok t ht _ h)
  | .ite t a b, g, m, o, hx, gs, h => by
    simp only [flatT] at h
    have hb0 := flatT_start b _ h
    have ha0 := flatT_start a _ hb0.1
    obtain ⟨-, hbr⟩ := ok_close_open ha0
    obtain ⟨B1, hB1, hp1⟩ := ok_open_block ha0
    obtain ⟨B2, hB2, hp2⟩ := ok_open_block hb0
    cases hx with
    | iteT ht hax => exact EndsAt.pre (reach_br hF hbr (by simp) rfl ht (bv := true) hB1 hp1) (flatT_ok a hax _ hb0.1)
    | iteF ht hbx => exact EndsAt.pre (reach_br hF hbr (by simp) rfl ht (bv := false) hB2 hp2) (flatT_ok b hbx _ h)
  | .term t, g, m, o, hx, gs, h => by
    have hB : F.blocks.lookup gs.cl = some ⟨gs.cp, gs.ci, t⟩ := GS.Ok.close h
    cases hx with
    | ret => exact ⟨gs.cl, gs.ci.length, g, _, _, Reach.refl, hB, by simp, rfl, rfl⟩
    | jmp hB' hl => exact reach_jmpA hF hB (by simp) rfl hB' hl
    | sw hx' hB' hp => exact reach_sw hF hB (by simp) rfl hx' hB' hp

end

end Proven.Ir

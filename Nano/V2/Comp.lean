import Nano.V2.Inp
import Nano.V2.Tail
import Nano.V2.Loop
/- nano v2 increment 3 (products): **`cE_ok`**, the expression compiler `cE` (Nano/V2/Gen.lean) is correct on the
LOOP-FREE, BUFFER-FREE fragment `Ex.Pure` (words, `bin`, `ite`, `let`, pairs, `fst`/`snd`, consuming `split`, input
reads), on the abstract machine of Nano/V2/Sem.lean.  A value is its words side by side (`Val.flat`); the compile-time
environment entry `(τ, p)` holds the variable's `τ.size` words from absolute slot `p` (`EnvRep`). -/
namespace Nano.V2B

/- increments 3–4: no buffers (loops allowed) -/
mutual
def Ex.Pure : Ex → Bool
  | .lit _ => true
  | .var _ => true
  | .isize => true
  | .bin _ a b => a.Pure && b.Pure
  | .ite _ a b t e => a.Pure && b.Pure && t.Pure && e.Pure
  | .let_ v b => v.Pure && b.Pure
  | .pair a b => a.Pure && b.Pure
  | .fst e => e.Pure
  | .snd e => e.Pure
  | .split e b => e.Pure && b.Pure
  | .iget i => i.Pure
  | .loop f i z t => f.Pure && i.Pure && z.Pure && t.Pure
  | _ => false
def Tl.Pure : Tl → Bool
  | .ret e => e.Pure
  | .next e => e.Pure
  | .ite _ a b t e => a.Pure && b.Pure && t.Pure && e.Pure
  | .let_ v b => v.Pure && b.Pure
  | .split e b => e.Pure && b.Pure
end

/-- a value's run-time words -/
def Val.flat : Val → List UInt64
  | .wd x => [x]
  | .bf _ => []
  | .pr a b => a.flat ++ b.flat

/-- buffer-free typing of values -/
def Val.HasTy : Val → Ty → Prop
  | .wd _, .w => True
  | .pr a b, .prod τ σ => a.HasTy τ ∧ b.HasTy σ
  | _, _ => False

theorem Val.HasTy.len : ∀ {v : Val} {τ : Ty}, v.HasTy τ → v.flat.length = τ.size
  | .wd _, .w, _ => rfl
  | .pr _ _, .prod _ _, ⟨ha, hb⟩ => by simp [Val.flat, Ty.size, ha.len, hb.len]
  | .wd _, .buf, h => h.elim
  | .wd _, .prod _ _, h => h.elim
  | .bf _, _, h => h.elim
  | .pr _ _, .w, h => h.elim
  | .pr _ _, .buf, h => h.elim

theorem Val.HasTy.w : ∀ {v : Val}, v.HasTy .w → v = .wd v.word
  | .wd _, _ => rfl
  | .bf _, h => h.elim
  | .pr _ _, h => h.elim

theorem Val.HasTy.prod : ∀ {v : Val} {τ σ : Ty}, v.HasTy (.prod τ σ) → v = .pr v.fst v.snd ∧ v.fst.HasTy τ ∧ v.snd.HasTy σ
  | .pr _ _, _, _, h => ⟨rfl, h⟩
  | .wd _, _, _, h => h.elim
  | .bf _, _, _, h => h.elim

/-- the compile-time environment describes the stack `L` and the values `vs` -/
def EnvRep (L : List UInt64) : List (Ty × Nat) → List Val → Prop
  | [], [] => True
  | (τ, p) :: env, v :: vs => v.HasTy τ ∧ p + τ.size ≤ L.length ∧ (L.drop p).take τ.size = v.flat ∧ EnvRep L env vs
  | _, _ => False

theorem EnvRep.ext {L : List UInt64} (M : List UInt64) :
    ∀ {env : List (Ty × Nat)} {vs : List Val}, EnvRep L env vs → EnvRep (L ++ M) env vs
  | [], [], _ => trivial
  | (τ, p) :: _, _ :: _, ⟨h1, h2, h3, h4⟩ => by
    refine ⟨h1, by simp; omega, ?_, EnvRep.ext M h4⟩
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]; exact h3
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem EnvRep.get {L : List UInt64} :
    ∀ {env : List (Ty × Nat)} {vs : List Val} {i : Nat} {τ : Ty} {p : Nat}, EnvRep L env vs → env[i]? = some (τ, p) →
      (vs.getD i (.wd 0)).HasTy τ ∧ p + τ.size ≤ L.length ∧ (L.drop p).take τ.size = (vs.getD i (.wd 0)).flat
  | [], _, _, _, _, _, h => by simp at h
  | (_, _) :: _, _ :: _, 0, _, _, ⟨h1, h2, h3, _⟩, h => by
    simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨h1, h2, h3⟩
  | (_, _) :: _, _ :: _, i + 1, _, _, ⟨_, _, _, h4⟩, h => by
    simp only [List.getElem?_cons_succ] at h; simpa using EnvRep.get h4 h
  | _ :: _, [], _, _, _, h, _ => h.elim

/-- the new top entry of an extended stack -/
theorem EnvRep.top {L V : List UInt64} {env : List (Ty × Nat)} {vs : List Val} {v : Val} {τ : Ty}
    (he : EnvRep L env vs) (hv : v.HasTy τ) (hV : v.flat = V) : EnvRep (L ++ V) ((τ, L.length) :: env) (v :: vs) := by
  subst hV
  have hl := hv.len
  refine ⟨hv, by simp; omega, ?_, he.ext _⟩
  rw [List.drop_left, ← hl, List.take_length]

theorem ROp.ofOp_eval (o : Op) (x y : UInt64) : (ROp.ofOp o).eval x y = o.eval x y := by
  cases o <;> simp only [ROp.ofOp, ROp.eval, Op.eval]
  · apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_shiftLeft]
  · apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_shiftRight]

theorem flat_ite (b : Bool) (u v : Val) : (if b then u else v).flat = if b then u.flat else v.flat := by
  cases b <;> rfl

/-! ## blocks for tails and loops -/

theorem seq_any {c : Cfg} {a b : SC} {s : St} {h : Nat} {M V : List UInt64} {P : Res → Prop}
    (hP : ∀ s', P (.jmp .oom s'))
    (ha : ∃ r, SC.Ex c a s r ∧ Post c s h M V r)
    (hb : ∀ s1, Stk c s1 h (M ++ V) → Keep s s1 → ∃ r, SC.Ex c b s1 r ∧ P r) :
    ∃ r, SC.Ex c (.seq a b) s r ∧ P r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | ok s1 => obtain ⟨r2, e2, p2⟩ := hb s1 p.1 p.2; exact ⟨r2, .seq e e2, p2⟩
  | jmp t s1 => simp only [Post] at p; subst p; exact ⟨_, .seqJ e, hP s1⟩

theorem JPost.keep {c : Cfg} {s s1 : St} {h : Nat} {A vs : List UInt64} {t : Tg} {r : Res}
    (k : Keep s s1) (hp : s1.get 30 = s.get 30) (p : JPost c s1 h A vs t r) : JPost c s h A vs t r := by
  cases r with
  | ok _ => exact p.elim
  | jmp t' s' =>
    rcases p with ⟨h1, h2, h3⟩ | h1
    · exact .inl ⟨h1, h2, k.trans h3 hp⟩
    · exact .inr h1

/-- a block pushing `C` over the frame part `B`, then `slide` -/
theorem slide_post {c : Cfg} {a : SC} {s : St} {h : Nat} {A B C : List UInt64} (hc : c.Good)
    (hs : Stk c s h (A ++ B)) (hm : B.length ≤ 255) (hk : C.length ≤ 255)
    (ha : ∃ r, SC.Ex c a s r ∧ Post c s h (A ++ B) C r) :
    ∃ r, SC.Ex c (.seq a (.ins (slide C.length B.length))) s r ∧ Post c s h A C r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | jmp t' s2 => exact ⟨_, .seqJ e, p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    obtain ⟨s3, e3, hs3, k3⟩ := slide_ok hc A B C s2 (by simpa using hs2) hm hk
    exact ⟨_, .seq e (.ins e3), hs3, k2.trans k3 (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])⟩

/-- `ite_node` with any outcome predicate -/
theorem ite_gen {c : Cfg} {cab ct ce : SC} {s : St} {h : Nat} {L : List UInt64} {x y : UInt64} {P : Res → Prop}
    (hc : c.Good) (hs : Stk c s h L) (k : Cmp) (hP : ∀ s', P (.jmp .oom s'))
    (hab : ∃ r, SC.Ex c cab s r ∧ Post c s h L [x, y] r)
    (ht : k.eval x y = true → ∀ s1, Stk c s1 h L → Keep s s1 → s1.get 30 = s.get 30 → ∃ r, SC.Ex c ct s1 r ∧ P r)
    (he : k.eval x y = false → ∀ s1, Stk c s1 h L → Keep s s1 → s1.get 30 = s.get 30 → ∃ r, SC.Ex c ce s1 r ∧ P r) :
    ∃ r, SC.Ex c (.seq (.seq cab (.ins pop2)) (.ite (BOp.ofCmp k) T0 T1 ct ce)) s r ∧ P r := by
  obtain ⟨r, e, p⟩ := hab
  cases r with
  | jmp t s2 => simp only [Post] at p; subst p; exact ⟨_, .seqJ (.seqJ e), hP _⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    have hl : 1 < (L ++ [x, y]).length := by simp
    have e1 := ld_slot hc hs2 T1 0 (by omega)
    rw [(getD_two L x y).1] at e1
    have hs1 := hs2.set T1 y (by decide) (by decide)
    have e2 := ld_slot hc hs1 T0 1 hl
    rw [(getD_two L x y).2] at e2
    let s3 := (s2.set T1 y).set T0 x
    have hs3 : Stk c s3 h (L ++ [x, y]) := hs1.set T0 x (by decide) (by decide)
    have hs4 := hs3.popk (M := L) (X := [x, y]) hc
    let s4 := s3.set 31 (s3.get 31 + UInt64.ofInt ((8 * [x, y].length : Nat) : Int))
    have e4 : runL c pop2 s2 = some s4 := by
      rw [show pop2 = [.ld T1 SP (8 * ((0 : Nat) : Int))] ++ [.ld T0 SP (8 * ((1 : Nat) : Int))] ++
        [.i .addi SP SP ((8 * [x, y].length : Nat) : Int)] from rfl]
      rw [runL_append, runL_append, e1]; simp only [Option.bind_some]; rw [e2]; rfl
    have g0 : s4.get T0 = x := by
      simp only [s4, s3]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have g1 : s4.get T1 = y := by
      simp only [s4, s3]
      rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have k4 : Keep s s4 := by
      have : Keep s2 s4 := by
        refine ⟨?_, ?_, fun _ _ => by simp [s4, s3], by simp [s4, s3]⟩
        all_goals simp only [s4, s3]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      exact k2.trans this (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])
    have hp4 : s4.get 30 = s.get 30 := by apply UInt64.toNat.inj; rw [hs4.hp, hs.hp]
    have pre : SC.Ex c (.seq cab (.ins pop2)) s (.ok s4) := .seq e (.ins e4)
    cases hk : k.eval x y with
    | true =>
      obtain ⟨r, e5, p5⟩ := ht hk s4 hs4 k4 hp4
      exact ⟨r, .seq pre (.iteT (by rw [g0, g1, BOp.ofCmp_eval, hk]) e5), p5⟩
    | false =>
      obtain ⟨r, e5, p5⟩ := he hk s4 hs4 k4 hp4
      exact ⟨r, .seq pre (.iteF (by rw [g0, g1, BOp.ofCmp_eval, hk]) e5), p5⟩

/-- a tail's outcome type: `ret r : ρ`, `next s' : σ` -/
def TTy (σ ρ : Ty) : Val ⊕ Val → Prop
  | .inl r => r.HasTy ρ
  | .inr s' => s'.HasTy σ

/-- a tail's machine outcome: `ret r` = `r` slid over fuel + frame, jump to EXIT; `next s'` = `s'` slid over the
frame (fuel word `w` kept), jump to HEAD -/
def TJ (c : Cfg) (h : Nat) (L : List UInt64) (w : UInt64) (s : St) : Val ⊕ Val → Res → Prop
  | .inl r => JPost c s h L r.flat .exit
  | .inr s' => JPost c s h (L ++ [w]) s'.flat .head

theorem TJ.keep {c : Cfg} {h : Nat} {L : List UInt64} {w : UInt64} {s s1 : St} {o : Val ⊕ Val} {r : Res}
    (k : Keep s s1) (hp : s1.get 30 = s.get 30) (p : TJ c h L w s1 o r) : TJ c h L w s o r := by
  cases o <;> exact JPost.keep k hp p

theorem TJ.oom {c : Cfg} {h : Nat} {L : List UInt64} {w : UInt64} {s : St} (o : Val ⊕ Val) (s' : St) :
    TJ c h L w s o (.jmp .oom s') := by
  cases o <;> exact Or.inr rfl

theorem hp_eq {c : Cfg} {s s1 : St} {h : Nat} {A B : List UInt64} (hs : Stk c s h A) (hs1 : Stk c s1 h B) :
    s1.get 30 = s.get 30 := by apply UInt64.toNat.inj; rw [hs1.hp, hs.hp]

/-! ## the induction -/

/-- what `cE_ok` proves of one expression -/
def Good (c : Cfg) (h : Nat) (code : SC) (τ : Ty) (L : List UInt64) (v : Val) : Prop :=
  v.HasTy τ ∧ ∀ s, Stk c s h L → InpRep c s → ∃ r, SC.Ex c code s r ∧ Post c s h L v.flat r

theorem ofNat_eq_zero {n : Nat} (hn : n < 2 ^ 64) : UInt64.ofNat n = 0 ↔ n = 0 := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn] using this
  · rintro rfl; rfl

theorem ofNat_dec {m : Nat} (hn : m + 1 < 2 ^ 64) :
    UInt64.ofNat (m + 1) + UInt64.ofInt (-1) = UInt64.ofNat m := by
  apply UInt64.toNat.inj
  have : (UInt64.ofInt (-1)).toNat = 2 ^ 64 - 1 := by decide
  rw [UInt64.toNat_add, this]
  simp only [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega)]
  omega

theorem getD_mid (L F : List UInt64) (a : UInt64) :
    (L ++ [a] ++ F).getD ((L ++ [a] ++ F).length - 1 - F.length) 0 = a := by
  rw [show (L ++ [a] ++ F).length - 1 - F.length = L.length by simp <;> omega]
  simp [List.getD_eq_getElem?_getD]

theorem set_mid (L F : List UInt64) (a b : UInt64) :
    (L ++ [a] ++ F).set ((L ++ [a] ++ F).length - 1 - F.length) b = L ++ [b] ++ F := by
  rw [show (L ++ [a] ++ F).length - 1 - F.length = L.length by simp <;> omega]
  simp

mutual
theorem cE_ok {c : Cfg} {h : Nat} (hc : c.Good) :
    ∀ (e : Ex) (env : List (Ty × Nat)) (vals : List Val) (code : SC) (τ : Ty) (L : List UInt64),
      e.Pure = true → cE env L.length e = some (code, τ) → EnvRep L env vals →
      Good c h code τ L (den (inpW c) e vals)
  | .lit n, env, vals, code, τ, L, _, he, _ => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨by simp [den, Val.HasTy], fun s hs _ => by simpa [den, Val.flat] using lit_ok hc hs n⟩
  | .var i, env, vals, code, τ, L, _, he, hr => by
    unfold cE at he
    split at he
    · rename_i τ' p hi
      split at he
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2, h3⟩ := hr.get hi
        simp only [den]
        refine ⟨h1, fun s hs _ => ?_⟩
        have := varC_ok hc (L.length - 1 - p) (by unfold Lim at hb; omega) τ'.size L s hs (by omega) (by omega)
        rw [show seg L (L.length - 1 - p) τ'.size = (L.drop p).take τ'.size by
          unfold seg; congr 2; omega, h3] at this
        exact this
      · simp at he
    · simp at he
  | .isize, env, vals, code, τ, L, _, he, _ => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨by simp [den, Val.HasTy], fun s hs hin => by simpa [den, Val.flat] using isize_node hc hs hin⟩
  | .iget i, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ci hi
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Ex.Pure] at hp
      obtain ⟨t1, r1⟩ := cE_ok hc i env vals ci .w L hp hi hr
      refine ⟨by simp [den, Val.HasTy], fun s hs hin => ?_⟩
      have r := r1 s hs hin
      rw [t1.w] at r
      simpa [den, Val.flat] using iget_node hc hs hin r
    · simp at he
  | .bin o a b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca cb ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Ex.Pure, Bool.and_eq_true] at hp
      obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca .w L hp.1 ha hr
      let x := (den (inpW c) a vals).word
      have hb' : cE env (L ++ [x]).length b = some (cb, .w) := by simpa using hb
      obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb .w _ hp.2 hb' (hr.ext _)
      refine ⟨by simp [den, Val.HasTy], fun s hs hin => ?_⟩
      have ra' := ra s hs hin
      rw [ta.w] at ra'
      have := bin_node hc hs (ROp.ofOp o) ra' (fun s1 hs1 k1 => by
        have rb' := rb s1 hs1 (hin.keep k1); rw [tb.w] at rb'; exact rb')
      simpa [den, Val.flat, ROp.ofOp_eval] using this
    · simp at he
  | .ite k a b t e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca cb ct τ1 ce τ2 ha hb ht hte
      split at he
      · rename_i heq
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure, Bool.and_eq_true] at hp
        obtain ⟨⟨⟨pa, pb⟩, pt⟩, pe⟩ := hp
        obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca .w L pa ha hr
        let x := (den (inpW c) a vals).word
        have hb' : cE env (L ++ [x]).length b = some (cb, .w) := by simpa using hb
        obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb .w _ pb hb' (hr.ext _)
        obtain ⟨tt, rt⟩ := cE_ok hc t env vals ct τ1 L pt ht hr
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce τ1 L pe hte hr
        simp only [den]
        refine ⟨by split <;> assumption, fun s hs hin => ?_⟩
        have ra' := ra s hs hin
        rw [ta.w] at ra'
        have hab := seq_ok (B := [(den (inpW c) b vals).word]) ra' (fun s1 hs1 k1 => by
          have rb' := rb s1 hs1 (hin.keep k1); rw [tb.w] at rb'; exact rb') hs
        have := ite_node hc hs k hab (fun _ s1 hs1 k1 => rt s1 hs1 (hin.keep k1))
          (fun _ s1 hs1 k1 => re s1 hs1 (hin.keep k1))
        rw [flat_ite]; exact this
      · simp at he
    · simp at he
  | .let_ v b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i cv τv hv
      split at he
      · rename_i cb ρ hb
        split at he
        · rename_i hlim
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [Ex.Pure, Bool.and_eq_true] at hp
          obtain ⟨tv, rv⟩ := cE_ok hc v env vals cv τv L hp.1 hv hr
          let V := (den (inpW c) v vals).flat
          have hb' : cE ((τv, L.length) :: env) (L ++ V).length b = some (cb, ρ) := by
            simpa [V, tv.len] using hb
          obtain ⟨tb, rb⟩ := cE_ok hc b _ _ cb ρ (L ++ V) hp.2 hb' (hr.top tv rfl)
          simp only [den]
          refine ⟨tb, fun s hs hin => ?_⟩
          have := let_node hc hs (by rw [tv.len]; unfold Lim at hlim; omega)
            (by rw [tb.len]; unfold Lim at hlim; omega) (rv s hs hin)
            (fun s1 hs1 k1 => rb s1 hs1 (hin.keep k1))
          rw [tv.len, tb.len] at this
          exact this
        · simp at he
      · simp at he
    · simp at he
  | .pair a b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ca τa ha
      split at he
      · rename_i cb τb hb
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure, Bool.and_eq_true] at hp
        obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca τa L hp.1 ha hr
        let A := (den (inpW c) a vals).flat
        have hb' : cE env (L ++ A).length b = some (cb, τb) := by simpa [A, ta.len] using hb
        obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb τb _ hp.2 hb' (hr.ext _)
        simp only [den]
        exact ⟨⟨ta, tb⟩, fun s hs hin => seq_ok (ra s hs hin) (fun s1 hs1 k1 => rb s1 hs1 (hin.keep k1)) hs⟩
      · simp at he
    · simp at he
  | .fst e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure] at hp
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp he' hr
        obtain ⟨hv, t1, t2⟩ := te.prod
        simp only [den]
        refine ⟨t1, fun s hs hin => ?_⟩
        have r := re s hs hin
        rw [hv] at r
        have := drop_node hc hs r
        rw [t2.len] at this
        exact this
      · simp at he
    · simp at he
  | .snd e, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · rename_i hlim
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [Ex.Pure] at hp
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp he' hr
        obtain ⟨hv, t1, t2⟩ := te.prod
        simp only [den]
        refine ⟨t2, fun s hs hin => ?_⟩
        have r := re s hs hin
        rw [hv] at r
        have := slide_node hc hs (by rw [t1.len]; unfold Lim at hlim; omega)
          (by rw [t2.len]; unfold Lim at hlim; omega) r
        rw [t1.len, t2.len] at this
        exact this
      · simp at he
    · simp at he
  | .split e b, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i ce τa τb he'
      split at he
      · rename_i cb ρ hb
        split at he
        · rename_i hlim
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [Ex.Pure, Bool.and_eq_true] at hp
          obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ L hp.1 he' hr
          obtain ⟨hv, t1, t2⟩ := te.prod
          let v := den (inpW c) e vals
          let A := v.fst.flat
          let B := v.snd.flat
          have l1 : A.length = τa.size := t1.len
          have l2 : B.length = τb.size := t2.len
          have hr2 : EnvRep (L ++ A ++ B) ((τb, (L ++ A).length) :: (τa, L.length) :: env) (v.snd :: v.fst :: vals) :=
            (hr.top t1 rfl).top t2 rfl
          have hb' : cE ((τb, (L ++ A).length) :: (τa, L.length) :: env) (L ++ A ++ B).length b = some (cb, ρ) := by
            rw [show (L ++ A).length = L.length + τa.size by simp [l1],
              show (L ++ A ++ B).length = L.length + τa.size + τb.size by simp [l1, l2]; omega]
            exact hb
          obtain ⟨tb, rb⟩ := cE_ok hc b _ _ cb ρ _ hp.2 hb' hr2
          simp only [den]
          refine ⟨tb, fun s hs hin => ?_⟩
          have r := re s hs hin
          rw [hv] at r
          have := let_node hc hs (V := A ++ B) (by simp [l1, l2]; unfold Lim at hlim; omega)
            (by rw [tb.len]; unfold Lim at hlim; omega) r
            (fun s1 hs1 k1 => by
              have := rb s1 (by simpa [A, B, Val.flat] using hs1) (hin.keep k1)
              simpa [A, B, Val.flat] using this)
          rw [show (A ++ B).length = τa.size + τb.size by simp [l1, l2], tb.len] at this
          exact this
        · simp at he
      · simp at he
    · simp at he
  | .mk _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .size _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .get _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .set _ _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .push _ _, _, _, _, _, _, hp, _, _ => by simp [Ex.Pure] at hp
  | .loop f i z body, env, vals, code, τ, L, hp, he, hr => by
    unfold cE at he
    split at he
    · rename_i cf ci σ hf hi
      dsimp only at he
      split at he
      · rename_i cz ρ hz
        split at he
        · rename_i cb hb
          split at he
          · rename_i hlim
            simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp only [Ex.Pure, Bool.and_eq_true] at hp
            obtain ⟨⟨⟨pf, pi⟩, pz⟩, pb⟩ := hp
            unfold Lim at hlim
            obtain ⟨tf, rf⟩ := cE_ok hc f env vals cf .w L pf hf hr
            let F := (den (inpW c) f vals).word
            have hi' : cE env (L ++ [F]).length i = some (ci, σ) := by simpa using hi
            obtain ⟨ti, ri⟩ := cE_ok hc i env vals ci σ _ pi hi' (hr.ext _)
            have hrw : ∀ (w : UInt64) (st : Val), st.HasTy σ →
                EnvRep (L ++ [w] ++ st.flat ++ []) ((σ, L.length + 1) :: env) (st :: vals) := by
              intro w st hst
              have := (hr.ext [w]).top hst rfl
              simpa using this
            have Z : ∀ (w : UInt64) (st : Val), st.HasTy σ →
                Good c h cz ρ (L ++ [w] ++ st.flat) (den (inpW c) z (st :: vals)) := fun w st hst =>
              cE_ok hc z _ _ cz ρ (L ++ [w] ++ st.flat) pz
                (by rw [show (L ++ [w] ++ st.flat).length = L.length + 1 + σ.size by simp [hst.len] <;> omega]; exact hz)
                (by simpa using hrw w st hst)
            have B : ∀ (w : UInt64) (st : Val), st.HasTy σ → TTy σ ρ (denT (inpW c) body (st :: vals)) ∧
                ∀ s, Stk c s h (L ++ [w] ++ st.flat ++ []) → InpRep c s →
                  ∃ r, SC.Ex c cb s r ∧ TJ c h L w s (denT (inpW c) body (st :: vals)) r := fun w st hst =>
              cT_ok hc body _ _ cb σ ρ 0 L w st.flat [] pb hst.len rfl hb (hrw w st hst)
            have RT : ∀ n (st : Val), st.HasTy σ → (run (inpW c) z body vals n st).HasTy ρ := by
              intro n
              induction n with
              | zero => intro st hst; rw [run]; exact (Z 0 st hst).1
              | succ m ih =>
                intro st hst
                have tb := (B 0 st hst).1
                rw [run]
                split
                · rename_i r heq; rw [heq] at tb; exact tb
                · rename_i s' heq; rw [heq] at tb; exact ih s' tb
            simp only [den]
            refine ⟨RT _ _ ti, fun s0 hs0 hin0 => ?_⟩
            let st0 := den (inpW c) i vals
            let V := run (inpW c) z body vals F.toNat st0
            have rf' := rf s0 hs0 hin0
            rw [tf.w] at rf'
            have hfi := seq_ok (B := st0.flat) rf' (fun s1 hs1 k1 => ri s1 hs1 (hin0.keep k1)) hs0
            refine seq_any (fun _ => rfl) hfi (fun s1 hs1 k1 => ?_)
            let Inv : Nat → St → Prop := fun n s => n < 2 ^ 64 ∧ ∃ st : Val, st.HasTy σ ∧
              run (inpW c) z body vals n st = V ∧ Stk c s h (L ++ [UInt64.ofNat n] ++ st.flat) ∧ Keep s0 s ∧ InpRep c s
            let Aft : Nat → St → Prop := fun n s => n < 2 ^ 64 ∧ s.get 5 = UInt64.ofNat n ∧ ∃ st : Val, st.HasTy σ ∧
              run (inpW c) z body vals n st = V ∧ Stk c s h (L ++ [UInt64.ofNat n] ++ st.flat) ∧ Keep s0 s ∧ InpRep c s
            have hI : Inv F.toNat s1 :=
              ⟨F.toNat_lt, st0, ti, rfl, by simpa [UInt64.ofNat_toNat] using hs1, k1, hin0.keep k1⟩
            refine loop_ok Inv Aft (Post c s0 h L V.flat) ?_ ?_ ?_ F.toNat s1 hI
            · rintro n s ⟨hn, st, hst, hrun, hs, k, hin⟩
              have e := ld_slot hc hs T0 σ.size (by simp [hst.len] <;> omega)
              rw [show (L ++ [UInt64.ofNat n] ++ st.flat).getD
                ((L ++ [UInt64.ofNat n] ++ st.flat).length - 1 - σ.size) 0 = UInt64.ofNat n by
                  rw [← hst.len]; exact getD_mid _ _ _] at e
              have kk : Keep s (s.set T0 (UInt64.ofNat n)) := Keep.set s T0 _ (by decide) (by decide)
              have hs' := hs.set T0 (UInt64.ofNat n) (by decide) (by decide)
              refine ⟨_, e, ?_, hn, get_set_eq _ _ _ (by decide), st, hst, hrun, hs',
                k.trans kk (hp_eq hs0 hs), hin.keep kk⟩
              rw [show (s.set T0 (UInt64.ofNat n)).get 5 = UInt64.ofNat n from get_set_eq _ _ _ (by decide)]
              exact ofNat_eq_zero hn
            · rintro sa ⟨_, _, st, hst, hrun, hs, k, hin⟩
              rw [run] at hrun
              obtain ⟨tz, rz⟩ := Z (UInt64.ofNat 0) st hst
              have := slide_post (A := L) (B := [UInt64.ofNat 0] ++ st.flat) hc (by simpa using hs)
                (by simp [hst.len]; omega) (by rw [tz.len]; omega) (by simpa using rz sa hs hin)
              rw [tz.len, show ([UInt64.ofNat 0] ++ st.flat).length = σ.size + 1 by simp [hst.len] <;> omega,
                hrun] at this
              obtain ⟨r, e, p⟩ := this
              refine ⟨r, e, ?_⟩
              cases r with
              | ok s2 => exact ⟨p.1, k.trans p.2 (hp_eq hs0 hs)⟩
              | jmp t s2 => simp only [Post] at p; subst p; exact ⟨.inl rfl, rfl⟩
            · rintro m sa ⟨hn, g5, st, hst, hrun, hs, k, hin⟩
              let sb := sa.set T0 (sa.get T0 + UInt64.ofInt (-1))
              have gb : sb.get T0 = UInt64.ofNat m := by
                simp only [sb]; rw [get_set_eq _ _ _ (by decide)]; exact (show sa.get 5 = _ from g5) ▸ ofNat_dec hn
              have kb : Keep sa sb := Keep.set sa T0 _ (by decide) (by decide)
              have hsb := hs.set T0 (sa.get T0 + UInt64.ofInt (-1)) (by decide) (by decide)
              obtain ⟨sc, esc, hsc, ksc, _⟩ := sd_slot hc hsb T0 σ.size (by simp [hst.len] <;> omega)
              rw [gb, show (L ++ [UInt64.ofNat (m + 1)] ++ st.flat).set
                ((L ++ [UInt64.ofNat (m + 1)] ++ st.flat).length - 1 - σ.size) (UInt64.ofNat m) =
                  L ++ [UInt64.ofNat m] ++ st.flat by rw [← hst.len]; exact set_mid _ _ _ _] at hsc
              have kc : Keep s0 sc := (k.trans kb (hp_eq hs0 hs)).trans ksc (hp_eq hs0 hsb)
              refine ⟨sc, ?_, ?_⟩
              · show runL c ([.i .addi T0 T0 (-1)] ++ [.sd T0 SP (8 * σ.size)]) sa = some sc
                rw [runL_append]
                simp only [runL, I.run, IOp.eval, Option.bind_some]
                exact esc
              · obtain ⟨tb, rb⟩ := B (UInt64.ofNat m) st hst
                obtain ⟨r, e, p⟩ := rb sc (by simpa using hsc) (hin.keep (kb.trans ksc (hp_eq hs hsb)))
                refine ⟨r, e, ?_⟩
                rw [run] at hrun
                generalize denT (inpW c) body (st :: vals) = o at tb p hrun
                cases o with
                | inl R =>
                  try simp only at hrun
                  cases r with
                  | ok _ => exact p.elim
                  | jmp t s3 =>
                    rcases p with ⟨rfl, h2, h3⟩ | rfl
                    · exact ⟨hrun ▸ h2, kc.trans h3 (hp_eq hs0 hsc)⟩
                    · exact ⟨.inl rfl, rfl⟩
                | inr S' =>
                  try simp only at hrun
                  cases r with
                  | ok _ => exact p.elim
                  | jmp t s3 =>
                    rcases p with ⟨rfl, h2, h3⟩ | rfl
                    · have k3 : Keep s0 s3 := kc.trans h3 (hp_eq hs0 hsc)
                      exact ⟨by omega, S', tb, hrun, by simpa using h2, k3, hin0.keep k3⟩
                    · exact ⟨.inl rfl, rfl⟩
          · simp at he
        · simp at he
      · simp at he
    · simp at he

theorem cT_ok {c : Cfg} {h : Nat} (hc : c.Good) :
    ∀ (t : Tl) (env : List (Ty × Nat)) (vals : List Val) (code : SC) (σ ρ : Ty) (x : Nat) (L : List UInt64)
      (w : UInt64) (stF X : List UInt64),
      t.Pure = true → stF.length = σ.size → X.length = x →
      cT env (L.length + 1 + σ.size) σ ρ x t = some code → EnvRep (L ++ [w] ++ stF ++ X) env vals →
      TTy σ ρ (denT (inpW c) t vals) ∧ ∀ s, Stk c s h (L ++ [w] ++ stF ++ X) → InpRep c s →
        ∃ r, SC.Ex c code s r ∧ TJ c h L w s (denT (inpW c) t vals) r
  | .ret e, env, vals, code, σ, ρ, x, L, w, stF, X, hp, hF, hX, he, hr => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at he
    split at he
    · rename_i ce τ hce
      split at he
      · rename_i hcond
        obtain ⟨rfl, hl1, hl2⟩ := hcond
        simp only [Option.some.injEq] at he; subst he
        simp only [Tl.Pure] at hp
        unfold Lim at hl1 hl2
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce τ _ hp (by rw [hlen]; exact hce) hr
        simp only [denT, TTy, TJ]
        refine ⟨te, fun s hs hin => ?_⟩
        have := tail_node (A := L) (B := [w] ++ stF ++ X) hc (by simpa using hs) (by simp [hF, hX]; omega)
          (by rw [te.len]; omega) .exit (by simpa using re s hs hin)
        rw [te.len, show ([w] ++ stF ++ X).length = σ.size + 1 + x by simp [hF, hX]; omega] at this
        exact this
      · simp at he
    · simp at he
  | .next e, env, vals, code, σ, ρ, x, L, w, stF, X, hp, hF, hX, he, hr => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at he
    split at he
    · rename_i ce τ hce
      split at he
      · rename_i hcond
        obtain ⟨rfl, hl1⟩ := hcond
        simp only [Option.some.injEq] at he; subst he
        simp only [Tl.Pure] at hp
        unfold Lim at hl1
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce τ _ hp (by rw [hlen]; exact hce) hr
        simp only [denT, TTy, TJ]
        refine ⟨te, fun s hs hin => ?_⟩
        have := tail_node (A := L ++ [w]) (B := stF ++ X) hc (by simpa using hs) (by simp [hF, hX]; omega)
          (by rw [te.len]; omega) .head (by simpa using re s hs hin)
        rw [te.len, show (stF ++ X).length = τ.size + x by simp [hF, hX]] at this
        exact this
      · simp at he
    · simp at he
  | .ite k a b t e, env, vals, code, σ, ρ, x, L, w, stF, X, hp, hF, hX, he, hr => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at he
    split at he
    · rename_i ca cb ct ce ha hb ht hte
      simp only [Option.some.injEq] at he; subst he
      simp only [Tl.Pure, Bool.and_eq_true] at hp
      obtain ⟨⟨⟨pa, pb⟩, pt⟩, pe⟩ := hp
      obtain ⟨ta, ra⟩ := cE_ok hc a env vals ca .w _ pa (by rw [hlen]; exact ha) hr
      let xa := (den (inpW c) a vals).word
      obtain ⟨tb, rb⟩ := cE_ok hc b env vals cb .w (L ++ [w] ++ stF ++ X ++ [xa]) pb
        (by rw [show (L ++ [w] ++ stF ++ X ++ [xa]).length = L.length + 1 + σ.size + x + 1 by simp [hF, hX]; omega]
            exact hb) (hr.ext _)
      obtain ⟨tt, rt⟩ := cT_ok hc t env vals ct σ ρ x L w stF X pt hF hX ht hr
      obtain ⟨tE, rE⟩ := cT_ok hc e env vals ce σ ρ x L w stF X pe hF hX hte hr
      simp only [denT]
      refine ⟨by split <;> assumption, fun s hs hin => ?_⟩
      have ra' := ra s hs hin
      rw [ta.w] at ra'
      have hab := seq_ok (B := [(den (inpW c) b vals).word]) ra' (fun s1 hs1 k1 => by
        have rb' := rb s1 hs1 (hin.keep k1); rw [tb.w] at rb'; exact rb') hs
      refine ite_gen hc hs k (TJ.oom _) hab (fun hk s1 hs1 k1 hp1 => ?_) (fun hk s1 hs1 k1 hp1 => ?_)
      · obtain ⟨r, e1, p1⟩ := rt s1 hs1 (hin.keep k1)
        exact ⟨r, e1, by simp only [hk, if_true]; exact TJ.keep k1 hp1 p1⟩
      · obtain ⟨r, e1, p1⟩ := rE s1 hs1 (hin.keep k1)
        exact ⟨r, e1, by simp only [hk]; exact TJ.keep k1 hp1 p1⟩
    · simp at he
  | .let_ v b, env, vals, code, σ, ρ, x, L, w, stF, X, hp, hF, hX, he, hr => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at he
    split at he
    · rename_i cv τ hv
      split at he
      · rename_i cb hcb
        simp only [Option.some.injEq] at he; subst he
        simp only [Tl.Pure, Bool.and_eq_true] at hp
        obtain ⟨tv, rv⟩ := cE_ok hc v env vals cv τ _ hp.1 (by rw [hlen]; exact hv) hr
        let V := (den (inpW c) v vals).flat
        have hr2 : EnvRep (L ++ [w] ++ stF ++ (X ++ V))
            ((τ, L.length + 1 + σ.size + x) :: env) (den (inpW c) v vals :: vals) := by
          have := hr.top tv (rfl : _ = V)
          rw [hlen, List.append_assoc (L ++ [w] ++ stF) X V] at this
          exact this
        obtain ⟨tb, rb⟩ := cT_ok hc b _ _ cb σ ρ (x + τ.size) L w stF (X ++ V) hp.2 hF
          (by simp [V, hX, tv.len]) hcb hr2
        simp only [denT]
        refine ⟨tb, fun s hs hin => seq_any (TJ.oom _) (rv s hs hin) (fun s1 hs1 k1 => ?_)⟩
        obtain ⟨r, e1, p1⟩ := rb s1 (by rwa [List.append_assoc (L ++ [w] ++ stF) X V] at hs1) (hin.keep k1)
        exact ⟨r, e1, TJ.keep k1 (hp_eq hs hs1) p1⟩
      · simp at he
    · simp at he
  | .split e b, env, vals, code, σ, ρ, x, L, w, stF, X, hp, hF, hX, he, hr => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at he
    split at he
    · rename_i ce τa τb hce
      split at he
      · rename_i cb hcb
        simp only [Option.some.injEq] at he; subst he
        simp only [Tl.Pure, Bool.and_eq_true] at hp
        obtain ⟨te, re⟩ := cE_ok hc e env vals ce _ _ hp.1 (by rw [hlen]; exact hce) hr
        obtain ⟨hv, t1, t2⟩ := te.prod
        let v := den (inpW c) e vals
        let A := v.fst.flat
        let B := v.snd.flat
        have l1 : A.length = τa.size := t1.len
        have l2 : B.length = τb.size := t2.len
        have hr2 : EnvRep (L ++ [w] ++ stF ++ (X ++ (A ++ B)))
            ((τb, L.length + 1 + σ.size + x + τa.size) :: (τa, L.length + 1 + σ.size + x) :: env)
            (v.snd :: v.fst :: vals) := by
          have := (hr.top t1 rfl).top t2 rfl
          rw [show (L ++ [w] ++ stF ++ X ++ A).length = L.length + 1 + σ.size + x + τa.size by
            simp [hF, hX, l1]; omega, hlen] at this
          simpa only [List.append_assoc] using this
        obtain ⟨tb, rb⟩ := cT_ok hc b _ _ cb σ ρ (x + τa.size + τb.size) L w stF (X ++ (A ++ B)) hp.2 hF
          (by simp [hX, l1, l2]; omega) hcb hr2
        simp only [denT]
        refine ⟨tb, fun s hs hin => ?_⟩
        have r0 := re s hs hin
        rw [hv] at r0
        refine seq_any (TJ.oom _) r0 (fun s1 hs1 k1 => ?_)
        obtain ⟨r, e1, p1⟩ := rb s1 (by simpa only [Val.flat, List.append_assoc] using hs1) (hin.keep k1)
        exact ⟨r, e1, TJ.keep k1 (hp_eq hs hs1) p1⟩
      · simp at he
    · simp at he
end

end Nano.V2B

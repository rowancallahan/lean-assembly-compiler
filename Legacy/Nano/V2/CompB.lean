import Legacy.Nano.V2.CompBH
/- nano v2 increment 5 (buffers): **`cB_ok`**, the expression compiler `cE` (Nano/V2/Gen.lean) is correct for the
WHOLE language (words, products, input, `let`, `if`, buffers: `mk`/`size`/`get`/`set`/`push` in place, loops) on
the abstract machine (Nano/V2/Sem.lean), for every expression the ownership checker `Ex.lv` (Nano/V2/Own.lean)
accepts.  The environment invariant `EnvB` and the outcome `PB` are in Nano/V2/Heap.lean: buffers are `BufRep`s
with pairwise-disjoint footprints for live variables; a block changes memory below the old heap top only inside
the footprints of the buffers it consumed; the result's buffers live there or in the newly allocated heap. -/
namespace Nano.V2B

/-- a successful outcome from a pure tail that leaves one word -/
theorem OB.tailw {c : Cfg} {s s1 s2 : St} {h h1 : Nat} {L : List UInt64} {R : Rg} {z : UInt64} (hh : h ≤ h1)
    (h8 : h1 % 8 = 0) (k1 : KeepB s s1 h R) (hs2 : Stk c s2 h1 (L ++ [z])) (k2 : Keep s1 s2)
    (hp1 : (s1.get 30).toNat = h1) : OB c s h L R .w (.wd z) s2 :=
  ⟨h1, [z], fun _ => False, hh, h8, hs2, VR.ofw z, fun _ h => h.elim, k1.keep k2 (by rw [hp1]; exact hh)⟩

theorem RgC.below {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d' : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) : ∀ y, RgC env.length d d' Fs y → y < h :=
  fun _ hy => hy.low he

/-- the footprint of a value in `R ∪ [h, h1)`, `R` consumed from `d`, is disjoint from the non-dead entries of `d1` -/
theorem fresh_disj {c : Cfg} {s : St} {h h1 : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 : List Nat} {Fs : Nat → Rg} {F : Rg} (he : EnvB c s h L env vals d Fs) (st : Step (env.map (·.1)) d d1)
    (hF : ∀ y, F y → RgC env.length d d1 Fs y ∨ (h ≤ y ∧ y < h1)) :
    ∀ k, k < env.length → fl d1 k ≠ 2 → Disj F (Fs k) := by
  intro k hk hd y hy hy'
  have hd0 : fl d k ≠ 2 := by rcases st k with h' | ⟨h', _⟩ <;> omega
  rcases hF y hy with ⟨k', hk', a, b, f⟩ | ⟨h1', _⟩
  · have hne : k' ≠ k := by rintro rfl; omega
    exact he.disj k' k hne hk' hk a hd0 y f hy'
  · have := he.low k hk hd0 y hy'; omega

theorem fresh_low {c : Cfg} {s : St} {h h1 : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 : List Nat} {Fs : Nat → Rg} {F : Rg} (he : EnvB c s h L env vals d Fs) (hh : h ≤ h1)
    (hF : ∀ y, F y → RgC env.length d d1 Fs y ∨ (h ≤ y ∧ y < h1)) : ∀ y, F y → y < h1 := by
  intro y hy; rcases hF y hy with h' | h'
  · have := h'.low he; omega
  · exact h'.2

/-- a buffer value's footprint below the heap top -/
theorem VR.buf_foot {c : Cfg} {s : St} {v : Val} {W : List UInt64} {F : Rg} {h1 : Nat}
    (hv : VR c s .buf v W F) (hF : ∀ y, F y → y < h1) :
    ∃ a cap l, v = .bf l ∧ W = [UInt64.ofNat a] ∧ BufRep c s a cap l ∧ foot a cap ≤ h1 ∧ ∀ y, F y ↔ blk a cap y := by
  cases v with
  | bf l =>
    obtain ⟨a, cap, hW, hr, hF'⟩ := hv
    refine ⟨a, cap, l, rfl, hW, hr, ?_, hF'⟩
    have := hF (foot a cap - 1) ((hF' _).2 ⟨by unfold foot; omega, by unfold foot; omega⟩); omega
  | wd _ => exact hv.elim
  | pr _ _ => exact hv.elim

theorem cE_var {env : List (Ty × Nat)} {n : Nat} {i : Nat} {code : SC} {τ : Ty} (h : cE env n (.var i) = some (code, τ)) :
    ∃ p, env[i]? = some (τ, p) ∧ n < Lim + p + 1 ∧ p < n ∧ code = varC (n - 1 - p) τ.size := by
  unfold cE at h; split at h
  · rename_i τ' p hi; split at h
    · rename_i hb; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨p, hi, hb.1, hb.2, rfl⟩
    · simp at h
  · simp at h

/-- reading a variable (pure: memory untouched): its words are pushed -/
theorem var_post {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} {i p : Nat} {τ : Ty} (hc : c.Good) (hs : Stk c s h L)
    (he : EnvB c s h L env vals d Fs) (hi : env[i]? = some (τ, p)) (hb : L.length < Lim + p + 1) (hp : p < L.length) :
    ∃ r, SC.Ex c (varC (L.length - 1 - p) τ.size) s r ∧ Post c s h L ((L.drop p).take τ.size) r := by
  have := he.slot i τ p hi
  have hP := varC_ok hc (L.length - 1 - p) (by unfold Lim at hb; omega) τ.size L s hs (by omega) (by omega)
  rwa [show seg L (L.length - 1 - p) τ.size = (L.drop p).take τ.size by unfold seg; congr 2; omega] at hP

theorem fl_lt {d : List Nat} {k : Nat} (h : fl d k ≠ 0) : k < d.length := by
  unfold fl at h
  rcases Nat.lt_or_ge k d.length with h' | h'
  · exact h'
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at h

theorem getD_map_fst {env : List (Ty × Nat)} {i : Nat} {τ : Ty} {p : Nat} (hi : env[i]? = some (τ, p)) :
    (env.map (·.1)).getD i .w = τ := by simp [List.getD_eq_getElem?_getD, hi]

/-- a consumed variable: its flag goes 0 → 2 (buffers), or nothing happens (no buffer, empty footprint) -/
theorem use_fl {env : List (Ty × Nat)} {d d' : List Nat} {i p : Nat} {τ : Ty} (hi : env[i]? = some (τ, p))
    (hl : d.length = env.length) (hnb0 : τ.hasBuf = false → fl d i = 0) (hu : use (env.map (·.1)) d i = some d') :
    fl d i = 0 ∧ (τ.hasBuf = true → fl d' i = 2) ∧ (τ.hasBuf = false → d' = d) := by
  obtain ⟨_, _, hbuf, hnb⟩ := use_spec hu
  have hi' := lt_of_getElem? hi
  rw [getD_map_fst hi] at hbuf hnb
  cases hτ : τ.hasBuf
  · exact ⟨hnb0 hτ, fun h => absurd h (by decide), fun _ => hnb hτ⟩
  · rcases hbuf hτ with ⟨h0, h2⟩ | h0
    · exact ⟨h0, fun _ => h2, fun h => absurd h (by decide)⟩
    · omega

/-- an entry not consumed by a block keeps its memory -/
theorem rep_frame {c : Cfg} {s s' : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d' : List Nat} {Fs : Nat → Rg} (he : EnvB c s h L env vals d Fs) (st : Step (env.map (·.1)) d d')
    (k : KeepB s s' h (RgC env.length d d' Fs)) {i : Nat} (hi : i < env.length) (hd : fl d' i ≠ 2) :
    ∀ y, Fs i y → s'.w y = s.w y := by
  have hd0 : fl d i ≠ 2 := by rcases st i with h' | ⟨h', _⟩ <;> omega
  intro y hy
  refine k.heap y (he.low i hi hd0 y hy) ?_
  rintro ⟨k', hk', a, b, f⟩
  have hne : k' ≠ i := by rintro rfl; omega
  exact he.disj k' i hne hk' hi a hd0 y f hy

/-- a BORROWED buffer variable: its address pushed as a plain word (empty footprint) -/
theorem var_word {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d : List Nat} {Fs : Nat → Rg} {i : Nat} {code : SC} (R : Rg) (hc : c.Good) (hs : Stk c s h L)
    (he : EnvB c s h L env vals d Fs) (hce : cE env L.length (.var i) = some (code, .buf)) (hd : fl d i ≠ 2) :
    ∃ a cap l, i < env.length ∧ vals.getD i (.wd 0) = .bf l ∧ BufRep c s a cap l ∧ foot a cap ≤ h ∧
      (∀ y, Fs i y ↔ blk a cap y) ∧ ∃ r, SC.Ex c code s r ∧ PB c s h L R .w (.wd (UInt64.ofNat a)) r := by
  obtain ⟨p, hi, hb, hp, rfl⟩ := cE_var hce
  have hi' := lt_of_getElem? hi
  obtain ⟨a, cap, l, hv, hW, hr, hf, hF⟩ := (he.rep i .buf p hi hd).buf_foot (he.low i hi' hd)
  refine ⟨a, cap, l, hi', hv, hr, hf, hF, ?_⟩
  have hP := var_post hc hs he hi hb hp
  rw [show Ty.size .buf = 1 from rfl] at hP ⊢
  rw [show (L.drop p).take 1 = [UInt64.ofNat a] from hW] at hP
  exact liftP hs he.h8 hP (fun _ _ => VR.ofw _) (fun _ h => h.elim)

theorem ite_rg {tys : List Ty} {n : Nat} {d d2 x y : List Nat} {Fs : Nat → Rg} (st : Step tys d d2)
    (stx : Step tys d2 x) (sty : Step tys d2 y) (lx : x.length = d2.length) (ly : y.length = d2.length) :
    (∀ z, RgC n d d2 Fs z → RgC n d (orL x y) Fs z) ∧ (∀ z, RgC n d2 x Fs z → RgC n d (orL x y) Fs z) ∧
      (∀ z, RgC n d2 y Fs z → RgC n d (orL x y) Fs z) := by
  have ho := fl_orL (lx.trans ly.symm)
  refine ⟨fun z hz => hz.mono fun k _ a b => ⟨a, ?_⟩, fun z hz => hz.mono fun k _ a b => ⟨?_, ?_⟩,
    fun z hz => hz.mono fun k _ a b => ⟨?_, ?_⟩⟩
  · rw [ho]; rcases stx k with h1 | ⟨h1, _⟩ <;> rcases sty k with h2 | ⟨h2, _⟩ <;> omega
  · rcases st k with h1 | ⟨h1, _⟩ <;> omega
  · rw [ho]; rcases sty k with h2 | ⟨h2, _⟩ <;> omega
  · rcases st k with h1 | ⟨h1, _⟩ <;> omega
  · rw [ho]; rcases stx k with h2 | ⟨h2, _⟩ <;> omega

theorem assocE {c : Cfg} {a b d : SC} {s : St} {P : Res → Prop} (H : ∃ r, SC.Ex c (.seq a (.seq b d)) s r ∧ P r) :
    ∃ r, SC.Ex c (.seq (.seq a b) d) s r ∧ P r := let ⟨r, e, p⟩ := H; ⟨r, seq_assoc e, p⟩

/-! ## the induction -/

mutual
theorem cB_ok {c : Cfg} (hc : c.Good) :
    ∀ (e : Ex) (env : List (Ty × Nat)) (vals : List Val) (code : SC) (τ : Ty) (L : List UInt64)
      (d d' : List Nat) (Fs : Nat → Rg) (s : St) (h : Nat),
      cE env L.length e = some (code, τ) → e.lv (env.map (·.1)) d = some d' →
      Stk c s h L → EnvB c s h L env vals d Fs →
      ∃ r, SC.Ex c code s r ∧ PB c s h L (RgC env.length d d' Fs) τ (den (inpW c) e vals) r
  | .lit n, env, vals, code, τ, L, d, d', Fs, s, h, hce, _, hs, he => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
    simp only [den]
    exact liftP hs he.h8 (lit_ok hc hs n) (fun _ _ => VR.ofw n) (fun _ h => h.elim)
  | .isize, env, vals, code, τ, L, d, d', Fs, s, h, hce, _, hs, he => by
    simp only [cE, Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
    simp only [den]
    exact liftP hs he.h8 (isize_node hc hs he.inp) (fun _ _ => VR.ofw _) (fun _ h => h.elim)
  | .mk cap, env, vals, code, τ, L, d, d', Fs, s, h, hce, _, hs, he => by
    simp only [cE] at hce; split at hce
    · rename_i hcap; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      simp only [den]
      exact mk_node _ hc hs he.h8 hcap
    · simp at hce
  | .var i, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    obtain ⟨p, hi, hb, hp, rfl⟩ := cE_var hce
    simp only [den]
    have hi' := lt_of_getElem? hi
    obtain ⟨h0, h2, _⟩ := use_fl hi he.dl (he.nb i τ p hi) (lv_var.1 hlv)
    have hvr := he.rep i τ p hi (by omega)
    refine liftP hs he.h8 (var_post hc hs he hi hb hp)
      (fun s' k => hvr.frame fun y hy => k.heap y (by rw [hs.hp]; exact he.low i hi' (by omega) y hy)) ?_
    intro y hy
    cases hτ : τ.hasBuf
    · exact absurd hy (hvr.nobuf hτ y)
    · exact ⟨i, hi', h0, h2 hτ, hy⟩
  | .bin o a b, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ca cb ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      obtain ⟨d1, h1, h2⟩ := lv_bin hlv
      obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, _⟩ := lv_step _ _ _ _ h2
      have P := pairB he st1 st2 l1 (cB_ok hc a env vals ca .w L d d1 Fs s h ha h1 hs he)
        (fun s1 h1' W _ hs1 hW he1 => cB_ok hc b env vals cb .w (L ++ W) d1 d' Fs s1 h1'
          (by rw [List.length_append, hW]; exact hb) h2 hs1 he1)
      simp only [den]
      refine thenB (fun t _ ht => ht) P ?_
      rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, _, k1⟩
      obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd
      obtain ⟨s2, e, hs2, k2⟩ := binT_ok hc (by simpa using hs1) (ROp.ofOp o)
      rw [ROp.ofOp_eval] at hs2
      exact ⟨_, .ins e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
    · simp at hce
  | .pair a b, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ca τa ha; split at hce
      · rename_i cb τb hb; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
        obtain ⟨d1, h1, h2⟩ := lv_pair hlv
        obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, _⟩ := lv_step _ _ _ _ h2
        simp only [den]
        exact pairB he st1 st2 l1 (cB_ok hc a env vals ca τa L d d1 Fs s h ha h1 hs he)
          (fun s1 h1' W _ hs1 hW he1 => cB_ok hc b env vals cb τb (L ++ W) d1 d' Fs s1 h1'
            (by rw [List.length_append, hW]; exact hb) h2 hs1 he1)
      · simp at hce
    · simp at hce
  | .iget i, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ci hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      simp only [den]
      refine (fun ⟨r, e, p⟩ => ⟨r, seq_assoc e, p⟩) (thenB (fun t _ ht => ht)
        (cB_ok hc i env vals ci .w L d d' Fs s h hi (lv_iget hlv) hs he) ?_)
      rintro s1 ⟨h1', W, F, hh, h8', hs1, hv, _, k1⟩
      obtain ⟨-, rfl, _⟩ := hv.wd
      obtain ⟨s2, e, hs2, k2⟩ := igetT_ok hc hs1 (he.inp.keepB k1)
      exact ⟨_, e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
    · simp at hce
  | .ite k a b t e, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ca cb ct τ1 ce τ2 ha hb ht hte
      split at hce
      · rename_i heq; subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
        obtain ⟨d1, d2, x, y, h1, h2, h3, h4, rfl⟩ := lv_ite hlv
        obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
        obtain ⟨st3, l3⟩ := lv_step _ _ _ _ h3; obtain ⟨st4, l4⟩ := lv_step _ _ _ _ h4
        have P := pairB he st1 st2 l1 (cB_ok hc a env vals ca .w L d d1 Fs s h ha h1 hs he)
          (fun s1 h1' W _ hs1 hW he1 => cB_ok hc b env vals cb .w (L ++ W) d1 d2 Fs s1 h1'
            (by rw [List.length_append, hW]; exact hb) h2 hs1 he1)
        have st12 := st1.trans st2
        obtain ⟨R1, Rx, Ry⟩ := ite_rg (n := env.length) (Fs := Fs) st12 st3 st4 l3 l4
        simp only [den]
        refine (fun ⟨r, e, p⟩ => ⟨r, seq_assoc e, p⟩) (thenB (fun t _ ht => ht) P ?_)
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, _, k1⟩
        obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd
        obtain ⟨s2, e2, g0, g1, hs2, k2⟩ := pop2_ok hc (by simpa using hs1)
        have k12 : KeepB s s2 h (RgC env.length d d2 Fs) := k1.keep k2 (by rw [hs1.hp]; exact hh)
        have he2 : EnvB c s2 h1' L env vals d2 Fs := by
          simpa using he.after (M := []) st12 (l2.trans l1) k12 hh h8'
        cases hk : k.eval (den (inpW c) a vals).word (den (inpW c) b vals).word
        · obtain ⟨r, er, pr⟩ := cB_ok hc e env vals ce τ1 L d2 y Fs s2 h1' hte h4 hs2 he2
          refine ⟨r, .seq (.ins e2) (.iteF (by rw [g0, g1, BOp.ofCmp_eval, hk]) er), ?_⟩
          simp only [Bool.false_eq_true, if_false]
          exact PB.after k12 hh (fun z _ hz => R1 z hz) (fun z hz => .inl (Ry z hz)) pr
        · obtain ⟨r, er, pr⟩ := cB_ok hc t env vals ct τ1 L d2 x Fs s2 h1' ht h3 hs2 he2
          refine ⟨r, .seq (.ins e2) (.iteT (by rw [g0, g1, BOp.ofCmp_eval, hk]) er), ?_⟩
          simp only [if_true]
          exact PB.after k12 hh (fun z _ hz => R1 z hz) (fun z hz => .inl (Rx z hz)) pr
      · simp at hce
    · simp at hce
  | .fst e, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ce τ1 σ1 he'; split at hce
      · simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
        simp only [den]
        refine thenB (fun t _ ht => ht) (cB_ok hc e env vals ce _ L d d' Fs s h he' (lv_fst hlv) hs he) ?_
        rintro s1 ⟨h1, W, F, hh, h8', hs1, hv, hF, k1⟩
        generalize den (inpW c) e vals = V at hv ⊢
        cases V with
        | pr u w =>
          obtain ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hFF⟩ := hv
          have hs2 := (show Stk c s1 h1 ((L ++ W1) ++ W2) by simpa using hs1).popk (M := L ++ W1) (X := W2) hc
          have hcode : (8 * (σ1.size : Int)) = ((8 * W2.length : Nat) : Int) := by rw [hv2.len]; push_cast; rfl
          refine ⟨_, .ins (by simp only [runL, I.run, IOp.eval, Option.bind_some]; rw [hcode]; rfl), h1, W1, F1, hh,
            h8', hs2, hv1.frame (fun y _ => by simp), fun y hy => hF y ((hFF y).2 (.inl hy)),
            k1.keep (Keep.set _ _ _ (by decide) (by decide)) (by rw [hs1.hp]; exact hh)⟩
        | wd _ => exact hv.elim
        | bf _ => exact hv.elim
      · simp at hce
    · simp at hce
  | .snd e, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ce τ1 σ1 he'; split at hce
      · rename_i hlim; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
        simp only [den]
        refine thenB (fun t _ ht => ht) (cB_ok hc e env vals ce _ L d d' Fs s h he' (lv_snd hlv) hs he) ?_
        rintro s1 ⟨h1, W, F, hh, h8', hs1, hv, hF, k1⟩
        generalize den (inpW c) e vals = V at hv ⊢
        cases V with
        | pr u w =>
          obtain ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hFF⟩ := hv
          obtain ⟨s2, e2, hs2, k2⟩ := slide_ok hc L W1 W2 s1 (by simpa using hs1) (by rw [hv1.len]; unfold Lim at hlim; omega)
            (by rw [hv2.len]; unfold Lim at hlim; omega)
          rw [hv1.len, hv2.len] at e2
          have hlow := fresh_low he hh hF
          refine ⟨_, .ins e2, h1, W2, F2, hh, h8', hs2,
            hv2.frame (fun y hy => k2.heap y (by rw [hs1.hp]; exact hlow y ((hFF y).2 (.inr hy)))),
            fun y hy => hF y ((hFF y).2 (.inr hy)), k1.keep k2 (by rw [hs1.hp]; exact hh)⟩
        | wd _ => exact hv.elim
        | bf _ => exact hv.elim
      · simp at hce
    · simp at hce
  | .let_ v b, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cv τv hv; split at hce
      · rename_i cb ρ hb; split at hce
        · rename_i hlim; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
          simp only [den]
          unfold Lim at hlim
          apply assocE
          rcases lv_let hlv with ⟨j, τj, d'', rfl, hj, hbuf, hdj, h1, rfl⟩ | ⟨τ', d1, d'', hty, h1, h2, rfl⟩
          · -- read-only alias of `j`
            obtain ⟨p, hjp, hb1, hp1, rfl⟩ := cE_var hv
            have hτ : τj = τv := by simp [List.getElem?_map, hjp] at hj; exact hj.symm
            subst hτ
            simp only [den]
            obtain ⟨r1, e1, p1⟩ := var_post hc hs he hjp hb1 hp1
            cases r1 with
            | jmp t s1 => exact ⟨_, .seqJ e1, .inl p1⟩
            | ok s1 =>
              obtain ⟨hs1, k1⟩ := p1
              have hsl := he.slot j _ p hjp
              have hW : ((L.drop p).take τj.size).length = τj.size := by simp; omega
              have k1' := k1.toB hs.hp (RgC env.length d (d''.tail.set j (fl d j)) Fs)
              have he1 := he.after (M := (L.drop p).take τj.size) (Step.refl _ d) rfl
                (k1.toB hs.hp _) (Nat.le_refl _) he.h8
              have he2 := he1.alias hjp hbuf (by rw [getD_append_take hsl]) hdj
              obtain ⟨r, e, pr⟩ := cB_ok hc b _ _ cb ρ (L ++ (L.drop p).take τj.size) _ d'' _ s1 h
                (by rw [List.length_append, hW]; exact hb) (by simpa using h1) hs1 he2
              have := PB.slide hc (RgC.below he2) (by omega) (by rw [hW]; omega) ⟨r, e, pr⟩
              rw [hW] at this
              obtain ⟨r', e', p'⟩ := this
              exact ⟨r', .seq e1 e', PB.after k1' (Nat.le_refl _) (fun _ _ h => h)
                (fun z hz => .inl (RgC.alias (by rw [he.dl]; exact lt_of_getElem? hjp) hz)) p'⟩
          · -- an ordinary `let`
            have hτ' : τ' = τv := by rw [cE_tyOf v env _ cv τv hv] at hty; exact (Option.some.inj hty).symm
            subst hτ'
            obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
            obtain ⟨st3, _⟩ := step_tail st2 (by simpa using l2)
            refine thenB (fun t _ ht => ht) (cB_ok hc v env vals cv τ' L d d1 Fs s h hv h1 hs he) ?_
            rintro s1 ⟨h1', W, F, hh, h8', hs1, hv1, hF, k1⟩
            have hW := hv1.len
            have he1 := he.after (M := W) st1 l1 k1 hh h8'
            have he2 := he1.push hv1 (fresh_low he hh hF) (fresh_disj he st1 hF)
            obtain ⟨r, e, pr⟩ := cB_ok hc b _ _ cb ρ (L ++ W) _ d'' _ s1 h1'
              (by rw [List.length_append, hW]; exact hb) (by simpa using h2) hs1 he2
            have := PB.slide hc (RgC.below he2) (by omega) (by rw [hW]; omega) ⟨r, e, pr⟩
            rw [hW] at this
            obtain ⟨r', e', p'⟩ := this
            refine ⟨r', e', PB.after k1 hh ?_ ?_ p'⟩
            · intro z _ hz; exact hz.mono (fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩)
            · intro z hz
              rcases RgC.cons hz with hF' | hR
              · rcases hF z hF' with h' | h'
                · exact .inl (h'.mono (fun k _ a b => ⟨a, by rcases st3 k with h'' | ⟨h'', _⟩ <;> omega⟩))
                · exact .inr h'
              · exact .inl (RgC.trans st1 st3 (.inr hR))
        · simp at hce
      · simp at hce
    · simp at hce
  | .split e b, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i ce τ1 σ1 he'; split at hce
      · rename_i cb ρ hb; split at hce
        · rename_i hlim; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
          unfold Lim at hlim
          obtain ⟨τ', σ', d1, d'', hty, h1, h2, rfl⟩ := lv_split hlv
          have hτ : Ty.prod τ' σ' = .prod τ1 σ1 := by rw [cE_tyOf e env _ ce _ he'] at hty; exact (Option.some.inj hty).symm
          simp only [Ty.prod.injEq] at hτ; obtain ⟨rfl, rfl⟩ := hτ
          obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
          obtain ⟨st3, _⟩ := step_drop2 st2 (by simpa using l2)
          simp only [den]
          apply assocE
          refine thenB (fun t _ ht => ht) (cB_ok hc e env vals ce _ L d d1 Fs s h he' h1 hs he) ?_
          rintro s1 ⟨h1', W, F, hh, h8', hs1, hv, hF, k1⟩
          generalize hV : den (inpW c) e vals = V at hv ⊢
          cases V with
          | pr u w =>
            obtain ⟨W1, W2, F1, F2, rfl, hv1, hv2, hd12, hFF⟩ := hv
            have hW1 := hv1.len; have hW2 := hv2.len
            have hlow := fresh_low he hh hF
            have hdis := fresh_disj he st1 hF
            have heA := he.after (M := W1) st1 l1 k1 hh h8'
            have heB := heA.push hv1 (fun y hy => hlow y ((hFF y).2 (.inl hy)))
              (fun k hk hd y hy => hdis k hk hd y ((hFF y).2 (.inl hy)))
            have heC := (heB.ext W2).push (L := L ++ W1) hv2 (fun y hy => hlow y ((hFF y).2 (.inr hy))) (by
              intro k hk hd y hy hy'
              cases k with
              | zero => exact hd12 y hy' hy
              | succ k =>
                simp only [fl_cons_succ] at hd
                exact hdis k (by simpa using hk) hd y ((hFF y).2 (.inr hy)) hy')
            rw [show (L ++ W1).length = L.length + τ'.size by simp [hW1]] at heC
            obtain ⟨r, er, pr⟩ := cB_ok hc b _ _ cb ρ (L ++ W1 ++ W2) _ d'' _ s1 h1'
              (by simp only [List.length_append, hW1, hW2]; exact hb) (by simpa using h2)
              (by simpa using hs1) heC
            have := PB.slide (W := W1 ++ W2) hc (RgC.below heC) hlim.2 (by simp [hW1, hW2]; omega)
              ⟨r, er, by simpa using pr⟩
            rw [show (W1 ++ W2).length = τ'.size + σ'.size by simp [hW1, hW2]] at this
            obtain ⟨r', e', p'⟩ := this
            refine ⟨r', e', PB.after k1 hh ?_ ?_ p'⟩
            · intro z _ hz; exact hz.mono (fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩)
            · intro z hz
              have hFz : F z → RgC env.length d (d''.drop 2) Fs z ∨ (h ≤ z ∧ z < h1') := fun hF' => by
                rcases hF z hF' with h' | h'
                · exact .inl (h'.mono (fun k _ a b => ⟨a, by rcases st3 k with h'' | ⟨h'', _⟩ <;> omega⟩))
                · exact .inr h'
              rcases RgC.cons2 hz with h' | h' | h'
              · exact hFz ((hFF z).2 (.inr h'))
              · exact hFz ((hFF z).2 (.inl h'))
              · exact .inl (RgC.trans st1 st3 (.inr h'))
          | wd _ => exact hv.elim
          | bf _ => exact hv.elim
        · simp at hce
      · simp at hce
    · simp at hce
  | .size b, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cb hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      rcases lv_size hlv with ⟨i, rfl, hd, hdd⟩ | h1
      · rw [hdd]
        obtain ⟨a, cap, l, hi', hvl, hr, hf, hFi, P⟩ := var_word (RgC env.length d d Fs) hc hs he hb hd
        simp only [den, hvl, Val.list]
        refine thenB (fun t _ ht => ht) P ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, hv, _, k1⟩
        obtain ⟨-, rfl, _⟩ := hv.wd
        have hr1 := hr.frame fun y hy => rep_frame he (Step.refl _ d) k1 hi' hd y ((hFi y).2 hy)
        obtain ⟨s2, e, hs2, k2⟩ := sizeT_ok hc hs1 hr1 (by omega)
        exact ⟨_, .ins e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
      · simp only [den]
        refine thenB (fun t _ ht => ht) (cB_ok hc b env vals cb .buf L d d' Fs s h hb h1 hs he) ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, hv, hF, k1⟩
        obtain ⟨a, cap, l, hvl, rfl, hr, hf, _⟩ := hv.buf_foot (fresh_low he hh hF)
        rw [hvl]
        obtain ⟨s2, e, hs2, k2⟩ := sizeT_ok hc hs1 hr hf
        exact ⟨_, .ins e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
    · simp at hce
  | .get b j, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cb cj hb hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      apply assocE
      rcases lv_get hlv with ⟨i, rfl, hd, h1, hd'⟩ | ⟨d1, h1, h2⟩
      · obtain ⟨a, cap, l, hi', hvl, hr, hf, hFi, P⟩ := var_word (RgC env.length d d Fs) hc hs he hb hd
        obtain ⟨st1, _⟩ := lv_step _ _ _ _ h1
        have P2 := pairB he (Step.refl _ d) st1 rfl P (fun s1 h1' W _ hs1 hW he1 =>
          cB_ok hc j env vals cj .w (L ++ W) d d' Fs s1 h1' (by rw [List.length_append, hW]; exact hj) h1 hs1 he1)
        simp only [den, hvl, Val.list]
        refine thenB (fun t _ ht => ht) P2 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, _, k1⟩
        obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd
        have hr1 := hr.frame fun y hy => rep_frame he st1 k1 hi' hd' y ((hFi y).2 hy)
        obtain ⟨s2, e, hs2, k2⟩ := getT_ok hc (by simpa using hs1) hr1 (by omega)
        exact ⟨_, e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
      · obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, _⟩ := lv_step _ _ _ _ h2
        have P2 := pairB he st1 st2 l1 (cB_ok hc b env vals cb .buf L d d1 Fs s h hb h1 hs he)
          (fun s1 h1' W _ hs1 hW he1 => cB_ok hc j env vals cj .w (L ++ W) d1 d' Fs s1 h1'
            (by rw [List.length_append, hW]; exact hj) h2 hs1 he1)
        simp only [den]
        refine thenB (fun t _ ht => ht) P2 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hFF⟩, hF, k1⟩
        obtain ⟨a, cap, l, hvl, rfl, hr, hf, _⟩ :=
          hv1.buf_foot (fun y hy => fresh_low he hh hF y ((hFF y).2 (.inl hy)))
        obtain ⟨-, rfl, _⟩ := hv2.wd
        rw [hvl]
        obtain ⟨s2, e, hs2, k2⟩ := getT_ok hc (by simpa using hs1) hr hf
        exact ⟨_, e, OB.tailw hh h8' k1 hs2 k2 hs1.hp⟩
    · simp at hce
  | .set b j x, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cb cj cx hb hj hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      apply assocE
      rcases lv_set hlv with ⟨i, d1, d2, rfl, hd0, h1, h2, hu⟩ | ⟨d1, d2, h1, h2, h3⟩
      · obtain ⟨p, hi, _, _, _⟩ := cE_var hb
        obtain ⟨a, cap, l, hi', hvl, hr, hf, hFi, P⟩ :=
          var_word (RgC env.length d d Fs) hc hs he hb (by omega)
        obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
        obtain ⟨st3, _⟩ := use_spec hu
        obtain ⟨h0', h2', _⟩ := use_fl hi (l2.trans (l1.trans he.dl)) (fun h' => absurd h' (by decide)) hu
        have P2 := pairB he (Step.refl _ d) st1 rfl P (fun s1 h1' W _ hs1 hW he1 =>
          cB_ok hc j env vals cj .w (L ++ W) d d1 Fs s1 h1' (by rw [List.length_append, hW]; exact hj) h1 hs1 he1)
        have P3 := pairB he st1 st2 l1 P2 (fun s1 h1' W _ hs1 hW he1 =>
          cB_ok hc x env vals cx .w (L ++ W) d1 d2 Fs s1 h1' (by rw [List.length_append, hW]; exact hx) h2 hs1 he1)
        simp only [den, hvl, Val.list]
        refine thenB (fun t _ ht => ht) P3 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨Wa, W3, Fa, F3, rfl, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, hv3, _, _⟩,
          _, k1⟩
        obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd; obtain ⟨-, rfl, _⟩ := hv3.wd
        have hr1 := hr.frame fun y hy => rep_frame he (st1.trans st2) k1 hi' (by omega) y ((hFi y).2 hy)
        obtain ⟨s2, s3, e1, e2, hs3, hr3, k3⟩ := setT_ok hc (by simpa using hs1) hr1 (by omega)
        refine ⟨_, .seq (.ins e1) e2, h1', [UInt64.ofNat a], blk a cap, hh, h8', hs3,
          ⟨a, cap, rfl, hr3, fun _ => Iff.rfl⟩, fun y hy => .inl ⟨i, hi', hd0, h2' rfl, (hFi y).2 hy⟩, ?_⟩
        refine k1.trans k3 hh fun y _ hy => ?_
        rcases hy with hy | hy
        · exact hy.mono fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩
        · exact ⟨i, hi', hd0, h2' rfl, (hFi y).2 hy⟩
      · obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
        obtain ⟨st3, _⟩ := lv_step _ _ _ _ h3
        have P2 := pairB he st1 st2 l1 (cB_ok hc b env vals cb .buf L d d1 Fs s h hb h1 hs he)
          (fun s1 h1' W _ hs1 hW he1 => cB_ok hc j env vals cj .w (L ++ W) d1 d2 Fs s1 h1'
            (by rw [List.length_append, hW]; exact hj) h2 hs1 he1)
        have P3 := pairB he (st1.trans st2) st3 (l2.trans l1) P2 (fun s1 h1' W _ hs1 hW he1 =>
          cB_ok hc x env vals cx .w (L ++ W) d2 d' Fs s1 h1' (by rw [List.length_append, hW]; exact hx) h3 hs1 he1)
        simp only [den]
        refine thenB (fun t _ ht => ht) P3 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨Wa, W3, Fa, F3, rfl, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hF12⟩, hv3, _,
          hFa⟩, hF, k1⟩
        have hF1 : ∀ y, F1 y → RgC env.length d d' Fs y ∨ (h ≤ y ∧ y < h1') := fun y hy =>
          hF y ((hFa y).2 (.inl ((hF12 y).2 (.inl hy))))
        obtain ⟨a, cap, l, hvl, rfl, hr, hf, hFb⟩ := hv1.buf_foot (fresh_low he hh hF1)
        obtain ⟨-, rfl, _⟩ := hv2.wd; obtain ⟨-, rfl, _⟩ := hv3.wd
        rw [hvl]
        obtain ⟨s2, s3, e1, e2, hs3, hr3, k3⟩ := setT_ok hc (by simpa using hs1) hr hf
        refine ⟨_, .seq (.ins e1) e2, h1', [UInt64.ofNat a], blk a cap, hh, h8', hs3,
          ⟨a, cap, rfl, hr3, fun _ => Iff.rfl⟩, fun y hy => hF1 y ((hFb y).2 hy), ?_⟩
        refine k1.trans k3 hh fun y hy hy' => ?_
        rcases hy' with hy' | hy'
        · exact hy'
        · rcases hF1 y ((hFb y).2 hy') with h' | h'
          · exact h'
          · omega
    · simp at hce
  | .push b x, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cb cx hb hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
      apply assocE
      rcases lv_push hlv with ⟨i, d1, rfl, hd0, h1, hu⟩ | ⟨d1, h1, h2⟩
      · obtain ⟨p, hi, _, _, _⟩ := cE_var hb
        obtain ⟨a, cap, l, hi', hvl, hr, hf, hFi, P⟩ :=
          var_word (RgC env.length d d Fs) hc hs he hb (by omega)
        obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1
        obtain ⟨st3, _⟩ := use_spec hu
        obtain ⟨h0', h2', _⟩ := use_fl hi (l1.trans he.dl) (fun h' => absurd h' (by decide)) hu
        have P2 := pairB he (Step.refl _ d) st1 rfl P (fun s1 h1' W _ hs1 hW he1 =>
          cB_ok hc x env vals cx .w (L ++ W) d d1 Fs s1 h1' (by rw [List.length_append, hW]; exact hx) h1 hs1 he1)
        simp only [den, hvl, Val.list]
        refine thenB (fun t _ ht => ht) P2 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, _, k1⟩
        obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd
        have hr1 := hr.frame fun y hy => rep_frame he st1 k1 hi' (by omega) y ((hFi y).2 hy)
        obtain ⟨s2, e1, ⟨s3, e2, hs3, hr3, k3⟩ | ⟨s3, e2⟩⟩ := pushT_ok hc (by simpa using hs1) hr1 (by omega)
        · refine ⟨_, .seq (.ins e1) e2, h1', [UInt64.ofNat a], blk a cap, hh, h8', hs3,
            ⟨a, cap, rfl, hr3, fun _ => Iff.rfl⟩, fun y hy => .inl ⟨i, hi', hd0, h2' rfl, (hFi y).2 hy⟩, ?_⟩
          refine k1.trans k3 hh fun y _ hy => ?_
          rcases hy with hy | hy
          · exact hy.mono fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩
          · exact ⟨i, hi', hd0, h2' rfl, (hFi y).2 hy⟩
        · exact ⟨_, .seq (.ins e1) e2, .inr rfl⟩
      · obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, _⟩ := lv_step _ _ _ _ h2
        have P2 := pairB he st1 st2 l1 (cB_ok hc b env vals cb .buf L d d1 Fs s h hb h1 hs he)
          (fun s1 h1' W _ hs1 hW he1 => cB_ok hc x env vals cx .w (L ++ W) d1 d' Fs s1 h1'
            (by rw [List.length_append, hW]; exact hx) h2 hs1 he1)
        simp only [den]
        refine thenB (fun t _ ht => ht) P2 ?_
        rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hFF⟩, hF, k1⟩
        have hF1 : ∀ y, F1 y → RgC env.length d d' Fs y ∨ (h ≤ y ∧ y < h1') := fun y hy => hF y ((hFF y).2 (.inl hy))
        obtain ⟨a, cap, l, hvl, rfl, hr, hf, hFb⟩ := hv1.buf_foot (fresh_low he hh hF1)
        obtain ⟨-, rfl, _⟩ := hv2.wd
        rw [hvl]
        obtain ⟨s2, e1, ⟨s3, e2, hs3, hr3, k3⟩ | ⟨s3, e2⟩⟩ := pushT_ok hc (by simpa using hs1) hr hf
        · refine ⟨_, .seq (.ins e1) e2, h1', [UInt64.ofNat a], blk a cap, hh, h8', hs3,
            ⟨a, cap, rfl, hr3, fun _ => Iff.rfl⟩, fun y hy => hF1 y ((hFb y).2 hy), ?_⟩
          refine k1.trans k3 hh fun y hy hy' => ?_
          rcases hy' with hy' | hy'
          · exact hy'
          · rcases hF1 y ((hFb y).2 hy') with h' | h'
            · exact h'
            · omega
        · exact ⟨_, .seq (.ins e1) e2, .inr rfl⟩
    · simp at hce
  | .loop f i z body, env, vals, code, τ, L, d, d', Fs, s, h, hce, hlv, hs, he => by
    unfold cE at hce; split at hce
    · rename_i cf ci σ hf hi; simp only at hce; split at hce
      · rename_i cz ρ hz; split at hce
        · rename_i cb hb; split at hce
          · rename_i hlim; simp only [Option.some.injEq, Prod.mk.injEq] at hce; obtain ⟨rfl, rfl⟩ := hce
            unfold Lim at hlim
            obtain ⟨σ', d1, dz, dt, hty, h1, h2, h3, h4⟩ := lv_loop hlv
            have hσ : σ' = σ := by rw [cE_tyOf i env _ ci σ hi] at hty; exact (Option.some.inj hty).symm
            subst hσ
            obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
            have st12 := st1.trans st2
            have l12 : d'.length = d.length := l2.trans l1
            have P := pairB he st1 st2 l1 (cB_ok hc f env vals cf .w L d d1 Fs s h hf h1 hs he)
              (fun s1 h1' W _ hs1 hW he1 => cB_ok hc i env vals ci σ' (L ++ W) d1 d' Fs s1 h1'
                (by rw [List.length_append, hW]; exact hi) h2 hs1 he1)
            simp only [den]
            generalize hV : run (inpW c) z body vals (den (inpW c) f vals).word.toNat (den (inpW c) i vals) = V
            refine thenB (fun t _ ht => ht) P ?_
            rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, hFF⟩, hF, k1⟩
            obtain ⟨-, rfl, _⟩ := hv1.wd
            let R := RgC env.length d d' Fs
            let Inv : Nat → St → Prop := fun n s' => n < 2 ^ 64 ∧ ∃ (st : Val) (hc' : Nat) (Wst : List UInt64) (Fst : Rg),
              h ≤ hc' ∧ hc' % 8 = 0 ∧ Stk c s' hc' (L ++ [UInt64.ofNat n] ++ Wst) ∧ VR c s' σ' st Wst Fst ∧
              (∀ y, Fst y → R y ∨ (h ≤ y ∧ y < hc')) ∧ KeepB s s' h R ∧ run (inpW c) z body vals n st = V
            let Aft : Nat → St → Prop := fun n s' => s'.get 5 = UInt64.ofNat n ∧ Inv n s'
            -- the body's environment at a loop state
            have envL : ∀ (s' : St) (hc' : Nat) (w : UInt64) (Wst : List UInt64) (st : Val) (Fst : Rg),
                h ≤ hc' → hc' % 8 = 0 → KeepB s s' h R → VR c s' σ' st Wst Fst →
                (∀ y, Fst y → R y ∨ (h ≤ y ∧ y < hc')) →
                EnvB c s' hc' (L ++ [w] ++ Wst) ((σ', L.length + 1) :: env) (st :: vals)
                  (0 :: killAll (env.map (·.1)) d') (consF Fst Fs) := by
              intro s' hc' w Wst st Fst hh' h8x k' hv' hF'
              have heA := (he.after (M := [w]) st12 l12 k' hh' h8x).kill_all
              rw [show L.length + 1 = (L ++ [w]).length by simp]
              refine (heA.ext Wst).push hv' (fresh_low he hh' hF') ?_
              intro k hk hd
              have hd' : fl d' k ≠ 2 := by
                have hl : d'.length = (env.map (·.1)).length := by simp [l12, he.dl]
                rw [fl_killAll hl] at hd; split at hd <;> omega
              exact fresh_disj he st12 hF' k hk hd'
            have hRb : ∀ (Fst : Rg) (dd : List Nat) (y : Nat), RgC (env.length + 1)
                (0 :: killAll (env.map (·.1)) d') dd (consF Fst Fs) y → Fst y :=
              fun Fst dd y hy => RgC.body (he.after (M := []) st12 l12 k1 hh h8') hy
            refine loop_ok Inv Aft (PB c s h L R ρ V) ?_ ?_ ?_ _ s1 ⟨(den (inpW c) f vals).word.toNat_lt,
              den (inpW c) i vals, h1', W2, F2, hh, h8', by simpa [UInt64.ofNat_toNat] using hs1, hv2,
              fun y hy => hF y ((hFF y).2 (.inr hy)), k1, hV⟩
            · -- the test: t0 := the fuel
              rintro n s' ⟨hn, st, hc', Wst, Fst, hh', h8x, hs', hv', hF', k', hrun⟩
              have e := ld_slot hc hs' T0 σ'.size (by simp [hv'.len]; omega)
              rw [show (L ++ [UInt64.ofNat n] ++ Wst).getD ((L ++ [UInt64.ofNat n] ++ Wst).length - 1 - σ'.size) 0
                = UInt64.ofNat n by rw [← hv'.len]; exact getD_mid _ _ _] at e
              refine ⟨_, e, ?_, get_set_eq _ _ _ (by decide), hn, st, hc', Wst, Fst, hh', h8x,
                hs'.set T0 _ (by decide) (by decide), hv'.frame (fun _ _ => by simp), hF',
                k'.keep (Keep.set _ _ _ (by decide) (by decide)) (by rw [hs'.hp]; exact hh'), hrun⟩
              rw [show (s'.set T0 (UInt64.ofNat n)).get 5 = UInt64.ofNat n from get_set_eq _ _ _ (by decide)]
              exact ofNat_eq_zero hn
            · -- fuel 0: `z`, slid over fuel and state
              rintro sa ⟨_, hn, st, hc', Wst, Fst, hh', h8x, hs', hv', hF', k', hrun⟩
              rw [run] at hrun
              have he2 := envL sa hc' (UInt64.ofNat 0) Wst st Fst hh' h8x k' hv' hF'
              have hlz : (L ++ [UInt64.ofNat 0] ++ Wst).length = L.length + 1 + σ'.size := by simp [hv'.len]; omega
              obtain ⟨r, er, pr⟩ := cB_ok hc z _ _ cz ρ (L ++ [UInt64.ofNat 0] ++ Wst) _ dz _ sa hc'
                (by rw [hlz]; exact hz) (by simpa using h3) hs' he2
              have P' := PB.slide (L := L) (W := [UInt64.ofNat 0] ++ Wst) hc (RgC.below he2) hlim.2
                (by simp only [List.length_append, List.length_cons, List.length_nil, hv'.len]; omega)
                ⟨r, er, by simpa using pr⟩
              rw [show ([UInt64.ofNat 0] ++ Wst).length = σ'.size + 1 by simp only [List.length_append, List.length_cons, List.length_nil, hv'.len]; omega] at P'
              obtain ⟨r', e', p'⟩ := P'
              have q := PB.after k' hh' (fun _ _ h => h) (fun y hy => hF' y (hRb Fst dz y hy)) p'
              rw [hrun] at q
              refine ⟨r', e', ?_⟩
              cases r' with
              | ok _ => exact q
              | jmp t s3 =>
                rcases q with rfl | rfl
                · exact ⟨.inl rfl, .inl rfl⟩
                · exact ⟨.inr rfl, .inr rfl⟩
            · -- one body run
              rintro m sa ⟨g5, hn, st, hc', Wst, Fst, hh', h8x, hs', hv', hF', k', hrun⟩
              have hW := hv'.len
              let sb := sa.set T0 (sa.get T0 + UInt64.ofInt (-1))
              have gb : sb.get T0 = UInt64.ofNat m := by
                simp only [sb]; rw [get_set_eq _ _ _ (by decide)]; exact (show sa.get 5 = _ from g5) ▸ ofNat_dec hn
              have kb : Keep sa sb := Keep.set sa T0 _ (by decide) (by decide)
              have hsb := hs'.set T0 (sa.get T0 + UInt64.ofInt (-1)) (by decide) (by decide)
              obtain ⟨sc, esc, hsc, ksc, _⟩ := sd_slot hc hsb T0 σ'.size (by simp [hW]; omega)
              rw [gb, show (L ++ [UInt64.ofNat (m + 1)] ++ Wst).set
                ((L ++ [UInt64.ofNat (m + 1)] ++ Wst).length - 1 - σ'.size) (UInt64.ofNat m) =
                  L ++ [UInt64.ofNat m] ++ Wst by rw [← hW]; exact set_mid _ _ _ _] at hsc
              have kc : Keep sa sc := kb.trans ksc (hp_eq hs' hsb)
              have kc' : KeepB s sc h R := k'.keep kc (by rw [hs'.hp]; exact hh')
              have hvc : VR c sc σ' st Wst Fst := hv'.frame fun y hy => kc.heap y (by
                rw [hs'.hp]; exact fresh_low he hh' hF' y hy)
              have he2 := envL sc hc' (UInt64.ofNat m) Wst st Fst hh' h8x kc' hvc hF'
              refine ⟨sc, ?_, ?_⟩
              · show runL c ([.i .addi T0 T0 (-1)] ++ [.sd T0 SP (8 * σ'.size)]) sa = some sc
                rw [runL_append]
                simp only [runL, I.run, IOp.eval, Option.bind_some]
                exact esc
              · obtain ⟨r, er, pr⟩ := cTB_ok hc body _ _ cb σ' ρ 0 L (UInt64.ofNat m) Wst [] _ dt _ sc hc'
                  hW rfl (by simpa using hb) (by simpa using h4) (by simpa using hsc) (by simpa using he2)
                refine ⟨r, er, ?_⟩
                rw [run] at hrun
                have q := TB.after kc' hh' (fun _ _ h => h) (fun y hy => hF' y (hRb Fst dt y hy)) pr
                generalize denT (inpW c) body (st :: vals) = o at q hrun
                cases r with
                | ok _ => exact q.elim
                | jmp t s3 =>
                  rcases q with rfl | rfl | q
                  · exact ⟨.inl rfl, .inl rfl⟩
                  · exact ⟨.inr rfl, .inr rfl⟩
                  · cases o with
                    | inl R' =>
                      obtain ⟨rfl, q⟩ := q
                      simp only at hrun; rw [← hrun]; exact q
                    | inr S' =>
                      obtain ⟨rfl, ⟨hc2, Ws, Fs2, hh2, h82, hs3, hv3, hF3, k3⟩⟩ := q
                      simp only at hrun
                      exact ⟨by omega, S', hc2, Ws, Fs2, hh2, h82, hs3, hv3, hF3, k3, hrun⟩
          · simp at hce
        · simp at hce
      · simp at hce
    · simp at hce

theorem cTB_ok {c : Cfg} (hc : c.Good) :
    ∀ (t : Tl) (env : List (Ty × Nat)) (vals : List Val) (code : SC) (σ ρ : Ty) (x : Nat) (L : List UInt64)
      (w : UInt64) (stF X : List UInt64) (d d' : List Nat) (Fs : Nat → Rg) (s : St) (h : Nat),
      stF.length = σ.size → X.length = x →
      cT env (L.length + 1 + σ.size) σ ρ x t = some code → t.lvT (env.map (·.1)) d = some d' →
      Stk c s h (L ++ [w] ++ stF ++ X) → EnvB c s h (L ++ [w] ++ stF ++ X) env vals d Fs →
      ∃ r, SC.Ex c code s r ∧ TB c s h L w (RgC env.length d d' Fs) σ ρ (denT (inpW c) t vals) r
  | .ret e, env, vals, code, σ, ρ, x, L, w, stF, X, d, d', Fs, s, h, hF, hX, hct, hlv, hs, he => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at hct; split at hct
    · rename_i ce τ hce; split at hct
      · rename_i hcond; obtain ⟨rfl, hl1, hl2⟩ := hcond
        simp only [Option.some.injEq] at hct; subst hct
        unfold Lim at hl1 hl2
        have P := cB_ok hc e env vals ce τ _ d d' Fs s h (by rw [hlen]; exact hce) (lvT_ret hlv) hs he
        rw [show L ++ [w] ++ stF ++ X = L ++ ([w] ++ stF ++ X) by simp] at P
        have P' := PB.slide hc (RgC.below he) hl2 (by simp [hF, hX]; omega) P
        rw [show ([w] ++ stF ++ X).length = σ.size + 1 + x by simp [hF, hX]; omega] at P'
        obtain ⟨r, e1, p1⟩ := P'
        simp only [denT]
        cases r with
        | ok s1 => exact ⟨_, .seq e1 .jmp, .inr (.inr ⟨rfl, p1⟩)⟩
        | jmp t s1 => exact ⟨_, .seqJ e1, p1.elim .inl (fun h' => .inr (.inl h'))⟩
      · simp at hct
    · simp at hct
  | .next e, env, vals, code, σ, ρ, x, L, w, stF, X, d, d', Fs, s, h, hF, hX, hct, hlv, hs, he => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at hct; split at hct
    · rename_i ce τ hce; split at hct
      · rename_i hcond; obtain ⟨rfl, hl1⟩ := hcond
        simp only [Option.some.injEq] at hct; subst hct
        unfold Lim at hl1
        have P := cB_ok hc e env vals ce τ _ d d' Fs s h (by rw [hlen]; exact hce) (lvT_next hlv) hs he
        rw [show L ++ [w] ++ stF ++ X = (L ++ [w]) ++ (stF ++ X) by simp] at P
        have P' := PB.slide hc (RgC.below he) (by omega) (by simp [hF, hX]; omega) P
        rw [show (stF ++ X).length = τ.size + x by simp [hF, hX]] at P'
        obtain ⟨r, e1, p1⟩ := P'
        simp only [denT]
        cases r with
        | ok s1 => exact ⟨_, .seq e1 .jmp, .inr (.inr ⟨rfl, p1⟩)⟩
        | jmp t s1 => exact ⟨_, .seqJ e1, p1.elim .inl (fun h' => .inr (.inl h'))⟩
      · simp at hct
    · simp at hct
  | .ite k a b t e, env, vals, code, σ, ρ, x, L, w, stF, X, d, d', Fs, s, h, hF, hX, hct, hlv, hs, he => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at hct; split at hct
    · rename_i ca cb ct ce ha hb ht hte
      simp only [Option.some.injEq] at hct; subst hct
      obtain ⟨d1, d2, x1, y1, h1, h2, h3, h4, rfl⟩ := lvT_ite hlv
      obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lv_step _ _ _ _ h2
      obtain ⟨st3, l3⟩ := lvT_step _ _ _ _ h3; obtain ⟨st4, l4⟩ := lvT_step _ _ _ _ h4
      have P := pairB he st1 st2 l1 (cB_ok hc a env vals ca .w _ d d1 Fs s h (by rw [hlen]; exact ha) h1 hs he)
        (fun s1 h1' W _ hs1 hW he1 => cB_ok hc b env vals cb .w (L ++ [w] ++ stF ++ X ++ W) d1 d2 Fs s1 h1'
          (by rw [List.length_append, hW, hlen]; exact hb) h2 hs1 he1)
      have st12 := st1.trans st2
      obtain ⟨R1, Rx, Ry⟩ := ite_rg (n := env.length) (Fs := Fs) st12 st3 st4 l3 l4
      simp only [denT]
      refine (fun ⟨r, e, p⟩ => ⟨r, seq_assoc e, p⟩) (thenB (fun t' s' ht => ?_) P ?_)
      · rcases ht with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl)
      rintro s1 ⟨h1', W, F, hh, h8', hs1, ⟨W1, W2, F1, F2, rfl, hv1, hv2, _, _⟩, _, k1⟩
      obtain ⟨-, rfl, _⟩ := hv1.wd; obtain ⟨-, rfl, _⟩ := hv2.wd
      obtain ⟨s2, e2, g0, g1, hs2, k2⟩ := pop2_ok (L := L ++ [w] ++ stF ++ X) hc (by simpa using hs1)
      have k12 : KeepB s s2 h (RgC env.length d d2 Fs) := k1.keep k2 (by rw [hs1.hp]; exact hh)
      have he2 : EnvB c s2 h1' (L ++ [w] ++ stF ++ X) env vals d2 Fs := by
        simpa using he.after (M := []) st12 (l2.trans l1) k12 hh h8'
      cases hk : k.eval (den (inpW c) a vals).word (den (inpW c) b vals).word
      · obtain ⟨r, er, pr⟩ := cTB_ok hc e env vals ce σ ρ x L w stF X d2 y1 Fs s2 h1' hF hX hte h4 hs2 he2
        refine ⟨r, .seq (.ins e2) (.iteF (by rw [g0, g1, BOp.ofCmp_eval, hk]) er), ?_⟩
        simp only [Bool.false_eq_true, if_false]
        exact TB.after k12 hh (fun z _ hz => R1 z hz) (fun z hz => .inl (Ry z hz)) pr
      · obtain ⟨r, er, pr⟩ := cTB_ok hc t env vals ct σ ρ x L w stF X d2 x1 Fs s2 h1' hF hX ht h3 hs2 he2
        refine ⟨r, .seq (.ins e2) (.iteT (by rw [g0, g1, BOp.ofCmp_eval, hk]) er), ?_⟩
        simp only [if_true]
        exact TB.after k12 hh (fun z _ hz => R1 z hz) (fun z hz => .inl (Rx z hz)) pr
    · simp at hct
  | .let_ v b, env, vals, code, σ, ρ, x, L, w, stF, X, d, d', Fs, s, h, hF, hX, hct, hlv, hs, he => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at hct; split at hct
    · rename_i cv τv hv; split at hct
      · rename_i cb hb
        simp only [Option.some.injEq] at hct; subst hct
        simp only [denT]
        rcases lvT_let hlv with ⟨j, τj, d'', rfl, hj, hbuf, hdj, h1, rfl⟩ | ⟨τ', d1, d'', hty, h1, h2, rfl⟩
        · obtain ⟨p, hjp, hb1, hp1, rfl⟩ := cE_var (by rw [← hlen] at hv; exact hv)
          have hτ : τj = τv := by simp [List.getElem?_map, hjp] at hj; exact hj.symm
          subst hτ
          simp only [den]
          obtain ⟨r1, e1, p1⟩ := var_post hc hs he hjp hb1 hp1
          cases r1 with
          | jmp t s1 => exact ⟨_, .seqJ e1, by rw [p1]; exact .inl rfl⟩
          | ok s1 =>
            obtain ⟨hs1, k1⟩ := p1
            let M := L ++ [w] ++ stF ++ X
            have hsl : p + τj.size ≤ M.length := he.slot j _ p hjp
            have hW : ((M.drop p).take τj.size).length = τj.size := by
              simp only [List.length_take, List.length_drop]; omega
            have k1' := k1.toB hs.hp (RgC env.length d (d''.tail.set j (fl d j)) Fs)
            have he1 := he.after (M := (M.drop p).take τj.size) (Step.refl _ d) rfl
              (k1.toB hs.hp _) (Nat.le_refl _) he.h8
            have he2 := he1.alias hjp hbuf (by rw [getD_append_take hsl]) hdj
            rw [show M.length = L.length + 1 + σ.size + x from hlen] at he2
            obtain ⟨r, e, pr⟩ := cTB_ok hc b _ _ cb σ ρ (x + τj.size) L w stF (X ++ (M.drop p).take τj.size) _ d''
              _ s1 h hF (by simp [hX, hW]) hb (by simpa using h1) (by simpa [M] using hs1) (by simpa [M] using he2)
            exact ⟨r, .seq e1 e, TB.after k1' (Nat.le_refl _) (fun _ _ h => h)
              (fun z hz => .inl (RgC.alias (by rw [he.dl]; exact lt_of_getElem? hjp) hz)) pr⟩
        · have hτ' : τ' = τv := by rw [cE_tyOf v env _ cv τv hv] at hty; exact (Option.some.inj hty).symm
          subst hτ'
          obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lvT_step _ _ _ _ h2
          obtain ⟨st3, _⟩ := step_tail st2 (by simpa using l2)
          refine thenB (fun t' s' ht => ?_) (cB_ok hc v env vals cv τ' _ d d1 Fs s h (by rw [hlen]; exact hv) h1 hs he) ?_
          · rcases ht with rfl | rfl
            · exact .inl rfl
            · exact .inr (.inl rfl)
          rintro s1 ⟨h1', W, F, hh, h8', hs1, hv1, hFv, k1⟩
          have hW := hv1.len
          have he1 := he.after (M := W) st1 l1 k1 hh h8'
          have he2 := he1.push hv1 (fresh_low he hh hFv) (fresh_disj he st1 hFv)
          rw [hlen] at he2
          obtain ⟨r, e, pr⟩ := cTB_ok hc b _ _ cb σ ρ (x + τ'.size) L w stF (X ++ W) _ d'' _ s1 h1' hF
            (by simp [hX, hW]) hb (by simpa using h2) (by simpa using hs1) (by simpa using he2)
          refine ⟨r, e, TB.after k1 hh ?_ ?_ pr⟩
          · intro z _ hz; exact hz.mono (fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩)
          · intro z hz
            rcases RgC.cons hz with hF' | hR
            · rcases hFv z hF' with h' | h'
              · exact .inl (h'.mono (fun k _ a b => ⟨a, by rcases st3 k with h'' | ⟨h'', _⟩ <;> omega⟩))
              · exact .inr h'
            · exact .inl (RgC.trans st1 st3 (.inr hR))
      · simp at hct
    · simp at hct
  | .split e b, env, vals, code, σ, ρ, x, L, w, stF, X, d, d', Fs, s, h, hF, hX, hct, hlv, hs, he => by
    have hlen : (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x := by simp [hF, hX]; omega
    unfold cT at hct; split at hct
    · rename_i ce τ1 σ1 he'; split at hct
      · rename_i cb hb
        simp only [Option.some.injEq] at hct; subst hct
        obtain ⟨τ', σ', d1, d'', hty, h1, h2, rfl⟩ := lvT_split hlv
        have hτ : Ty.prod τ' σ' = .prod τ1 σ1 := by
          rw [cE_tyOf e env _ ce _ he'] at hty; exact (Option.some.inj hty).symm
        simp only [Ty.prod.injEq] at hτ; obtain ⟨rfl, rfl⟩ := hτ
        obtain ⟨st1, l1⟩ := lv_step _ _ _ _ h1; obtain ⟨st2, l2⟩ := lvT_step _ _ _ _ h2
        obtain ⟨st3, _⟩ := step_drop2 st2 (by simpa using l2)
        simp only [denT]
        refine thenB (fun t' s' ht => ?_) (cB_ok hc e env vals ce _ _ d d1 Fs s h (by rw [hlen]; exact he') h1 hs he) ?_
        · rcases ht with rfl | rfl
          · exact .inl rfl
          · exact .inr (.inl rfl)
        rintro s1 ⟨h1', W, F, hh, h8', hs1, hv, hFv, k1⟩
        generalize den (inpW c) e vals = V at hv ⊢
        cases V with
        | pr u v =>
          obtain ⟨W1, W2, F1, F2, rfl, hv1, hv2, hd12, hFF⟩ := hv
          have hW1 := hv1.len; have hW2 := hv2.len
          have hlow := fresh_low he hh hFv
          have hdis := fresh_disj he st1 hFv
          have heA := he.after (M := W1) st1 l1 k1 hh h8'
          have heB := heA.push hv1 (fun y hy => hlow y ((hFF y).2 (.inl hy)))
            (fun k hk hd y hy => hdis k hk hd y ((hFF y).2 (.inl hy)))
          have heC := (heB.ext W2).push hv2 (fun y hy => hlow y ((hFF y).2 (.inr hy))) (by
            intro k hk hd y hy hy'
            cases k with
            | zero => exact hd12 y hy' hy
            | succ k =>
              simp only [fl_cons_succ] at hd
              exact hdis k (by simpa using hk) hd y ((hFF y).2 (.inr hy)) hy')
          rw [show (L ++ [w] ++ stF ++ X ++ W1).length = L.length + 1 + σ.size + x + τ'.size by
              rw [List.length_append, hW1, hlen],
            show (L ++ [w] ++ stF ++ X).length = L.length + 1 + σ.size + x from hlen] at heC
          obtain ⟨r, e2, pr⟩ := cTB_ok hc b _ _ cb σ ρ (x + τ'.size + σ'.size) L w stF (X ++ W1 ++ W2) _ d'' _
            s1 h1' hF (by simp [hX, hW1, hW2]; omega) hb (by simpa using h2) (by simpa using hs1) (by simpa using heC)
          refine ⟨r, e2, TB.after k1 hh ?_ ?_ pr⟩
          · intro z _ hz; exact hz.mono (fun k _ a b => ⟨a, by rcases st3 k with h' | ⟨h', _⟩ <;> omega⟩)
          · intro z hz
            have hFz : F z → RgC env.length d (d''.drop 2) Fs z ∨ (h ≤ z ∧ z < h1') := fun hF' => by
              rcases hFv z hF' with h' | h'
              · exact .inl (h'.mono (fun k _ a b => ⟨a, by rcases st3 k with h'' | ⟨h'', _⟩ <;> omega⟩))
              · exact .inr h'
            rcases RgC.cons2 hz with h' | h' | h'
            · exact hFz ((hFF z).2 (.inr h'))
            · exact hFz ((hFF z).2 (.inl h'))
            · exact .inl (RgC.trans st1 st3 (.inr h'))
        | wd _ => exact hv.elim
        | bf _ => exact hv.elim
      · simp at hct
    · simp at hct
end

end Nano.V2B


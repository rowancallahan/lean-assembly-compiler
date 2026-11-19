/- Machine bridge (Opus box E): the multi-word HEAP contract `EVHw` (success path).
`EVHw C pc len p nl Inv hb R W w S`: if the semantics `S env sp H` succeeds with `(vs, H')`, the code at [pc, pc+len)
pushes the w words `vs` (component i at old t6 − 8(i+1)), keeps s0, the frame up to its own lets `W`, every cell at or
above the old t6 except those slots, `Inv`, x0 = 0, and the heap relation moves from H to H'.  `S` reads only the slots
in `R`.  `HeapEV.EVH` is the one-word case (`ofEVH` / `toEVH`); compound templates here: `nilX`, `pairX` (operand
sequences, PAIR, multi-word LOCAL), `ifX` (IF with multi-word arms), `letX` (LET of width w). -/
import Nano.V2Self.Proof.HeapEV
namespace Templates
open CallProbe

abbrev Env := Nat → UInt64
abbrev SemW := Env → Nat → Hp → Option (List UInt64 × Hp)

structure EVHw (C : List J) (pc len p nl : Nat) (Inv : St → Prop) (hb : Nat) (R W : Nat → Prop) (w : Nat)
    (S : SemW) : Prop where
  run : ∀ (s : St) (env : Env) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H → S env (s.x 31).toNat H = some (vs, H') →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
      vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧ HRel hb s' H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

/-- one word as a list -/
def one (S : Env → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (S env sp H).map fun r => ([r.1], r.2)

/-- the head word of a result (for one-word operands) -/
def hd1 (S : SemW) : Env → Nat → Hp → Option (UInt64 × Hp) :=
  fun env sp H => (S env sp H).bind fun r => match r.1 with | [v] => some (v, r.2) | _ => none

theorem ofEVH {C : List J} {pc len p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {S : Env → Nat → Hp → Option (UInt64 × Hp)} (h : EVH C pc len p nl Inv hb R W S) :
    EVHw C pc len p nl Inv hb R W 1 (one S) where
  stable := fun env env' sp H hk => by simp only [one]; rw [h.stable env env' sp H hk]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [one, Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H1⟩, hS, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s', env', r, I, z, p31, vm, e8, F, ag, hR, mm⟩ := h.run s env H v H1 I0 z0 F0 O0 R0 hS
    refine ⟨s', env', r, I, z, by rw [p31], rfl, fun i hi => ?_, e8, F, ag, hR, mm⟩
    have : i = 0 := by omega
    subst this; simpa using vm

theorem toEVH {C : List J} {pc len p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHw C pc len p nl Inv hb R W 1 S) : EVH C pc len p nl Inv hb R W (hd1 S) where
  stable := fun env env' sp H hk => by simp only [hd1]; rw [h.stable env env' sp H hk]
  run := fun s env H v H' I0 z0 F0 O0 R0 hS => by
    simp only [hd1, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨vs, H1⟩, hS, e⟩ := hS
    obtain ⟨s', env', r, I, z, p31, hl, vm, e8, F, ag, hR, mm⟩ := h.run s env H vs H1 I0 z0 F0 O0 R0 hS
    match vs, hl, e with
    | [x], _, e =>
      simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨s', env', r, I, z, by rw [p31], by simpa using vm 0 (by omega), e8, F, ag, hR, mm⟩

/-- for a one-word semantics that only ever returns one word, `one (hd1 S) = S` -/
theorem one_hd1 {S : SemW} (h : ∀ env sp H vs H', S env sp H = some (vs, H') → vs.length = 1) :
    one (hd1 S) = S := by
  funext env sp H
  simp only [one, hd1]
  cases e : S env sp H with
  | none => rfl
  | some r =>
    obtain ⟨vs, H'⟩ := r
    have := h env sp H vs H' e
    match vs, this with
    | [x], _ => rfl

/-! ## the empty fragment and sequencing -/

def nilS : SemW := fun _ _ H => some ([], H)

theorem nilX {C : List J} {pc p nl hb : Nat} {Inv : St → Prop} :
    EVHw C pc 0 p nl Inv hb (fun _ => False) (fun _ => False) 0 nilS where
  stable := fun _ _ _ _ _ => rfl
  run := fun s env H vs H' I0 z0 F0 _ R0 hS => by
    simp only [nilS, Option.some.injEq, Prod.mk.injEq] at hS; obtain ⟨rfl, rfl⟩ := hS
    exact ⟨s, env, by simpa using Star.refl (pc, s), I0, z0, by omega, rfl, fun i hi => absurd hi (by omega), rfl, F0,
      fun _ _ => rfl, R0, fun _ _ _ => rfl⟩

def pairS (wa : Nat) (SA SB : SemW) : SemW :=
  fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8 * wa) r1.2).bind fun r2 => some (r1.1 ++ r2.1, r2.2)

theorem hrel_sp {hb : Nat} {s : St} {H : Hp} (h : HRel hb s H) : 16 ≤ (s.x 31).toNat := by
  obtain ⟨a, b, c, _⟩ := h; omega

/-- **A then B** (operand sequences, PAIR, multi-word LOCAL): B reads none of A's lets -/
theorem pairX {C : List J} {pc la lb p nl hb wa wb : Nat} {Inv : St → Prop} {RA WA RB WB : Nat → Prop} {SA SB : SemW}
    (hA : EVHw C pc la p nl Inv hb RA WA wa SA) (hB : EVHw C (pc + la) lb p nl Inv hb RB WB wb SB)
    (sB : ∀ k, RB k → ¬ WA k) :
    EVHw C pc (la + lb) p nl Inv hb (fun k => RA k ∨ RB k) (fun k => WA k ∨ WB k) (wa + wb) (pairS wa SA SB) where
  stable := fun env env' sp H h => by
    simp only [pairS]
    rw [hA.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SA env' sp H with
    | none => rfl
    | some r1 => simp only [Option.bind_some]; rw [hB.stable env env' _ r1.2 (fun k hk => h k (Or.inr hk))]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    obtain ⟨o1, o2, o3⟩ := O0
    simp only [pairS, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨⟨a, H1⟩, hSA, ⟨b, H2⟩, hSB, rfl, rfl⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, la1, v1, e81, F1, ag1, R1, m1⟩ := hA.run s env H a H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 hSA
    have hs1 := hrel_sp R1
    have hSB1 : SB env1 (s1.x 31).toNat H1 = some (b, H2) := by
      rw [p1, hB.stable env1 env _ _ (fun k hk => ag1 k (sB k hk))]; exact hSB
    obtain ⟨s2, env2, r2, I2, z2, p2, lb2, v2, e82, F2, ag2, R2, m2⟩ :=
      hB.run s1 env1 H1 b H2 I1 z1 F1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ R1 hSB1
    rw [p1] at p2 v2 m2; rw [e81] at m2
    refine ⟨s2, env2, by rw [← Nat.add_assoc]; exact r1.trans r2, I2, z2, by rw [p2]; omega, by simp [la1, lb2],
      ?_, by rw [e82, e81], F2, ?_, R2, ?_⟩
    · intro i hi
      by_cases hi' : i < wa
      · rw [m2 _ (by omega) (fun k hk _ => by
          have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega), v1 i hi']
        rw [getD_app_l _ _ _ (by rw [la1]; exact hi')]
      · have := v2 (i - wa) (by omega)
        rw [show (s.x 31).toNat - 8 * wa - 8 * (i - wa + 1) = (s.x 31).toNat - 8 * (i + 1) by omega] at this
        rw [this, getD_app_r _ _ _ (by rw [la1]; omega), la1]
    · intro k hk; simp only [not_or] at hk; rw [ag2 k hk.2, ag1 k hk.1]
    · intro a ha hw
      rw [m2 a (by omega) (fun k hk wk => hw k hk (Or.inr wk)), m1 a ha (fun k hk wk => hw k hk (Or.inl wk))]

/-! ## IF with multi-word arms -/

/-- the compare instruction of the IF head (Gen: cmp 1 = `beq`, otherwise `bltu`) -/
def cmpJ (cmp : Nat) : J := if cmp = 1 then .beq 5 6 2 else .bltu 5 6 2
def cmpF (cmp : Nat) (a b : UInt64) : Prop := if cmp = 1 then a = b else a.toNat < b.toNat
instance (cmp : Nat) (a b : UInt64) : Decidable (cmpF cmp a b) := by unfold cmpF; split <;> infer_instance

def ifHeadG (cmp lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, cmpJ cmp, .jal 0 ((lt : Int) + 2)]

def ifS (cmp : Nat) (SP ST SE : SemW) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => if cmpF cmp a b then ST env sp r.2 else SE env sp r.2
    | _ => none

theorem step_cmp {C : List J} {q cmp : Nat} {s : St} (hc : C[q]? = some (cmpJ cmp)) :
    step C (q, s) = some (if cmpF cmp (s.x 5) (s.x 6) then q + 2 else q + 1, s) := by
  by_cases h : cmp = 1
  · simp only [cmpJ, h, if_true] at hc; simp only [cmpF, h, if_true, step, hc]
    by_cases e : s.x 5 = s.x 6 <;> simp [e]; omega
  · simp only [cmpJ, h, if_false] at hc; simp only [cmpF, h, if_false, step, hc]
    by_cases e : (s.x 5).toNat < (s.x 6).toNat <;> simp [e]; omega

/-- **IF**: P (the two operands, `[a, b]`); head; T; jal END; E.  T and E read none of P's lets. -/
theorem ifX {C : List J} {pc lp lt le p nl hb w cmp : Nat} {Inv : St → Prop} {RP WP RT WT RE WE : Nat → Prop}
    {SP ST SE : SemW} (hI : InvOKH hb p Inv)
    (hP : EVHw C pc lp p nl Inv hb RP WP 2 SP) (hH : At C (pc + lp) (ifHeadG cmp lt))
    (hT : EVHw C (pc + lp + 5) lt p nl Inv hb RT WT w ST)
    (hJ : C[pc + lp + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : EVHw C (pc + lp + 6 + lt) le p nl Inv hb RE WE w SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) :
    EVHw C pc (lp + 6 + lt + le) p nl Inv hb (fun k => RP k ∨ RT k ∨ RE k) (fun k => WP k ∨ WT k ∨ WE k) w
      (ifS cmp SP ST SE) where
  stable := fun env env' sp H h => by
    simp only [ifS]
    rw [hP.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SP env' sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      rw [hT.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inl hk))),
        hE.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    simp only [ifS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 hSP
    match ab, l1, hS, v1 with
    | [a, b], _, hS, v1 =>
    have va : s1.m ((s.x 31).toNat - 8) = a := by simpa using v1 0 (by omega)
    have vb : s1.m ((s.x 31).toNat - 8 - 8) = b := by
      have := v1 1 (by omega); rw [show (s.x 31).toNat - 8 * (1 + 1) = (s.x 31).toNat - 8 - 8 by omega] at this
      simpa using this
    dsimp only at hS
    have c0 := hH.at 0 (by simp [ifHeadG]); have c1 := hH.at 1 (by simp [ifHeadG])
    have c2 := hH.at 2 (by simp [ifHeadG]); have c3 := hH.at 3 (by simp [ifHeadG])
    have c4 := hH.at 4 (by simp [ifHeadG])
    simp only [ifHeadG, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4
    have sp1 := hrel_sp R1
    have ea0 : ea (s1.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p1]; omega
    have ea8 : ea (s1.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p1]; omega
    have ea16 : ea (s1.x 31) 16 = (s.x 31).toNat := by simp [ea, p1]; omega
    let s2 : St := ⟨upd (upd (upd s1.x 6 b) 5 a) 31 (UInt64.ofNat (s.x 31).toNat), s1.m, s1.b⟩
    have r2 : run C 3 (pc + lp, s1) = some (pc + lp + 3, s2) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s2]
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by simp [s2, upd]
    have x8 : s2.x 8 = s.x 8 := by simp [s2, upd, e81]
    have x30 : s2.x 30 = s1.x 30 := by simp [s2, upd]
    have x5 : s2.x 5 = a := by simp [s2, upd]
    have x6 : s2.x 6 = b := by simp [s2, upd]
    have z2 : s2.x 0 = 0 := by simp [s2, upd, z1]
    have I2 : Inv s2 := hI s1 s2 I1 (by simp [s2, upd]) (by simp [s2, upd]) (by simp [s2, upd]) (fun _ _ => rfl)
    have F2 : Frame p nl s2 env1 := by
      intro k hk; show s1.m (slotAddr p (s2.x 8).toNat k) = env1 k; rw [x8, ← e81]; exact F1 k hk
    have O2 : FrameOK p nl s2 := ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩
    have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun _ _ _ => rfl)
    have st2 : Star C (pc, s) (pc + lp + 3, s2) := r1.trans (run_star r2)
    have mm : ∀ a', (s.x 31).toNat ≤ a' → (∀ k, k < nl → WP k → a' ≠ slotAddr p (s.x 8).toNat k) → s2.m a' = s.m a' :=
      fun a' h1 h2 => m1 a' h1 h2
    have sc := step_cmp (s := s2) c3
    rw [x5, x6] at sc
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at hS sc
      have hST : ST env1 (s2.x 31).toNat H1 = some (vs, H') := by
        rw [x31, hT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact hS
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, v4, e84, F4, ag4, R4, m4⟩ := hT.run s2 env1 H1 vs H' I2 z2 F2 O2 R2 hST
      have sj : step C (pc + lp + 5 + lt, s4) =
          some (pc + (lp + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + lp + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      have w4 : wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + lp + 5 + lt + 1))) = s4 := by simp [wr]
      rw [w4] at sj
      refine ⟨s4, env4, (st2.tail sc |>.trans r4).tail sj, I4, z4, by rw [p4, x31], l4, ?_, by rw [e84, x8], F4, ?_,
        R4, ?_⟩
      · intro i hi; rw [x31] at v4; exact v4 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.1, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inl wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]
    · rw [if_neg hc] at hS sc
      have hSE : SE env1 (s2.x 31).toNat H1 = some (vs, H') := by
        rw [x31, hE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact hS
      have sj0 : step C (pc + lp + 4, s2) =
          some (pc + lp + 6 + lt, wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1)))) := by
        simp [step, c4]; omega
      have w2 : wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1))) = s2 := by simp [wr]
      rw [w2] at sj0
      obtain ⟨s5, env5, r5, I5, z5, p5, l5, v5, e85, F5, ag5, R5, m5⟩ := hE.run s2 env1 H1 vs H' I2 z2 F2 O2 R2 hSE
      refine ⟨s5, env5, ?_, I5, z5, by rw [p5, x31], l5, ?_, by rw [e85, x8], F5, ?_, R5, ?_⟩
      · have : pc + lp + 6 + lt + le = pc + (lp + 6 + lt + le) := by omega
        rw [← this]; exact ((st2.tail sc).tail sj0).trans r5
      · intro i hi; rw [x31] at v5; exact v5 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag5 k hk.2.2, ag1 k hk.1]
      · intro a' ha hW
        rw [m5 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]

/-! ## LET of width w -/

/-- slots k0 … k0+w−1 get the words of `vs` -/
def setW (env : Env) (k0 w : Nat) (vs : List UInt64) : Env :=
  fun k => if k0 ≤ k ∧ k < k0 + w then vs.getD (k - k0) 0 else env k

def letS (k0 w : Nat) (SV SB : SemW) : SemW :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2

/-- **LET** (width w): value; pop into slots k0 … k0+w−1 (g26); body.  Scoping: the body reads none of the value's own
lets (other than through the bound slots). -/
theorem letX {C : List J} {pc lv lb p nl hb k0 w wb : Nat} {Inv : St → Prop} {Rv Wv Rb Wb : Nat → Prop}
    {SV SB : SemW} (hI : InvOKH hb p Inv)
    (hv : EVHw C pc lv p nl Inv hb Rv Wv w SV) (hS : At C (pc + lv) (popN p k0 w))
    (hb' : EVHw C (pc + lv + 3 * w) lb p nl Inv hb Rb Wb wb SB)
    (hk0 : k0 + w ≤ nl) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) :
    EVHw C pc (lv + 3 * w + lb) p nl Inv hb (fun k => Rv k ∨ (Rb k ∧ ¬ (k0 ≤ k ∧ k < k0 + w)))
      (fun k => Wv k ∨ (k0 ≤ k ∧ k < k0 + w) ∨ Wb k) wb (letS k0 w SV SB) where
  stable := fun env env' sp H h => by
    simp only [letS]
    rw [hv.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SV env' sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      apply hb'.stable; intro k hk
      unfold setW
      split
      · rfl
      · rename_i hk'; exact h k (Or.inr ⟨hk, hk'⟩)
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS' => by
    simp only [letS, Option.bind_eq_some_iff] at hS'
    obtain ⟨⟨u, H1⟩, hSV, hSB⟩ := hS'
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, m1⟩ := hv.run s env H u H1 I0 z0 F0 O0 R0 hSV
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have sp1 := hrel_sp R1
    have T1 : (s1.x 31).toNat + 8 * w = (s.x 31).toNat := by rw [p1]; have := R1.2.2.1; omega
    obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := k0) w (pc + lv) s1 hS (by omega)
      (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
      (fun j i hj hi => by
        rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega); omega)
    rw [e81] at ms2 mo2
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
    have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
    have x30 : s2.x 30 = s1.x 30 := ex2 30 (by decide) (by decide)
    let env2 := setW env1 k0 w u
    have F2 : Frame p nl s2 env2 := by
      intro k hk
      show s2.m (slotAddr p (s2.x 8).toNat k) = env2 k
      rw [x8]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · have := ms2 (k - k0) (by omega)
        rw [show k0 + (k - k0) = k by omega] at this
        rw [this, show (s1.x 31).toNat + 8 * (w - 1 - (k - k0)) = (s.x 31).toNat - 8 * (k - k0 + 1) by omega,
          v1 (k - k0) (by omega)]
        simp [env2, setW, e]
      · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
        simp only [env2, setW, e, if_false]; rw [← e81]; exact F1 k hk
    have slot_hi : ∀ j, j < w → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat (k0 + j) ∧
        slotAddr p (s.x 8).toNat (k0 + j) < (s.x 8).toNat + 8 * p + 16 := fun j hj =>
      ⟨slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega), slotAddr_lt (nl := nl) (by omega) (by omega)⟩
    have I2 : Inv s2 := by
      apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide))
      intro a ha
      apply mo2 a; intro j hj e; apply ha; rw [e81, e]
      have hh := slot_hi j hj; have := R1.1; have := R1.2.1; have := R1.2.2.1
      exact ⟨by omega, hh.2⟩
    have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
    have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun a h1 h2 => by
      apply mo2 a; intro j hj e; have := slot_hi j hj; have := R1.2.2.1; omega)
    have hSB2 : SB env2 (s2.x 31).toNat H1 = some (vs, H') := by
      rw [x31]; rw [← hSB]; apply hb'.stable; intro k hk
      simp only [env2, setW]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · simp [e]
      · simp only [e, if_false]; exact ag1 k (hsc k hk e)
    obtain ⟨s3, env3, r3, I3, z3, p3, l3, v3, e83, F3, ag3, R3, m3⟩ :=
      hb'.run s2 env2 H1 vs H' I2 z2 F2 ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩ R2 hSB2
    refine ⟨s3, env3, ?_, I3, z3, by rw [p3, x31], l3, ?_, by rw [e83, x8], F3, ?_, R3, ?_⟩
    · have : pc + lv + 3 * w + lb = pc + (lv + 3 * w + lb) := by omega
      rw [← this]; exact (r1.trans (run_star r2)).trans r3
    · intro i hi; rw [x31] at v3; exact v3 i hi
    · intro k hk; simp only [not_or] at hk
      rw [ag3 k hk.2.2]; simp only [env2, setW, hk.2.1, if_false]; exact ag1 k hk.1
    · intro a ha hW
      rw [m3 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk)))]
      rw [mo2 a (fun j hj e => hW (k0 + j) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)) e)]
      exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

end Templates

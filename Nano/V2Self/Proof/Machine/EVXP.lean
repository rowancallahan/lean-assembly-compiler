/- Machine bridge (Opus box E): leaves and prim closings as `EVHw` fragments.
`leafX` (one checked push: CONST, LOCAL 1, LEN/ISIZE), `localX` (LOCAL of width w = w single pushes),
`fin1X` / `fin2X` / `fin3X` (an operand block of 1/2/3 words, then a closing fragment `Fin1/2/3`: BIN, RD, BSIZE,
BGET, BPUSH/PUT, BSET), `bnewX` (BNEW). -/
import Nano.V2Self.Proof.Machine.EVXC
import Nano.V2Self.Proof.Machine.ExprEV
namespace Templates
open CallProbe

/-- one checked push of `V env` (exact room condition: t5 + 8 ≤ t6) -/
def leafS (V : Env → UInt64) : SemW := fun env sp H => if H.top + 8 ≤ sp then some ([V env], H) else none

theorem leafX {C : List J} {pc len p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {V : Env → UInt64}
    (hI : InvOKH hb p Inv) (hst : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env')
    (hgo : ∀ (s : St) (env : Env), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
      (s.x 30).toNat + 8 ≤ (s.x 31).toNat →
      ∃ s', Star C (pc, s) (pc + len, s') ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
        s'.m = upd s.m ((s.x 31).toNat - 8) (V env) ∧ s'.x 8 = s.x 8 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
        s'.x 30 = s.x 30 ∧ s'.x 0 = s.x 0) :
    EVHw C pc len p nl Inv hb R W 1 (leafS V) where
  stable := fun env env' sp H h => by simp only [leafS]; rw [hst env env' h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [leafS] at hS
    split at hS
    rotate_left; · simp at hS
    rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hS; obtain ⟨rfl, rfl⟩ := hS
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    obtain ⟨s', r, p31, hm, e8, e28, e29, e30, e0⟩ := hgo s env I0 z0 F0 O0 (by omega)
    obtain ⟨o1, o2, o3⟩ := O0
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    refine ⟨s', env, r, ?_, by rw [e0, z0], by rw [p31], rfl, ?_, e8, ?_, fun _ _ => rfl, ?_, ?_⟩
    · apply hI s s' I0 e8 e28 e29 r.b
      intro a ha; rw [hm]; apply upd_other; intro e; apply ha; rw [e]
      exact ⟨by have := R0.2.1; omega, by omega⟩
    · intro i hi; have : i = 0 := by omega
      subst this; rw [hm]; simp [upd_same]
    · intro k hk; show s'.m (slotAddr p (s'.x 8).toNat k) = env k
      rw [e8, hm, upd_other _ _ (hne k hk)]; exact F0 k hk
    · exact HRel_stack R0 e30 (by rw [p31]; omega) (fun a _ h2 => by rw [hm]; apply upd_other; omega)
    · intro a ha _; rw [hm]; apply upd_other; omega

/-- CONST v -/
theorem constX {C : List J} {pc p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {v : UInt64}
    (hI : InvOKH hb p Inv) (hC : At C pc (constT 1 pc v)) :
    EVHw C pc ((liT 5 v).length + 4) p nl Inv hb R W 1 (leafS (fun _ => v)) :=
  leafX hI (fun _ _ _ => rfl) (fun s env _ hx0 _ _ room => by
    obtain ⟨s', hr, hx, hm⟩ := const_run s hx0 hC room
    have lt64 := (s.x 31).toNat_lt
    refine ⟨s', run_star hr, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    all_goals rw [hx]; simp [upd_ne])

/-- ISIZE / LEN: the input length (x29, kept by `Inv`) -/
theorem lenX {C : List J} {pc p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {c29 : UInt64}
    (hI : InvOKH hb p Inv) (hInv : ∀ s, Inv s → s.x 29 = c29) (hC : At C pc (lenT 1 pc)) :
    EVHw C pc 4 p nl Inv hb R W 1 (leafS (fun _ => c29)) :=
  leafX hI (fun _ _ _ => rfl) (fun s env I0 hx0 _ _ room => by
    have lt64 := (s.x 31).toNat_lt
    have hr := len_run s hC room
    refine ⟨_, run_star hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd_same, UInt64.toNat_ofNat']; omega
    · simp [hInv s I0]
    all_goals simp [upd_ne])

/-- LOCAL k, width 1 -/
theorem local1X {C : List J} {pc p nl hb k : Nat} {Inv : St → Prop} {W : Nat → Prop}
    (hI : InvOKH hb p Inv) (hp : p < 2 ^ 20) (hk : k < nl) (hC : At C pc (localT 1 p k pc 1)) :
    EVHw C pc 5 p nl Inv hb (fun j => j = k) W 1 (leafS (fun env => env k)) :=
  leafX hI (fun env env' h => h k rfl) (fun s env _ hx0 hF hO room => by
    obtain ⟨o1, o2, o3⟩ := hO
    have hv : CallProbe.slotAddr p k (s.x 8).toNat = slotAddr p (s.x 8).toNat k := slotAddr_eq (by omega) o2 hk
    have hkp : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat := by omega
    obtain ⟨s', hr, hx, hm⟩ := local1_run s hC (by omega) hp hkp room
    have lt64 := (s.x 31).toNat_lt
    rw [hv] at hx hm
    refine ⟨s', run_star hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; simp only [upd_same]; simp only [UInt64.toNat_ofNat']; omega
    · rw [hm, hF k hk]
    all_goals rw [hx]; simp [upd_ne])

/-- LOCAL k w: w single pushes -/
def localS (k : Nat) : Nat → SemW
  | 0 => nilS
  | w + 1 => pairS 1 (leafS (fun env => env k)) (localS (k + 1) w)

theorem localT_succ (tgt p k q w : Nat) : localT tgt p k q (w + 1) = localT tgt p k q 1 ++ localT tgt p (k + 1) (q + 5) w := by
  simp [localT]

theorem localX {C : List J} {p nl hb : Nat} {Inv : St → Prop}
    (hI : InvOKH hb p Inv) (hp : p < 2 ^ 20) :
    ∀ w k pc, k + w ≤ nl → At C pc (localT 1 p k pc w) →
      EVHw C pc (5 * w) p nl Inv hb (fun j => k ≤ j ∧ j < k + w) (fun _ => False) w (localS k w)
  | 0, k, pc, _, _ => (nilX (C := C) (pc := pc) (p := p) (nl := nl) (hb := hb) (Inv := Inv)).mono
      (fun _ h => h.elim) (fun _ h => h)
  | w + 1, k, pc, hk, hC => by
    rw [localT_succ] at hC
    have h1 := local1X (nl := nl) (k := k) (W := fun _ => False) hI hp (by omega) hC.left
    have h2 := localX (nl := nl) hI hp w (k + 1) (pc + 5) (by omega) (by simpa using hC.right)
    exact ((pairX h1 h2 (fun _ _ h => h)).mono (R' := fun j => k ≤ j ∧ j < k + (w + 1)) (W' := fun _ => False)
      (fun j q => by rcases q with e | ⟨e1, e2⟩ <;> constructor <;> omega)
      (fun j q => by rcases q with e | e <;> exact e)).len (len' := 5 * (w + 1)) (by omega) |>.wid (by omega)

/-! ## operand block + closing fragment -/

def fin1S (SP : SemW) (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a] => (F a (sp - 8) r.2).map fun x => ([x.1], x.2)
    | _ => none
def fin2S (SP : SemW) (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => (F a b (sp - 16) r.2).map fun x => ([x.1], x.2)
    | _ => none
def fin3S (SP : SemW) (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : SemW :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b, c] => (F a b c (sp - 24) r.2).map fun x => ([x.1], x.2)
    | _ => none

/-- the common tail: after the closing fragment the result word sits at sp − 8, all else as the operands left it -/
theorem finTail {C : List J} {pc q lu t p nl hb : Nat} {Inv : St → Prop} {W : Nat → Prop}
    (hI : InvOKH hb p Inv) (s s1 s3 : St) (env env1 : Env) (H3 : Hp) (v : UInt64)
    (I1 : Inv s1) (z1 : s1.x 0 = 0) (O0 : FrameOK p nl s) (e81 : s1.x 8 = s.x 8) (F1 : Frame p nl s1 env1)
    (ag1 : ∀ k, ¬ W k → env1 k = env k)
    (m1 : ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s1.m a = s.m a)
    (r1 : Star C (pc, s) (q, s1)) (st3 : Star C (q, s1) (q + lu, s3))
    (p3 : (s3.x 31).toNat = (s.x 31).toNat - 8) (v3 : s3.m ((s.x 31).toNat - 8) = v) (R3 : HRel hb s3 H3)
    (qx : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s3.x r = s1.x r)
    (qm : ∀ a, a ≠ (s.x 31).toNat - 8 → ¬ (hb ≤ a ∧ a < H3.top) → s3.m a = s1.m a)
    (sp16 : 16 ≤ (s.x 31).toNat) (hq : q + lu = t) :
    ∃ s' env', Star C (pc, s) (t, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 * 1 ∧ [v].length = 1 ∧
      (∀ i, i < 1 → s'.m ((s.x 31).toNat - 8 * (i + 1)) = [v].getD i 0) ∧ s'.x 8 = s.x 8 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧ HRel hb s' H3 ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a := by
  obtain ⟨o1, o2, o3⟩ := O0
  have top3 := R3.2.2.1
  have q8 : s3.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e81]
  refine ⟨s3, env1, by rw [← hq]; exact r1.trans st3, ?_, ?_, by rw [p3], rfl, ?_, q8, ?_, ag1, R3, ?_⟩
  · apply hI s1 s3 I1 (by rw [q8, e81]) (qx 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) st3.b
    intro a ha
    apply qm
    · intro e; apply ha; rw [e, e81]; constructor
      · have := R3.2.1; omega
      · omega
    · intro ⟨h1, h2⟩; apply ha; rw [e81]; exact ⟨h1, by omega⟩
  · rw [qx 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), z1]
  · intro i hi; have : i = 0 := by omega
    subst this; simpa using v3
  · intro k hk
    show s3.m (slotAddr p (s3.x 8).toNat k) = env1 k
    have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
    rw [q8, qm _ (by omega) (by intro ⟨_, h2⟩; omega)]
    have := F1 k hk; rw [e81] at this; exact this
  · intro a ha hW
    rw [qm a (by omega) (by intro ⟨_, h2⟩; omega)]; exact m1 a ha hW

theorem fin2X {C : List J} {pc lp lu p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHw C pc lp p nl Inv hb R W 2 SP) (hU : Fin2 C (pc + lp) lu Inv hb F) :
    EVHw C pc (lp + lu) p nl Inv hb R W 1 (fin2S SP F) where
  stable := fun env env' sp H h => by simp only [fin2S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [fin2S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 hSP
    match ab, l1, hS, v1 with
    | [a, b], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have lt64 := (s.x 31).toNat_lt
    have va : s1.m ((s1.x 31).toNat + 8) = a := by
      rw [p1, show (s.x 31).toNat - 8 * 2 + 8 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have vb : s1.m (s1.x 31).toNat = b := by
      rw [p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 8 * (1 + 1) by omega]; simpa using v1 1 (by omega)
    have hF' : F (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H3) := by
      rw [va, vb, p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 16 by omega]; exact hF
    obtain ⟨s3, st3, q31, qv, R3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega) hF'
    rw [p1, show (s.x 31).toNat - 8 * 2 + 8 = (s.x 31).toNat - 8 by omega] at q31 qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 q31 qv R3 qx qm (by omega) (by omega)

theorem fin1X {C : List J} {pc lp lu p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHw C pc lp p nl Inv hb R W 1 SP) (hU : Fin1 C (pc + lp) lu Inv hb F) :
    EVHw C pc (lp + lu) p nl Inv hb R W 1 (fin1S SP F) where
  stable := fun env env' sp H h => by simp only [fin1S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [fin1S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 hSP
    match ab, l1, hS, v1 with
    | [a], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have va : s1.m (s1.x 31).toNat = a := by
      rw [p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have hF' : F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H3) := by
      rw [va, p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 by omega]; exact hF
    obtain ⟨s3, st3, q31, qv, R3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 hF'
    have q31' : (s3.x 31).toNat = (s.x 31).toNat - 8 := by rw [q31, p1]
    rw [p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 by omega] at qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 q31' qv R3
      (fun r a b c d e _ => qx r a b c d e) qm (by omega) (by omega)

theorem fin3X {C : List J} {pc lp lu p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHw C pc lp p nl Inv hb R W 3 SP) (hU : Fin3 C (pc + lp) lu Inv hb F) :
    EVHw C pc (lp + lu) p nl Inv hb R W 1 (fin3S SP F) where
  stable := fun env env' sp H h => by simp only [fin3S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [fin3S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 hSP
    match ab, l1, hS, v1 with
    | [a, b, c], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have va : s1.m ((s1.x 31).toNat + 16) = a := by
      rw [p1, show (s.x 31).toNat - 8 * 3 + 16 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have vb : s1.m ((s1.x 31).toNat + 8) = b := by
      rw [p1, show (s.x 31).toNat - 8 * 3 + 8 = (s.x 31).toNat - 8 * (1 + 1) by omega]; simpa using v1 1 (by omega)
    have vc : s1.m (s1.x 31).toNat = c := by
      rw [p1, show (s.x 31).toNat - 8 * 3 = (s.x 31).toNat - 8 * (2 + 1) by omega]; simpa using v1 2 (by omega)
    have hF' : F (s1.m ((s1.x 31).toNat + 16)) (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 =
        some (v, H3) := by
      rw [va, vb, vc, p1, show (s.x 31).toNat - 8 * 3 = (s.x 31).toNat - 24 by omega]; exact hF
    obtain ⟨s3, st3, q31, qv, R3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega) hF'
    rw [p1, show (s.x 31).toNat - 8 * 3 + 16 = (s.x 31).toNat - 8 by omega] at q31 qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 q31 qv R3 qx qm (by omega) (by omega)

/-- BNEW κ -/
theorem bnewX {C : List J} {pc κ p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    (hI : InvOKH hb p Inv) (hC : At C pc (bnewT 1 pc κ)) :
    EVHw C pc (bnewT 1 pc κ).length p nl Inv hb R W 1 (one (bnewS κ)) :=
  (ofEVH (bnew_EVH (nl := nl) hI hC)).mono (fun _ h => h.elim) (fun _ h => h.elim)

end Templates

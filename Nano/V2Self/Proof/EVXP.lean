/- Machine bridge (Opus box E): leaves and prim closings as `EVHw` fragments.
`leafX` (one checked push: CONST, LOCAL 1, LEN/ISIZE), `localX` (LOCAL of width w = w single pushes),
`fin1X` / `fin2X` / `fin3X` (an operand block of 1/2/3 words, then a closing fragment `Fin1/2/3`: BIN, RD, BSIZE,
BGET, BPUSH/PUT, BSET), `bnewX` (BNEW). -/
import Nano.V2Self.Proof.EVXC
import Nano.V2Self.Proof.ExprEV
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

end Templates

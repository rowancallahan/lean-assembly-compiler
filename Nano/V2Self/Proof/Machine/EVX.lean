/- Machine bridge (Opus box E): the multi-word HEAP contract `EVHw` (success path).
`EVHw C pc len p nl Inv hb R W w S`: if the semantics `S env sp H` succeeds with `(vs, H')`, the code at [pc, pc+len)
pushes the w words `vs` (component i at old t6 − 8(i+1)), keeps s0, the frame up to its own lets `W`, every cell at or
above the old t6 except those slots, `Inv`, x0 = 0, and the heap relation moves from H to H'.  `S` reads only the slots
in `R`.  `HeapEV.EVH` is the one-word case (`ofEVH` / `toEVH`); compound templates here: `nilX`, `pairX` (operand
sequences, PAIR, multi-word LOCAL), `ifX` (IF with multi-word arms), `letX` (LET of width w). -/
import Nano.V2Self.Proof.Machine.HeapEV
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

/-- weakening: more read slots, more written slots -/
theorem EVHw.mono {C : List J} {pc len p nl hb w : Nat} {Inv : St → Prop} {R W R' W' : Nat → Prop} {S : SemW}
    (h : EVHw C pc len p nl Inv hb R W w S) (hR : ∀ k, R k → R' k) (hW : ∀ k, W k → W' k) :
    EVHw C pc len p nl Inv hb R' W' w S where
  stable := fun env env' sp H hk => h.stable env env' sp H (fun k q => hk k (hR k q))
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    obtain ⟨s', env', r, I, z, p31, l, v, e8, F, ag, hRl, mm⟩ := h.run s env H vs H' I0 z0 F0 O0 R0 hS
    exact ⟨s', env', r, I, z, p31, l, v, e8, F, fun k hk => ag k (fun q => hk (hW k q)), hRl,
      fun a ha hw => mm a ha (fun k hk q => hw k hk (hW k q))⟩

/-- a fragment's length can be restated -/
theorem EVHw.len {C : List J} {pc len len' p nl hb w : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHw C pc len p nl Inv hb R W w S) (e : len = len') : EVHw C pc len' p nl Inv hb R W w S := e ▸ h

theorem EVHw.wid {C : List J} {pc len p nl hb w w' : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHw C pc len p nl Inv hb R W w S) (e : w = w') : EVHw C pc len p nl Inv hb R W w' S := e ▸ h

/-! ## the empty fragment and sequencing -/

def nilS : SemW := fun _ _ H => some ([], H)

def pairS (wa : Nat) (SA SB : SemW) : SemW :=
  fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8 * wa) r1.2).bind fun r2 => some (r1.1 ++ r2.1, r2.2)

theorem hrel_sp {hb : Nat} {s : St} {H : Hp} (h : HRel hb s H) : 16 ≤ (s.x 31).toNat := by
  obtain ⟨a, b, c, _⟩ := h; omega

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

/-! ## LET of width w -/

/-- slots k0 … k0+w−1 get the words of `vs` -/
def setW (env : Env) (k0 w : Nat) (vs : List UInt64) : Env :=
  fun k => if k0 ≤ k ∧ k < k0 + w then vs.getD (k - k0) 0 else env k

def letS (k0 w : Nat) (SV SB : SemW) : SemW :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2

end Templates

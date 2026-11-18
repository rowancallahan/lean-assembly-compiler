/- Astra-11 probe 2 (codegen): a NON-LEAF CALL with a LIVE expression-stack value, for C's fused code generator
(Nano/V2Self/C/Gen.lean, convention in Testing/notes/NANO_V2_CG.md).  Abstract machine: instruction-indexed pc,
64-bit registers, a word memory `Nat → UInt64` (8-byte cells; addresses are Nats, every address computation is
proved non-wrapping first).  The callee BODY is abstract (a hypothesis `Body`): it ends at the epilogue with the
result on top and writes only below its frame or into its own argument slots.  Statement: after the call returns,
t6 is exactly below the result, the result words are the body's, and EVERY cell at or above the caller's
pre-argument stack pointer (the live value and the caller's frame) is unchanged; s0 and the return pc are restored.
Registers: ra 1, t0 5, s0 8, a4 14, a5 15, t5 30 (heap top), t6 31 (expression stack). -/
namespace CallProbe

inductive J where
  | addi (rd rs : Nat) (imm : Int)
  | ld (rd rs : Nat) (off : Int)
  | sd (rs2 rs1 : Nat) (off : Int)
  | jal (rd : Nat) (off : Int)
  | jalr (rd rs : Nat)
  | bgeu (a b : Nat) (off : Int)

structure St where
  x : Nat → UInt64
  m : Nat → UInt64

def upd {α} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun i => if i = k then v else f i

def wr (s : St) (r : Nat) (v : UInt64) : St := if r = 0 then s else { s with x := upd s.x r v }
def ea (b : UInt64) (off : Int) : Nat := ((b.toNat : Int) + off).toNat

def step (C : List J) : Nat × St → Option (Nat × St)
  | (pc, s) => match C[pc]? with
    | some (.addi rd rs imm) => some (pc + 1, wr s rd (UInt64.ofNat (ea (s.x rs) imm)))
    | some (.ld rd rs off) => some (pc + 1, wr s rd (s.m (ea (s.x rs) off)))
    | some (.sd r2 r1 off) => some (pc + 1, { s with m := upd s.m (ea (s.x r1) off) (s.x r2) })
    | some (.jal rd off) => some (((pc : Int) + off).toNat, wr s rd (pc + 1).toUInt64)
    | some (.jalr rd rs) => some ((s.x rs).toNat, wr s rd (pc + 1).toUInt64)
    | some (.bgeu a b off) => some (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + off).toNat else pc + 1, s)
    | none => none

inductive Star (C : List J) : Nat × St → Nat × St → Prop
  | refl (a) : Star C a a
  | tail {a b c} : Star C a b → step C b = some c → Star C a c

theorem Star.trans {C a b c} (h1 : Star C a b) (h2 : Star C b c) : Star C a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact .tail ih h

theorem Star.one {C a b} (h : step C a = some b) : Star C a b := .tail (.refl a) h

/-- `l` sits in `C` at `pos` -/
def At (C : List J) (pos : Nat) (l : List J) : Prop := ∀ i, i < l.length → C[pos + i]? = l[i]?

/-! ## UInt64 arithmetic without wrap -/
theorem addi_toNat (b : UInt64) (imm : Int) (h : ea b imm < 2 ^ 64) : (UInt64.ofNat (ea b imm)).toNat = ea b imm := by
  simp [UInt64.toNat_ofNat]; omega

/-! ## one-instruction lemmas -/
section
variable {C : List J} {pc : Nat} {s : St}
theorem s_addi {rd rs imm} (h : C[pc]? = some (.addi rd rs imm)) :
    step C (pc, s) = some (pc + 1, wr s rd (UInt64.ofNat (ea (s.x rs) imm))) := by simp [step, h]
theorem s_ld {rd rs off} (h : C[pc]? = some (.ld rd rs off)) :
    step C (pc, s) = some (pc + 1, wr s rd (s.m (ea (s.x rs) off))) := by simp [step, h]
theorem s_sd {r2 r1 off} (h : C[pc]? = some (.sd r2 r1 off)) :
    step C (pc, s) = some (pc + 1, { s with m := upd s.m (ea (s.x r1) off) (s.x r2) }) := by simp [step, h]
theorem s_jal {rd off} (h : C[pc]? = some (.jal rd off)) :
    step C (pc, s) = some (((pc : Int) + off).toNat, wr s rd (pc + 1).toUInt64) := by simp [step, h]
theorem s_jalr {rd rs} (h : C[pc]? = some (.jalr rd rs)) :
    step C (pc, s) = some ((s.x rs).toNat, wr s rd (pc + 1).toUInt64) := by simp [step, h]
theorem s_bgeu_t {a b off} (h : C[pc]? = some (.bgeu a b off)) (hc : (s.x b).toNat ≤ (s.x a).toNat) :
    step C (pc, s) = some (((pc : Int) + off).toNat, s) := by simp [step, h, hc]
end

theorem At.get {C pos l} (h : At C pos l) {i} (hi : i < l.length) : C[pos + i]? = l[i]? := h i hi

/-! ## the push template (`g21`/`g22`): t6 -= 8; if t6 ≥ t5 skip; jal OOM; [t6] := r -/
def push (r : Nat) (oom : Int) : List J := [.addi 31 31 (-8), .bgeu 31 30 2, .jal 0 oom, .sd r 31 0]

theorem upd_same {α} (f : Nat → α) (k v) : upd f k v k = v := by simp [upd]
theorem upd_other {α} (f : Nat → α) {k i} (v : α) (h : i ≠ k) : upd f k v i = f i := by simp [upd, h]

/-- deterministic runs: `run C k a = some b` gives `Star C a b` -/
def run (C : List J) : Nat → Nat × St → Option (Nat × St)
  | 0, a => some a
  | k + 1, a => (step C a).bind (run C k)

theorem run_star {C} : ∀ {k a b}, run C k a = some b → Star C a b
  | 0, a, b, h => by simp [run] at h; subst h; exact .refl _
  | k + 1, a, b, h => by
    simp only [run] at h
    cases hs : step C a with
    | none => simp [hs] at h
    | some c => simp [hs] at h; exact (Star.one hs).trans (run_star h)

theorem run_add {C} : ∀ {k l a b}, run C k a = some b → run C (k + l) a = run C l b
  | 0, l, a, b, h => by simp [run] at h; subst h; simp
  | k + 1, l, a, b, h => by
    simp only [run] at h
    cases hs : step C a with
    | none => simp [hs] at h
    | some c => simp [hs] at h; rw [show k + 1 + l = (k + l) + 1 by omega]; simp [run, hs, run_add h]

theorem At.at {C pos l} (h : At C pos l) (i) (hi : i < l.length) : C[pos + i]? = l[i]? := h i hi

/-- push of register `r` (≠ 31, ≠ 0): needs t6 − 8 ≥ t5 (no out-of-memory) and t6 ≥ 8 -/
theorem push_run {C pc s r oom} (hC : At C pc (push r oom)) (hr : r ≠ 31) (hr0 : r ≠ 0)
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) :
    run C 3 (pc, s) = some (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)),
                                     upd s.m ((s.x 31).toNat - 8) (s.x r)⟩) := by
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e : ea (s.x 31) (-8) = (s.x 31).toNat - 8 := by simp [ea]; omega
  have t6' : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by
    simp [UInt64.toNat_ofNat]; omega
  have e0 : ea (UInt64.ofNat ((s.x 31).toNat - 8)) 0 = (s.x 31).toNat - 8 := by simp [ea, t6']
  have h0 := hC.at 0 (by simp [push]); have h1 := hC.at 1 (by simp [push])
  have h2 := hC.at 2 (by simp [push]); have h3 := hC.at 3 (by simp [push])
  simp only [push, Nat.add_zero] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  have c1 : (s.x 30).toNat ≤ (UInt64.ofNat ((s.x 31).toNat - 8)).toNat := by rw [t6']; omega
  have md : ((s.x 31).toNat - 8) % 18446744073709551616 = (s.x 31).toNat - 8 := by omega
  have c2 : (s.x 30).toNat ≤ (s.x 31).toNat - 8 := by omega
  have p3 : pc + 1 + 1 + 1 = pc + 3 := by omega
  simp [run, step, h0, h1, h3, e, wr, upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), md, c2, p3,
    show ((pc : Int) + 1 + 2).toNat = pc + 3 by omega]
  rw [e0, upd_other _ _ hr]

/-! ## the epilogue's result copy (`g29`): for j < q, t0 := [t6 + 8(q−1−j)]; [s0 + 8p + 16 − 8(j+1)] := t0 -/
def copyJ (p q j : Nat) : List J :=
  [.ld 5 31 (8 * ((q - 1 - j : Nat) : Int)), .sd 5 8 (8 * (p : Int) + 16 - 8 * ((j + 1 : Nat) : Int))]
def copy (p q : Nat) : Nat → List J
  | 0 => []
  | k + 1 => copy p q k ++ copyJ p q k

theorem copy_len (p q : Nat) : ∀ k, (copy p q k).length = 2 * k
  | 0 => rfl
  | k + 1 => by simp [copy, copyJ, copy_len p q k]; omega

/-- memory after the first k copies (sources read from the ORIGINAL memory) -/
def Mc (m : Nat → UInt64) (T D q : Nat) : Nat → (Nat → UInt64)
  | 0 => m
  | k + 1 => upd (Mc m T D q k) (D - 8 * (k + 1)) (m (T + 8 * (q - 1 - k)))

/-- a later source is never an earlier destination (D − 8q ≥ T: the copy moves up) -/
theorem Mc_src (m : Nat → UInt64) (T D q : Nat) (hD : T + 8 * q ≤ D) :
    ∀ k i, k ≤ i → i < q → Mc m T D q k (T + 8 * (q - 1 - i)) = m (T + 8 * (q - 1 - i))
  | 0, _, _, _ => rfl
  | k + 1, i, hk, hi => by
    simp only [Mc]; rw [upd_other _ _ (by omega)]; exact Mc_src m T D q hD k i (by omega) hi

theorem copy_run {C pc p q} (s : St) (hq : ∀ k, k ≤ q → At C pc (copy p q k))
    (hD : (s.x 31).toNat + 8 * q ≤ (s.x 8).toNat + 8 * p + 16) :
    ∀ k, k ≤ q → ∃ s', run C (2 * k) (pc, s) = some (pc + 2 * k, s') ∧ (∀ r, r ≠ 5 → s'.x r = s.x r) ∧
      s'.m = Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q k
  | 0, _ => ⟨s, by simp [run], fun _ _ => rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨s', hr, hx, hm⟩ := copy_run s hq hD k (by omega)
    have hA := hq (k + 1) hk
    have h0 : C[pc + 2 * k]? = some (.ld 5 31 (8 * ((q - 1 - k : Nat) : Int))) := by
      have := hA.at (2 * k) (by simp only [copy_len]; omega); simp [copy, copy_len, copyJ] at this; exact this
    have h1 : C[pc + 2 * k + 1]? = some (.sd 5 8 (8 * (p : Int) + 16 - 8 * ((k + 1 : Nat) : Int))) := by
      have := hA.at (2 * k + 1) (by simp only [copy_len]; omega)
      simp [copy, copy_len, copyJ] at this; rw [← Nat.add_assoc] at this; exact this
    have x31 := hx 31 (by decide); have x8 := hx 8 (by decide)
    have e1 : ea (s'.x 31) (8 * ((q - 1 - k : Nat) : Int)) = (s.x 31).toNat + 8 * (q - 1 - k) := by simp [ea, x31]; omega
    have e2 : ea (s'.x 8) (8 * (p : Int) + 16 - 8 * ((k + 1 : Nat) : Int)) = (s.x 8).toNat + 8 * p + 16 - 8 * (k + 1) := by
      simp [ea, x8]; omega
    refine ⟨⟨upd s'.x 5 (s.m ((s.x 31).toNat + 8 * (q - 1 - k))), Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q (k + 1)⟩, ?_, ?_, rfl⟩
    · rw [show 2 * (k + 1) = 2 * k + 2 by omega, run_add hr]
      have rd : s'.m ((s.x 31).toNat + 8 * (q - 1 - k)) = s.m ((s.x 31).toNat + 8 * (q - 1 - k)) := by
        rw [hm]; exact Mc_src s.m _ _ q (by omega) k k (Nat.le_refl _) (by omega)
      simp [run, step, h0, h1, e1, wr, rd, show pc + 2 * k + 1 + 1 = pc + 2 * (k + 1) by omega]
      simp [ea, upd, x8]
      constructor
      · omega
      · funext i; simp [Mc, upd, hm]
        rw [show ((s.x 8).toNat + (8 * (p : Int) + 16 - 8 * ((k : Int) + 1))).toNat = (s.x 8).toNat + 8 * p + 16 - 8 * (k + 1) by omega]
    · intro r hr5; simp [upd, hr5, hx r hr5]

end CallProbe

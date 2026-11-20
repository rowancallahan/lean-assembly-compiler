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
  /-- R-type ALU (Gen's BIN op numbering: add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8): rd := a op b -/
  | alu (op rd a b : Nat)
  | slli (rd rs sh : Nat)
  /-- byte load: the byte at address ea of the (aligned, little-endian) word cells of `m` -/
  | lbu (rd rs : Nat) (off : Int)
  /-- branches of IF (Gen: `beq t0, t1, +8` / `bltu t0, t1, +8`) -/
  | beq (a b : Nat) (off : Int)
  | bltu (a b : Nat) (off : Int)
  /-- start code only (g35): logical right shift, branch if not equal, byte store -/
  | srli (rd rs sh : Nat)
  | bne (a b : Nat) (off : Int)
  | sb (rs2 rs1 : Nat) (off : Int)

structure St where
  x : Nat → UInt64
  m : Nat → UInt64
  /-- the code base (byte address of instruction 0): return addresses are byte addresses `b + 4·pc` -/
  b : Nat
  /-- the target's extra instruction words per J instruction (RISC-V 0; AArch64 blocks of 4 words: 3); the link
  width `w = 4·(wk + 1)` (bytes of target code per J instruction) -/
  wk : Nat

/-- the link width: return addresses are `b + w·pc` -/
def St.w (s : St) : Nat := 4 * (s.wk + 1)

theorem St.w_pos (s : St) : 0 < s.w := by unfold St.w; omega

theorem St.w_eq {s t : St} (h : t.wk = s.wk) : t.w = s.w := by unfold St.w; rw [h]

/-- the link a `jal` at `pc` writes, read back by `jalr` -/
theorem link_div (s : St) (n : Nat) : (s.b + s.w * n - s.b) / s.w = n := by
  rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ s.w_pos]

def upd {α} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun i => if i = k then v else f i

def wr (s : St) (r : Nat) (v : UInt64) : St := if r = 0 then s else { s with x := upd s.x r v }
def ea (b : UInt64) (off : Int) : Nat := ((b.toNat : Int) + off).toNat

def aluf (op : Nat) (a b : UInt64) : UInt64 :=
  if op = 1 then a + b else if op = 2 then a - b else if op = 3 then a * b else if op = 4 then a &&& b
  else if op = 5 then a ||| b else if op = 6 then a <<< b else if op = 7 then a >>> b else a ^^^ b
def lbm (m : Nat → UInt64) (a : Nat) : UInt64 := (m (a - a % 8) >>> (8 * (a % 8)).toUInt64) &&& 255
/-- byte store: the low byte of v into byte a of the (aligned, little-endian) word cells -/
def sbm (m : Nat → UInt64) (a : Nat) (v : UInt64) : Nat → UInt64 :=
  fun c => if c = a - a % 8 then
    (m c &&& ~~~((255 : UInt64) <<< (8 * (a % 8)).toUInt64)) ||| ((v &&& 255) <<< (8 * (a % 8)).toUInt64)
    else m c

def step (C : List J) : Nat × St → Option (Nat × St)
  | (pc, s) => match C[pc]? with
    | some (.addi rd rs imm) => some (pc + 1, wr s rd (UInt64.ofNat (ea (s.x rs) imm)))
    | some (.ld rd rs off) => some (pc + 1, wr s rd (s.m (ea (s.x rs) off)))
    | some (.sd r2 r1 off) => some (pc + 1, { s with m := upd s.m (ea (s.x r1) off) (s.x r2) })
    | some (.jal rd off) => some (((pc : Int) + off).toNat, wr s rd (UInt64.ofNat (s.b + s.w * (pc + 1))))
    | some (.jalr rd rs) => some (((s.x rs).toNat - s.b) / s.w, wr s rd (UInt64.ofNat (s.b + s.w * (pc + 1))))
    | some (.bgeu a b off) => some (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + off).toNat else pc + 1, s)
    | some (.alu op rd a b) => some (pc + 1, wr s rd (aluf op (s.x a) (s.x b)))
    | some (.slli rd rs sh) => some (pc + 1, wr s rd (s.x rs <<< sh.toUInt64))
    | some (.lbu rd rs off) => some (pc + 1, wr s rd (lbm s.m (ea (s.x rs) off)))
    | some (.beq a b off) => some (if s.x a = s.x b then ((pc : Int) + off).toNat else pc + 1, s)
    | some (.bltu a b off) => some (if (s.x a).toNat < (s.x b).toNat then ((pc : Int) + off).toNat else pc + 1, s)
    | some (.srli rd rs sh) => some (pc + 1, wr s rd (s.x rs >>> sh.toUInt64))
    | some (.bne a b off) => some (if s.x a ≠ s.x b then ((pc : Int) + off).toNat else pc + 1, s)
    | some (.sb r2 r1 off) => some (pc + 1, { s with m := sbm s.m (ea (s.x r1) off) (s.x r2) })
    | none => none

inductive Star (C : List J) : Nat × St → Nat × St → Prop
  | refl (a) : Star C a a
  | tail {a b c} : Star C a b → step C b = some c → Star C a c

theorem Star.trans {C a b c} (h1 : Star C a b) (h2 : Star C b c) : Star C a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact .tail ih h

theorem Star.one {C a b} (h : step C a = some b) : Star C a b := .tail (.refl a) h

theorem wr_b (s : St) (r : Nat) (v : UInt64) : (wr s r v).b = s.b := by unfold wr; split <;> rfl

/-- steps never change the code base -/
theorem step_b {C : List J} {a c : Nat × St} (h : step C a = some c) : c.2.b = a.2.b := by
  obtain ⟨pc, s⟩ := a
  simp only [step] at h
  split at h <;> simp at h <;> (try split at h) <;> (try simp at h) <;> (try (obtain ⟨_, rfl⟩ := h)) <;> (try subst h) <;>
    simp [wr_b]

theorem Star.b {C : List J} {a c : Nat × St} (h : Star C a c) : c.2.b = a.2.b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [step_b hs, ih]

theorem wr_w (s : St) (r : Nat) (v : UInt64) : (wr s r v).wk = s.wk := by unfold wr; split <;> rfl

/-- steps never change the link width -/
theorem step_w {C : List J} {a c : Nat × St} (h : step C a = some c) : c.2.wk = a.2.wk := by
  obtain ⟨pc, s⟩ := a
  simp only [step] at h
  split at h <;> simp at h <;> (try split at h) <;> (try simp at h) <;> (try (obtain ⟨_, rfl⟩ := h)) <;> (try subst h) <;>
    simp [wr_w]

theorem Star.w {C : List J} {a c : Nat × St} (h : Star C a c) : c.2.wk = a.2.wk := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [step_w hs, ih]

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
    step C (pc, s) = some (((pc : Int) + off).toNat, wr s rd (UInt64.ofNat (s.b + s.w * (pc + 1)))) := by simp [step, h]
theorem s_slli {rd rs sh} (h : C[pc]? = some (.slli rd rs sh)) :
    step C (pc, s) = some (pc + 1, wr s rd (s.x rs <<< sh.toUInt64)) := by simp [step, h]
theorem s_bgeu_f {a b off} (h : C[pc]? = some (.bgeu a b off)) (hc : ¬ (s.x b).toNat ≤ (s.x a).toNat) :
    step C (pc, s) = some (pc + 1, s) := by simp [step, h, hc]
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
                                     upd s.m ((s.x 31).toNat - 8) (s.x r), s.b, s.wk⟩) := by
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
      s'.m = Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q k ∧ s'.b = s.b
  | 0, _ => ⟨s, by simp [run], fun _ _ => rfl, rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨s', hr, hx, hm, hb⟩ := copy_run s hq hD k (by omega)
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
    refine ⟨⟨upd s'.x 5 (s.m ((s.x 31).toNat + 8 * (q - 1 - k))), Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q (k + 1), s'.b, s'.wk⟩, ?_, ?_, rfl, hb⟩
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

theorem At.left {C pos l1 l2} (h : At C pos (l1 ++ l2)) : At C pos l1 := fun i hi => by
  have := h i (by simp; omega); rw [this, List.getElem?_append_left hi]
theorem At.right {C pos l1 l2} (h : At C pos (l1 ++ l2)) : At C (pos + l1.length) l2 := fun i hi => by
  have := h (l1.length + i) (by simp; omega); rw [Nat.add_assoc, this, List.getElem?_append_right (by omega)]; simp

/-! ## the prologue (`g38`): push ra, push s0, s0 := t6, t6 −= 8r (r = nslots − npw), checked -/
def pro (r : Nat) (oom : Int) : List J :=
  push 1 oom ++ (push 8 oom ++ [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 oom])

theorem copy_prefix (p q : Nat) : ∀ n k, k ≤ n → ∃ l, copy p q n = copy p q k ++ l
  | 0, k, h => ⟨[], by rw [show k = 0 by omega]; simp [copy]⟩
  | n + 1, k, h => by
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · obtain ⟨l, hl⟩ := copy_prefix p q n k (by omega); exact ⟨l ++ copyJ p q n, by simp [copy, hl]⟩
    · exact ⟨[], by rw [show k = n + 1 by omega]; simp⟩

theorem copy_at {C pc p q n k} (h : At C pc (copy p q n)) (hk : k ≤ n) : At C pc (copy p q k) := by
  obtain ⟨l, hl⟩ := copy_prefix p q n k hk; rw [hl] at h; exact h.left

/-! ## the epilogue (`g37` end + `g29`): a4 := [s0+8], a5 := [s0], copy, t6 := s0 + 8p + 16 − 8q, s0 := a5, jalr a4 -/
def epi (p q : Nat) : List J :=
  [.ld 14 8 8, .ld 15 8 0] ++ (copy p q q ++ [.addi 31 8 (8 * (p : Int) + 16 - 8 * (q : Int)), .addi 8 15 0, .jalr 0 14])

theorem epi_run {C e p q} (s : St) (hC : At C e (epi p q))
    (hD : (s.x 31).toNat + 8 * q ≤ (s.x 8).toNat + 8 * p + 16) (hlt : (s.x 8).toNat + 8 * p + 16 < 2 ^ 63) :
    ∃ s3, run C (2 + 2 * q + 3) (e, s) = some (((s.m ((s.x 8).toNat + 8)).toNat - s.b) / s.w, s3) ∧ s3.b = s.b ∧
      (s3.x 31).toNat = (s.x 8).toNat + 8 * p + 16 - 8 * q ∧ s3.x 8 = s.m (s.x 8).toNat ∧
      (∀ i, i ≠ 31 → i ≠ 8 → i ≠ 5 → i ≠ 14 → i ≠ 15 → s3.x i = s.x i) ∧
      s3.m = Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q q := by
  have a0 := hC.at 0 (by simp [epi]); have a1 := hC.at 1 (by simp [epi])
  simp [epi] at a0 a1
  have R : At C (e + 2) (copy p q q ++ [.addi 31 8 (8 * (p : Int) + 16 - 8 * (q : Int)), .addi 8 15 0, .jalr 0 14]) := by
    simpa [epi] using hC.right (l1 := [.ld 14 8 8, .ld 15 8 0])
  have T3 := R.right
  rw [copy_len] at T3
  have c0 := T3.at 0 (by simp); have c1 := T3.at 1 (by simp); have c2 := T3.at 2 (by simp)
  simp at c0 c1 c2
  have e8 : ea (s.x 8) 8 = (s.x 8).toNat + 8 := by simp [ea]; omega
  have e0 : ea (s.x 8) 0 = (s.x 8).toNat := by simp [ea]
  -- after the two loads
  let s' : St := ⟨upd (upd s.x 14 (s.m ((s.x 8).toNat + 8))) 15 (s.m (s.x 8).toNat), s.m, s.b, s.wk⟩
  have r2 : run C 2 (e, s) = some (e + 2, s') := by
    simp [run, step, a0, a1, wr, e8, e0, upd_other _ _ (show (8:Nat) ≠ 14 by decide), s']
  have x31 : s'.x 31 = s.x 31 := by simp [s', upd]
  have x8 : s'.x 8 = s.x 8 := by simp [s', upd]
  obtain ⟨s'', hr, hx, hm, hbb⟩ := copy_run (C := C) (pc := e + 2) (p := p) (q := q) s'
    (fun k hk => copy_at R.left hk) (by rw [x31, x8]; exact hD) q (Nat.le_refl _)
  have r22 : run C (2 + 2 * q) (e, s) = some (e + 2 + 2 * q, s'') := by rw [run_add r2]; exact hr
  have y8 : s''.x 8 = s.x 8 := by rw [hx 8 (by decide), x8]
  have y14 : s''.x 14 = s.m ((s.x 8).toNat + 8) := by rw [hx 14 (by decide)]; simp [s', upd]
  have y15 : s''.x 15 = s.m (s.x 8).toNat := by rw [hx 15 (by decide)]; simp [s', upd]
  have eA : ea (s.x 8) (8 * (p : Int) + 16 - 8 * (q : Int)) = (s.x 8).toNat + 8 * p + 16 - 8 * q := by
    simp only [ea]; omega
  have tA : (UInt64.ofNat ((s.x 8).toNat + 8 * p + 16 - 8 * q)).toNat = (s.x 8).toNat + 8 * p + 16 - 8 * q := by
    simp; omega
  have eB : ea (s.m (s.x 8).toNat) 0 = (s.m (s.x 8).toNat).toNat := by simp [ea]
  refine ⟨⟨upd (upd s''.x 31 (UInt64.ofNat ((s.x 8).toNat + 8 * p + 16 - 8 * q))) 8 (s.m (s.x 8).toNat), s''.m, s''.b, s''.wk⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have b2 : s''.b = s.b := hbb
    have w2 : s''.wk = s.wk := (run_star hr).w
    rw [show 2 + 2 * q + 3 = (2 + 2 * q) + 3 by omega, run_add r22]
    simp [run, step, c0, c1, c2, wr, y8, eA, upd_same, upd_other _ _ (show (15:Nat) ≠ 31 by decide),
      upd_other _ _ (show (14:Nat) ≠ 8 by decide), upd_other _ _ (show (14:Nat) ≠ 31 by decide), y14, y15, eB, b2, w2, St.w]
  · exact hbb
  · simp [upd, tA]
  · simp [upd_same]
  · intro i h1 h2 h3 h4 h5; simp [upd, h1, h2, hx i h3, s', h4, h5]
  · rw [hm, x31, x8]

theorem Mc_dest (m : Nat → UInt64) (T D q : Nat) (hD : 8 * q ≤ D) :
    ∀ k, k ≤ q → ∀ i, i < k → Mc m T D q k (D - 8 * (i + 1)) = m (T + 8 * (q - 1 - i))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, hk, i, hi => by
    simp only [Mc]
    rcases Nat.lt_or_ge i k with h | h
    · rw [upd_other _ _ (by omega)]; exact Mc_dest m T D q hD k (by omega) i h
    · rw [show i = k by omega, upd_same]

end CallProbe

/- Opus box E: the host lift (Sail `ImplementsCW` ↔ `SimW.RelW`).  `sim_ret`: the final `jalr x0, 0(ra)` as one Sail
step to any (even) ra — J's pc cannot name a return address below the code. -/
import Nano.V2Self.Proof.Main.Main
import Nano.V2Self.Proof.Machine.GenMain
import Nano.V2Self.Proof.Machine.SimX
namespace SimW
open Proven Nano.V2B

/-- **the return**: `jalr x0, 0(a)` at a related state retires to pc = the register's value; registers and memory kept -/
theorem sim_ret {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a : Nat} (ha : a < 32) (hC : K.W[pc]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat a) 0).toNat)
    (he : (s.x a).toNat % 2 = 0) :
    ∃ t' v, Next t t' (s.x a).toBitVec 0 v t.mem := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  have haN : (UInt64.ofNat a).toNat = a := by simp; omega
  rw [Bridge.g2_jalr _ (by omega), haN] at hi
  let A : Fin 32 := ⟨a, ha⟩
  have e : getX t A + (0 : BitVec 12).signExtend 64 = (s.x a).toBitVec := by
    rw [hR.x A]; simp [A]
  obtain ⟨t', hN⟩ := G.step_jalr hR.cfg hR.pc hok 0 A 0 (by simpa using hi) (by rw [e]; simpa using he)
  rw [e] at hN
  exact ⟨t', _, hN⟩

/-! ## the code bytes -/

/-- the 4 little-endian bytes Gen emits for a word -/
def le4 (v : UInt64) : List UInt8 := [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

theorem g40_bytes (c : List UInt8) (ws : List UInt64) (hl : ws.length < 2 ^ 64) :
    ∀ n i (o : List UInt8), ws.length ≤ i + n → i ≤ ws.length →
      C.g40 n c ws (UInt64.ofNat i) o = o ++ (ws.drop i).flatMap le4
  | 0, i, o, h1, h2 => by
    rw [List.drop_of_length_le (by omega)]; simp [C.g40]
  | n + 1, i, o, h1, h2 => by
    simp only [C.g40, bsize, bget]
    have hi : (UInt64.ofNat i).toNat = i := by simp; omega
    by_cases h : i < ws.length
    · have : UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      have e1 : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        apply UInt64.toNat_inj.1; simp; all_goals omega
      rw [if_pos this, e1, g40_bytes c ws hl n (i + 1) _ (by omega) (by omega), hi]
      simp [put, le4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.drop_eq_getElem_cons h, List.flatMap_cons]; rfl
    · have : ¬ UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      rw [if_neg this, List.drop_of_length_le (by omega)]; simp

theorem flat_le4 : ∀ (ws : List UInt64) (i k : Nat), i < ws.length → k < 4 →
    (ws.flatMap le4)[4 * i + k]? = (le4 ws[i]!)[k]?
  | [], i, k, h, _ => absurd h (by simp)
  | w :: ws, 0, k, _, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem?_append_left (by simp [le4]; omega)]; simp
  | w :: ws, i + 1, k, h, hk => by
    simp only [List.flatMap_cons]
    rw [List.getElem?_append_right (by simp [le4]; omega)]
    have := flat_le4 ws i k (by simp at h; omega) hk
    rw [show 4 * (i + 1) + k - (le4 w).length = 4 * i + k by simp [le4]; omega, this]; simp

theorem byte_le4 (v : UInt64) (k : Nat) (hk : k < 4) :
    ∃ b, (le4 v)[k]? = some b ∧ b.toBitVec = (BitVec.ofNat 32 v.toNat).extractLsb' (8 * k) 8 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    refine ⟨_, rfl, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp [le4, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, UInt64.toNat_shiftRight] <;> omega

theorem len_le4 (ws : List UInt64) : (ws.flatMap le4).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih]; simp [le4]; omega

/-- the code bytes at `e` give every word as an instruction -/
theorem code_at {t : Proven.St} {e : Nat} {ws : List UInt64}
    (he : e + 4 * ws.length < 2 ^ 64)
    (hb : bytesAt t e (ws.flatMap le4).length = (ws.flatMap le4).map (some ·.toBitVec)) :
    ∀ i (h : i < ws.length), instrAt t (BitVec.ofNat 64 (e + 4 * i)) (BitVec.ofNat 32 ws[i].toNat) := by
  intro i h
  have hlen := len_le4 ws
  have g : ∀ k, k < 4 → t.mem[e + 4 * i + k]? = some ((BitVec.ofNat 32 ws[i].toNat).extractLsb' (8 * k) 8) := by
    intro k hk
    have h1 := congrArg (·[4 * i + k]?) hb
    simp only [bytesAt, List.getElem?_map, List.getElem?_range (show 4 * i + k < (ws.flatMap le4).length by omega),
      Option.map_some] at h1
    rw [flat_le4 ws i k h hk] at h1
    obtain ⟨b, hb1, hb2⟩ := byte_le4 ws[i] k hk
    rw [getElem!_pos ws i h, hb1] at h1
    simp at h1; rw [Nat.add_assoc, h1, hb2]
  have hn : (BitVec.ofNat 64 (e + 4 * i)).toNat = e + 4 * i := by simp; omega
  unfold instrAt; rw [hn]
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)⟩

/-! ## the J state of a Sail state -/

/-- the byte at `a` (0 if absent) -/
def gb (t : Proven.St) (a : Nat) : BitVec 8 := (t.mem[a]?).getD 0

/-- the little-endian word at `a` -/
def wordAt (t : Proven.St) (a : Nat) : UInt64 :=
  UInt64.ofBitVec (gb t (a + 7) ++ gb t (a + 6) ++ gb t (a + 5) ++ gb t (a + 4) ++ gb t (a + 3) ++ gb t (a + 2) ++
    gb t (a + 1) ++ gb t a)

theorem wordAt_byte (t : Proven.St) (a k : Nat) (hk : k < 8) :
    (wordAt t a).toBitVec.extractLsb' (8 * k) 8 = gb t (a + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordAt, UInt64.toBitVec_ofBitVec, BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  repeat rw [Nano.V2B.or8 _ _ (BitVec.isLt _)]
  have h0 := (gb t a).isLt; have h1 := (gb t (a + 1)).isLt; have h2 := (gb t (a + 2)).isLt
  have h3 := (gb t (a + 3)).isLt; have h4 := (gb t (a + 4)).isLt; have h5 := (gb t (a + 5)).isLt
  have h6 := (gb t (a + 6)).isLt; have h7 := (gb t (a + 7)).isLt
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

/-- J's view of a Sail state: registers, little-endian words, code base `b` -/
def jOf (t : Proven.St) (b : Nat) : CallProbe.St :=
  ⟨fun j => if h : j < 32 then UInt64.ofBitVec (getX t ⟨j, h⟩) else 0, wordAt t, b⟩

theorem gb_some {t : Proven.St} {a : Nat} (h : (t.mem[a]?).isSome) : t.mem[a]? = some (gb t a) := by
  unfold gb; cases e : t.mem[a]? with
  | none => rw [e] at h; simp at h
  | some v => rfl

/-- **the start**: a Sail state with the code words at `base`, pc = base, the work cells and the input/output bytes
present, and `m0` = its memory, is related to its J view at pc 0 -/
theorem rel_init {K : LayW} {t : Proven.St} (hc : Cfg t) (hpc : t.regs.get? .PC = some (BitVec.ofNat 64 K.base))
    (hcode : ∀ i (h : i < K.W.length), instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 K.W[i]))
    (hw : ∀ a, wok K a → ∀ k < 8, (t.mem[a + k]?).isSome) (hio : ∀ a, io K a → (t.mem[a]?).isSome)
    (hm0 : K.m0 = fun a => t.mem[a]?) :
    RelW K (0, jOf t K.base) t where
  cfg := hc
  pc := by simpa using hpc
  code := hcode
  x0 := by simp [jOf, getX, xval]
  bb := rfl
  x := fun j => by simp [jOf, j.isLt]
  w := fun a ha k hk => by
    rw [gb_some (hw a ha k hk)]; simp only [jOf]; rw [wordAt_byte t a k hk]
  bw := fun c hc => by
    rw [gb_some (hio c hc)]; simp only [jOf]
    rw [wordAt_byte t _ _ (Nat.mod_lt _ (by decide)), show c - c % 8 + c % 8 = c by omega]
  fr := fun a _ _ => by rw [hm0]

/-! ## the end: the final `jalr x0, 0(ra)` and the spec's outcome -/

theorem byte_lbm (w : UInt64) (k : Nat) (hk : k < 8) (y : UInt8) (h : (w >>> (8 * k).toUInt64) &&& 255 = y.toUInt64) :
    w.toBitVec.extractLsb' (8 * k) 8 = y.toBitVec := by
  have h2 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt8.toNat_toUInt64] at h2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, UInt8.toNat_toBitVec, ← h2]
  have e : (8 * k).toUInt64.toNat % 64 = 8 * k := by simp; omega
  rw [e, Nat.shiftRight_eq_div_pow, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; rfl

/-- **the outcome**: from J's state at the final `jalr x0, 0(ra)` (ABI registers as at the start, the result
bytes `y` at the output), one Sail step reaches ra with the spec's facts -/
theorem fin_out {K : LayW} {pr : Nat} {s0 s3 : CallProbe.St} {t0 t3 : Proven.St} (hK : K.Ok) (hR : RelW K (pr, s3) t3)
    (hC : K.W[pr]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat 1) 0).toNat) (hra : (s3.x 1).toNat % 2 = 0)
    (hc0 : Cfg t0) (hx0 : ∀ j : Fin 32, getX t0 j = (s0.x j).toBitVec)
    (hkeep : ∀ j, Templates.keepR j = true → s3.x j = s0.x j) (hx8 : s3.x 8 = s0.x 8)
    (hm0 : K.m0 = fun a => t0.mem[a]?) (work : Region) (hlo : work.base ≤ K.lo) (hhi : K.hi ≤ work.base + work.len)
    (y : List UInt8) (hol : K.ol = y.length)
    (hy : ∀ i, i < y.length → CallProbe.lbm s3.m (K.ob + i) = (y.getD i 0).toUInt64) :
    ∃ t4, Retires t3 t4 ∧ t4.regs.get? .PC = some (s3.x 1).toBitVec ∧ abiSavedKept t0 t4 ∧ Cfg t4 ∧
      t4.regs.get? .x10 = some (s3.x 10).toBitVec ∧ t4.regs.get? .x11 = some (s3.x 11).toBitVec ∧
      bytesAt t4 K.ob y.length = y.map (some ·.toBitVec) ∧ unchangedOutside t0 t4 [⟨K.ob, y.length⟩, work] := by
  obtain ⟨t4, v, hN⟩ := sim_ret hK hR (by omega) hC hra
  have gx : ∀ j : Fin 32, getX t4 j = getX t3 j := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]
  have kx : ∀ j : Fin 32, Templates.keepR j.val = true ∨ j.val = 8 → getX t4 j = getX t0 j := fun j hj => by
    rw [gx, hR.x, hx0]; rcases hj with hj | hj
    · rw [hkeep _ hj]
    · simp only [hj]; rw [hx8]
  refine ⟨t4, hN.ret, hN.pc, ?_, hN.cfg, by rw [hN.cfg.x10, gx, hR.x]; rfl, by rw [hN.cfg.x11, gx, hR.x]; rfl, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hN.cfg.x2, hc0.x2, kx 2 (by decide)]
    · rw [hN.cfg.x3, hc0.x3, kx 3 (by decide)]
    · rw [hN.cfg.x4, hc0.x4, kx 4 (by decide)]
    · rw [hN.cfg.x8, hc0.x8, kx 8 (by decide)]
    · rw [hN.cfg.x9, hc0.x9, kx 9 (by decide)]
    · rw [hN.cfg.x18, hc0.x18, kx 18 (by decide)]
    · rw [hN.cfg.x19, hc0.x19, kx 19 (by decide)]
    · rw [hN.cfg.x20, hc0.x20, kx 20 (by decide)]
    · rw [hN.cfg.x21, hc0.x21, kx 21 (by decide)]
    · rw [hN.cfg.x22, hc0.x22, kx 22 (by decide)]
    · rw [hN.cfg.x23, hc0.x23, kx 23 (by decide)]
    · rw [hN.cfg.x24, hc0.x24, kx 24 (by decide)]
    · rw [hN.cfg.x25, hc0.x25, kx 25 (by decide)]
    · rw [hN.cfg.x26, hc0.x26, kx 26 (by decide)]
    · rw [hN.cfg.x27, hc0.x27, kx 27 (by decide)]
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h1 h2
    have hi : i < y.length := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, hN.mem]
    have hio : io K (K.ob + i) := Or.inr ⟨by omega, by omega⟩
    rw [hR.bw _ hio]
    congr 1
    have := hy i hi
    unfold CallProbe.lbm at this
    rw [byte_lbm _ _ (Nat.mod_lt _ (by decide)) _ this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
    rw [hN.mem]
    have h1 : ¬ wok K (a - a % 8) := fun hw => by unfold wok at hw; omega
    have h2 : ¬ outB K a := fun ho => by unfold outB at ho; omega
    rw [hR.fr a h1 h2, hm0]

end SimW

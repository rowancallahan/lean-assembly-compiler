/- Machine bridge (Opus box E): Sail sims of the start code's extra instructions (srli, beq +28, bne +16, sb), in the
form of SimW's sims (a J step on a matching word is one retired Sail instruction keeping `RelW`).  Wiring them into
`SimW.Safe` / `encJ` / `sim_stepW` is a shared edit (A's Safe retrofit), proposed separately. -/
import Nano.V2Self.Proof.Machine.SimW
namespace SimW
open Proven Nano.V2B

/-- **srli rd, a, sh** -/
theorem sim_srliW {K : LayRv} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a sh : Nat} (hC : K.W[pc]? = some (I.i .srli rd a (sh : Int)).enc) (hrd : rd < 32) (ha : a < 32) (hsh : sh < 64) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a >>> sh.toUInt64)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have hn : (sh : Int).toNat < 64 := by simpa using hsh
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat) RD A) := by
    rw [show 0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat = bits (sh : Int) 12 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; unfold bits; simp; omega]; exact hi
  obtain ⟨t', hN⟩ := G.step_srli hR.cfg hR.pc hok RD A _ hi'
  rw [xa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, ← shrK_bv _ _ hn] at hN
  exact ⟨t', hN.ret, by simpa using rel_regW hR RD _ hN⟩

set_option maxRecDepth 100000 in
theorem encBt28_eq (f3 : Nat) (hf : f3 < 8) (rs1 rs2 : Fin 32) :
    BitVec.ofNat 32 (encBt f3 rs1.val rs2.val 28) = wB (BitVec.ofNat 3 f3) (.ofFin rs1) (.ofFin rs2) 14#12 := by
  unfold encBt; rw [show bits (28 : Int) 13 = 28 from rfl]; encbits

theorem boff28 : boff (14#12) = 28#64 := by decide
theorem pc_plus28 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 28#64 = BitVec.ofNat 64 (b + 4 * (pc + 7)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- **beq a, b, +28** (the start code's copy-loop exit) -/
theorem sim_beq28 {K : LayRv} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .beq a b 28).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if s.x a = s.x b then ((pc : Int) + 7).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt28_eq 0 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 0 A.val B.val 28)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : s.x a = s.x b
  · obtain ⟨t', hN⟩ := G.beq_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
    rw [boff28, pc_plus28] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 7).toNat = pc + 7 by omega]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.beq_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg hc]; exact ⟨t', hN.ret, this⟩

/-- **bne a, b, +16** (the start code's empty-buffer check) -/
theorem sim_bne16 {K : LayRv} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bne a b 16).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if s.x a ≠ s.x b then ((pc : Int) + 4).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt16_eq 1 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 1 A.val B.val 16)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : s.x a = s.x b
  · obtain ⟨t', hN⟩ := G.bne_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg (by simpa using hc)]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bne_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
    rw [boff16, pc_plus16] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 4).toNat = pc + 4 by omega]; exact ⟨t', hN.ret, this⟩

theorem _root_.CallProbe.sbm_other' (m : Nat → UInt64) (a c : Nat) (v : UInt64) (h : c ≠ a - a % 8) :
    CallProbe.sbm m a v c = m c := by unfold CallProbe.sbm; rw [if_neg h]

theorem g255' (j : Nat) : (255#64).getLsbD j = decide (j < 8) := by
  rw [BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 8 <;> simp [h] <;> omega

theorem g255e (i : Nat) (h : i < 64) : (255#64)[i] = decide (i < 8) := by
  rw [← BitVec.getLsbD_eq_getElem]; exact g255' i

/-- byte j of the word after a byte store at byte k -/
theorem sbm_extract (x v : UInt64) (k j : Nat) (hk : k < 8) (hj : j < 8) :
    ((x &&& ~~~((255 : UInt64) <<< (8 * k).toUInt64)) ||| ((v &&& 255) <<< (8 * k).toUInt64)).toBitVec.extractLsb' (8 * j) 8
      = if j = k then v.toBitVec.setWidth 8 else x.toBitVec.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : 8 * k % 64 = 8 * k := by omega
  by_cases hjk : j = k
  · subst hjk
    simp [BitVec.getLsbD_shiftLeft, g255', e, hi, show 8 * j + i < 64 by omega, g255e,
      BitVec.getLsbD_eq_getElem, show i < 64 by omega, show ¬ 8 * j + i < 8 * j by omega]
  · simp only [if_neg hjk]
    simp [BitVec.getLsbD_shiftLeft, g255', e, hi, show 8 * j + i < 64 by omega]
    by_cases h2 : 8 * j + i < 8 * k
    · simp [h2]
    · rw [g255e _ (by omega)]; simp [show ¬ 8 * j + i - 8 * k < 8 by omega]

/-- **sb b, off(a)** (the start code's output copy): the byte lands in its aligned word cell (`sbm`) -/
theorem sim_sbW {K : LayRv} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {b a : Nat} {off : Int} (hC : K.W[pc]? = some (I.sb b a off).enc) (hb : b < 32) (ha : a < 32)
    (hi1 : -2048 ≤ off) (hi2 : off < 2048) (h0 : 0 ≤ ((s.x a).toNat : Int) + off)
    (hw : sok K (CallProbe.ea (s.x a) off)) :
    ∃ t', Retires t t' ∧
      RelW K (pc + 1, { s with m := CallProbe.sbm s.m (CallProbe.ea (s.x a) off) (s.x b) }) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let B : Fin 32 := ⟨b, hb⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hW := hK.wlo; have hH := hK.whi
  generalize hE : CallProbe.ea (s.x a) off = E at *
  have hk8 : E % 8 < 8 := Nat.mod_lt _ (by decide)
  have := hK.obh; have := hK.obl; have hoc := hK.oc
  have hrng : 0x80000000 ≤ E ∧ E + 1 ≤ 0x100000000 ∧ (E + 1 ≤ K.base ∨ K.base + 4 * K.W.length ≤ E) := by
    have hd := hK.cw
    rcases hw with hw | hw <;> simp only [wok, outB] at hw <;> omega
  have hlt : E < 2 ^ 64 := by omega
  have hea := eaW hR A off hi1 hi2 h0 (by show ((s.x a).toNat : Int) + off < 2 ^ 64; unfold CallProbe.ea at hE; omega)
  rw [hE] at hea
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encS 0 (BitVec.ofNat 12 (bits off 12)) B A) := by
    have e := encSt_eq 0 (by decide) B A (bits off 12) (bits_lt off 12)
    have hi2 : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc))
        (BitVec.ofNat 32 (encSt 0 B.val A.val ((bits off 12 : Nat) : Int))) := by rw [← encSt_bits]; exact hi
    rw [e] at hi2; exact hi2
  obtain ⟨t', hN⟩ := G.step_sb hR.cfg hR.pc hok B A _ hi' hea (by rw [toNat_lt64 hlt]; omega)
  rw [toNat_lt64 hlt, hR.x B] at hN
  refine ⟨t', hN.ret, ?_⟩
  exact {
    cfg := hN.cfg
    pc := by rw [hN.pc, ofNat_pc4]
    code := fun i h => by
      have hc := hR.code i h
      have hl : K.base + 4 * i < 2 ^ 64 := by have := hK.bhi; omega
      unfold instrAt at hc ⊢; rw [hN.mem]; rw [toNat_lt64 hl] at hc ⊢
      have hd := hK.cw
      obtain ⟨c0, c1, c2, c3⟩ := hc
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)]; assumption)
    x0 := hR.x0
    bb := hR.bb
    ww := hR.ww
    x := fun j => by
      rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact hR.x j
    w := fun c hc k hk => by
      rw [hN.mem, Std.ExtHashMap.getElem?_insert]
      unfold wok at hc
      by_cases ec : c = E - E % 8
      · subst ec
        have hs : CallProbe.sbm s.m E (s.x b) (E - E % 8) = _ := if_pos rfl
        simp only; rw [hs, sbm_extract _ _ _ _ hk8 hk]
        by_cases ek : k = E % 8
        · subst ek; rw [if_pos (by simp; omega), if_pos rfl]
        · rw [if_neg (by simp; omega), if_neg ek]; exact hR.w _ hc k hk
      · rw [if_neg (by simp; omega)]
        simp only; rw [CallProbe.sbm_other' s.m E c (s.x b) ec]; exact hR.w c hc k hk
    bw := fun c hc => by
      rw [hN.mem, Std.ExtHashMap.getElem?_insert]
      have hc8 : c % 8 < 8 := Nat.mod_lt _ (by decide)
      by_cases ec : c - c % 8 = E - E % 8
      · have hs : CallProbe.sbm s.m E (s.x b) (c - c % 8) = _ := if_pos ec
        simp only; rw [hs, sbm_extract _ _ _ _ hk8 hc8]
        by_cases ek : c = E
        · subst ek; rw [if_pos (by simp), if_pos rfl]
        · rw [if_neg (by simp; omega), if_neg (by omega)]
          exact hR.bw c hc
      · rw [if_neg (by simp; omega)]
        simp only; rw [CallProbe.sbm_other' s.m E _ (s.x b) ec]; exact hR.bw c hc
    fr := fun c h1 h2 => by
      rw [hN.mem, Std.ExtHashMap.getElem?_insert]
      have ne : c ≠ E := by
        rintro rfl; rcases hw with hw | hw
        · exact h1 hw
        · exact h2 hw
      rw [if_neg (by simp; omega)]; exact hR.fr c h1 h2 }

/-! ## SimW's `encJ` words of the new instructions are the `I.enc` words the sims take -/

/-! ## the start code's Safe layer: `encJX` (beq offsets in instructions, like bgeu), `SafeX` (Safe plus beq +7,
srli, bne +4, sb), `sim_stepX` / `SStarX`, and `SStar → SStarX` (A's template twins carry over) -/

/-- **one step**: a safe J step on matching words is one retired Sail instruction, keeping `RelW` -/
theorem sim_stepX {K : LayRv} {C : List CallProbe.J} (hK : K.Ok) (hW : K.W = C.map encJX)
    {a b : Nat × CallProbe.St} {t : Proven.St} (hR : RelW K a t) (hS : SafeX K C a) (hs : CallProbe.step C a = some b) :
    ∃ t', Retires t t' ∧ RelW K b t' := by
  obtain ⟨pc, s⟩ := a
  have hWpc : ∀ i, C[pc]? = some i → K.W[pc]? = some (encJX i) := by intro i h; rw [hW]; simp [h]
  simp only [SafeX] at hS
  simp only [CallProbe.step] at hs
  cases hc : C[pc]? with
  | none => rw [hc] at hS; exact hS.elim
  | some i =>
    rw [hc] at hS hs
    cases i with
    | addi rd rs imm =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_addi hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | ld rd rs off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_ld hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | sd b' a' off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_sd hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | bgeu a' b' o =>
      obtain ⟨h1, h2, ho⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs
      rcases ho with rfl | rfl | rfl
      · exact sim_bgeu8 hK hR (hWpc _ hc) h1 h2
      · exact sim_bgeu12 hK hR (hWpc _ hc) h1 h2
      · exact sim_bgeu16 hK hR (hWpc _ hc) h1 h2
    | jal rd off =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS
      have hl : C.length = K.W.length := by rw [hW]; simp
      simp only [Option.some.injEq] at hs; subst hs; exact sim_jal hK hR h1 (hWpc _ hc) h2 h3 h4 (by rw [← hl]; exact h5)
    | jalr rd rs =>
      obtain ⟨rfl, h2, j, hj⟩ := hS
      have hb : s.b = K.base := hR.bb
      simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨t', ht, hr⟩ := sim_jalr hK hR h2 (hWpc _ hc) (by rw [hj, hR.w4])
      refine ⟨t', ht, ?_⟩
      have : ((s.x rs).toNat - s.b) / s.w = j := by rw [hj, hb, hR.w4]; omega
      simp [this, CallProbe.wr]; exact hr
    | beq a' b' o =>
      obtain ⟨h1, h2, ho⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs
      rcases ho with rfl | rfl
      · exact sim_beq8 hK hR (hWpc _ hc) h1 h2
      · exact sim_beq28 hK hR (hWpc _ hc) h1 h2
    | bltu a' b' o =>
      obtain ⟨h1, h2, rfl⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_bltu8 hK hR (hWpc _ hc) h1 h2
    | alu op rd a' b' =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_aluW hK hR (hWpc _ hc) h1 h2 h3 h4 h5
    | slli rd rs sh =>
      obtain ⟨h1, h2, h3⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_slliW hK hR (hWpc _ hc) h1 h2 h3
    | lbu rd rs off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_lbuW hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | srli rd rs sh =>
      obtain ⟨h1, h2, h3⟩ := hS
      have hw := hWpc _ hc; simp only [encJX] at hw; rw [encJ_srli _ _ _ h1 h2 h3] at hw
      simp only [Option.some.injEq] at hs; subst hs; exact sim_srliW hK hR hw h1 h2 h3
    | bne a' b' o =>
      obtain ⟨h1, h2, rfl⟩ := hS
      have hw := hWpc _ hc; simp only [encJX] at hw; rw [encJ_bne _ _ h1 h2] at hw
      simp only [Option.some.injEq] at hs; subst hs; exact sim_bne16 hK hR hw h1 h2
    | sb b' a' off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      have hw := hWpc _ hc; simp only [encJX] at hw; rw [encJ_sb _ _ _ h1 h2 h3 h4] at hw
      simp only [Option.some.injEq] at hs; subst hs; exact sim_sbW hK hR hw h1 h2 h3 h4 h5 h6


end SimW

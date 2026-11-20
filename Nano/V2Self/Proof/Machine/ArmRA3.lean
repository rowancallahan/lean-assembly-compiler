/- rv2arm as a Lean function on bytes (`rv2arm`: the `rv2arm.sh` chunk loop around `RA.m`) and its correctness on
Gen's words (`rv2arm_ok`): reading words back (`w_eq`), the validation loop (`c1_all`), the emission loop (`l0_eq`),
one chunk (`m_eq`), the chunks concatenated (`chunks`). -/
import Nano.V2Self.Proof.Machine.ArmRA2
set_option linter.unusedSimpArgs false
namespace ArmRA
open CallProbe ArmEnc SimW

theorem orB {a b : Nat} (k : Nat) (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) : a ||| b = a + b := by
  rw [Nat.or_comm, orA k hb ha, Nat.add_comm]

/-- `orsum` for sums built from the low end -/
macro "rsum" : tactic => `(tactic| simp (disch := omega) only [orB 8, orB 16, orB 24])

theorem le4_len (v : UInt64) : (le4 v).length = 4 := rfl

theorem getD_flat4 : ∀ (ws : List UInt64) (i k : Nat), i < ws.length → k < 4 →
    (ws.flatMap le4).getD (4 * i + k) 0 = (le4 ws[i]!).getD k 0
  | [], _, _, h, _ => by simp at h
  | w :: ws, 0, k, _, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [le4_len]; exact hk)]; simp [List.getD_eq_getElem?_getD]
  | w :: ws, i + 1, k, h, hk => by
    simp only [List.flatMap_cons]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [le4_len]; omega), le4_len,
      show 4 * (i + 1) + k - 4 = 4 * i + k by omega, ← List.getD_eq_getElem?_getD,
      getD_flat4 ws i k (by simp at h; omega) hk]
    simp

/-- the word `v < 2^32` read back from its 4 bytes -/
theorem word_back (v : UInt64) (hv : v.toNat < 2 ^ 32) :
    ((le4 v).getD 0 0).toUInt64 ||| (((le4 v).getD 1 0).toUInt64 <<< 8) ||| (((le4 v).getD 2 0).toUInt64 <<< 16) |||
      (((le4 v).getD 3 0).toUInt64 <<< 24) = v := by
  apply u64; simp only [le4, List.getD_cons_zero, List.getD_cons_succ]
  wnorm
  simp only [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  simp only [show UInt64.toNat 8 = 8 from rfl, show UInt64.toNat 16 = 16 from rfl, show UInt64.toNat 24 = 24 from rfl,
    Nat.reduceMod, Nat.reducePow]
  rsum; omega

theorem w_eq (hdr : List UInt8) (hh : hdr.length = 4) (ws : List UInt64) (i : Nat) (hi : i < ws.length)
    (hl : ws.length < 2 ^ 60) (hv : ws[i].toNat < 2 ^ 32) : RA.w (hdr ++ ws.flatMap le4) i.toUInt64 = ws[i] := by
  have e : ∀ (c : UInt64) k, c.toNat = 4 + k → k < 4 →
      _root_.rd (hdr ++ ws.flatMap le4) (4 * i.toUInt64 + c) = ((le4 ws[i]).getD k 0).toUInt64 := by
    intro c k hc hk
    unfold _root_.rd
    have : (4 * i.toUInt64 + c).toNat = 4 + (4 * i + k) := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, tU (by omega), hc]; simp; omega
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hh, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD, getD_flat4 ws i k hi hk]
    simp [hi]
  unfold RA.w
  rw [e 4 0 rfl (by omega), e 5 1 rfl (by omega), e 6 2 rfl (by omega), e 7 3 rfl (by omega)]
  exact word_back _ hv

theorem encG_lt (j : J) (hj : GoodX j) : (encG j).toNat < 2 ^ 32 := by
  cases j with
  | addi rd rs imm => obtain ⟨h1, h2, h3, h4⟩ := hj; rw [addi_V rd rs imm h1 h2 h3 h4]; omega
  | ld rd rs f =>
    obtain ⟨h1, h2, h3, h4⟩ := hj
    have := I_V 3 3 rd rs f (by omega) (by omega) h1 h2
    simp only [encG, C.g11, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl]
    omega
  | lbu rd rs f =>
    obtain ⟨h1, h2, h3, h4⟩ := hj
    have := I_V 3 4 rd rs f (by omega) (by omega) h1 h2
    simp only [encG, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl]
    omega
  | sd r2 r1 f =>
    obtain ⟨h1, h2, h3, h4⟩ := hj
    have := S_V 3 r2 r1 f (by omega) h1 h2
    simp only [encG, C.g12, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl]
    omega
  | sb r2 r1 f =>
    obtain ⟨h1, h2, h3, h4⟩ := hj
    have := S_V 0 r2 r1 f (by omega) h1 h2
    simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]
    omega
  | alu op rd a b =>
    obtain ⟨hd, ha, hb, ho1, ho2⟩ := hj
    obtain ⟨-, -, -, -, f5, f6, -⟩ := alu_facts op ho1 ho2
    have := g1_sum (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64 f5 f6 (by rw [tU (by omega)]; omega)
      (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
    rw [tU (by omega), tU (by omega), tU (by omega)] at this
    simp only [encG]; omega
  | slli rd rs sh =>
    obtain ⟨h1, h2, h3⟩ := hj
    have := sh_V 1 rd rs sh (by omega) h1 h2 h3
    simp only [encG, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl]; omega
  | srli rd rs sh =>
    obtain ⟨h1, h2, h3⟩ := hj
    have := sh_V 5 rd rs sh (by omega) h1 h2 h3
    simp only [encG, show (5 : UInt64) = (5 : Nat).toUInt64 from rfl]; omega
  | beq a b o =>
    obtain ⟨h1, h2, -⟩ := hj
    have := B_V 0 a b o (by omega) h1 h2
    simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]; omega
  | bne a b o =>
    obtain ⟨h1, h2, -⟩ := hj
    have := B_V 1 a b o (by omega) h1 h2
    simp only [encG, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl]; omega
  | bltu a b o =>
    obtain ⟨h1, h2, -⟩ := hj
    have := B_V 6 a b o (by omega) h1 h2
    simp only [encG, show (6 : UInt64) = (6 : Nat).toUInt64 from rfl]; omega
  | bgeu a b o =>
    obtain ⟨h1, h2, -⟩ := hj
    have := B_V 7 a b o (by omega) h1 h2
    simp only [encG, show (7 : UInt64) = (7 : Nat).toUInt64 from rfl]; omega
  | jal rd o =>
    have hd : rd < 32 := hj
    have := jal_V rd o hd
    simp only [encG]; omega
  | jalr rd rs =>
    obtain ⟨h1, h2⟩ := hj
    have := g2_sum C.g_103 0 rd.toUInt64 rs.toUInt64 0 (by decide) (by decide) (by rw [tU (by omega)]; omega)
      (by rw [tU (by omega)]; omega)
    rw [tU (by omega), tU (by omega), show C.g_103.toNat = 103 from rfl, show (0 : UInt64).toNat = 0 from rfl] at this
    simp only [encG]; omega

theorem ltU {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (a.toUInt64 < b.toUInt64) = (a < b) := by
  apply propext; rw [UInt64.lt_iff_toNat_lt, tU ha, tU hb]
theorem succU {a : Nat} (ha : a + 1 < 2 ^ 64) : a.toUInt64 + 1 = (a + 1).toUInt64 :=
  u64 (by rw [UInt64.toNat_add, tU (by omega), tU ha]; simp; omega)

theorem c1_all (x : List UInt8) (n : Nat) (hn : n < 2 ^ 63) : ∀ fuel i, i ≤ n → n ≤ i + fuel →
    (RA.c1 fuel x i.toUInt64 n.toUInt64 = 1 ↔
      ∀ k, i ≤ k → k < n → RA.c0 (RA.w x k.toUInt64) k.toUInt64 n.toUInt64 = 1)
  | 0, i, _, h => by simp only [RA.c1, true_iff]; intro k h1 h2; omega
  | fuel + 1, i, h0, h => by
    simp only [RA.c1]
    by_cases hi : i < n
    · rw [if_pos (by rw [ltU (by omega) (by omega)]; exact hi), succU (by omega)]
      by_cases hc : RA.c0 (RA.w x i.toUInt64) i.toUInt64 n.toUInt64 = 1
      · rw [if_pos (by rw [hc]; rfl), c1_all x n hn fuel (i + 1) (by omega) (by omega)]
        constructor
        · intro H k h1 h2; by_cases e : k = i
          · subst e; exact hc
          · exact H k (by omega) h2
        · intro H k h1 h2; exact H k (by omega) h2
      · rw [if_neg (by intro e; exact hc (beq_iff_eq.1 e))]
        constructor
        · intro e; exact absurd e (by decide)
        · intro H; exact absurd (H i (Nat.le_refl _) hi) hc
    · rw [if_neg (by rw [ltU (by omega) (by omega)]; exact hi)]
      simp only [true_iff]; intro k h1 h2; omega

theorem l0_eq (x : List UInt8) (n : UInt64) (e : Nat) (he : e < 2 ^ 63) (F : Nat → List UInt8) :
    ∀ fuel i (o : List UInt8), i ≤ e → e ≤ i + fuel →
    (∀ k, i ≤ k → k < e → ∀ o', RA.t0 x o' (RA.w x k.toUInt64) = o' ++ F k) →
    RA.l0 fuel x i.toUInt64 e.toUInt64 n o = o ++ (List.range' i (e - i)).flatMap F
  | 0, i, o, _, h, _ => by
    simp only [RA.l0]; rw [show e - i = 0 by omega]; simp
  | fuel + 1, i, o, h0, h, H => by
    simp only [RA.l0]
    by_cases hi : i < e
    · rw [if_pos (by rw [ltU (by omega) (by omega)]; exact hi), succU (by omega), H i (Nat.le_refl _) hi,
        l0_eq x n e he F fuel (i + 1) _ (by omega) (by omega) (fun k h1 h2 => H k (by omega) h2)]
      rw [show e - i = (e - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons, List.append_assoc]
    · rw [if_neg (by rw [ltU (by omega) (by omega)]; exact hi), show e - i = 0 by omega]; simp

theorem flat_len (ws : List UInt64) : (ws.flatMap le4).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih, le4_len, List.length_cons]; omega

/-- the bytes of J instruction `j`'s block -/
def bytesJ (j : J) : List UInt8 := (blockJ j).flatMap fun W => le4 W.toUInt64

/-- chunk `c` of rv2arm on Gen's words `ws` (the header `le4 c`, then the code) -/
theorem m_eq (c : Nat) (hc : c < 2 ^ 18) (ws : List UInt64) (hn : ws.length < 2 ^ 18)
    (hw : ∀ k (h : k < ws.length), ws[k].toNat < 2 ^ 32) (F : Nat → List UInt8)
    (hcn : c * 32000 ≤ ws.length)
    (hF : ∀ k (h : k < ws.length), RA.c0 ws[k] k.toUInt64 ws.length.toUInt64 = 1 →
      ∀ o, RA.t0 (le4 c.toUInt64 ++ ws.flatMap le4) o ws[k] = o ++ F k) :
    RA.m (le4 c.toUInt64 ++ ws.flatMap le4) =
      if ∀ k (h : k < ws.length), RA.c0 ws[k] k.toUInt64 ws.length.toUInt64 = 1 then
        (List.range' (c * 32000) (min ((c + 1) * 32000) ws.length - c * 32000)).flatMap F
      else [] := by
  generalize hx : le4 c.toUInt64 ++ ws.flatMap le4 = x
  have hxl : x.length = 4 + 4 * ws.length := by rw [← hx, List.length_append, flat_len]; rfl
  have hwx : ∀ k (h : k < ws.length), RA.w x k.toUInt64 = ws[k] := fun k h => by
    rw [← hx]; exact w_eq _ rfl ws k h (by omega) (hw k h)
  have hlen : len x = (4 + 4 * ws.length).toUInt64 := by unfold len; rw [hxl]
  have hhd : (_root_.rd x 0 ||| (_root_.rd x 1 <<< 8) ||| (_root_.rd x 2 <<< 16) ||| (_root_.rd x 3 <<< 24)) = c.toUInt64 := by
    have hb : ∀ (u : UInt64) k, u.toNat = k → k < 4 → _root_.rd x u = ((le4 c.toUInt64).getD k 0).toUInt64 := by
      intro u k hu hk; unfold _root_.rd; rw [hu, ← hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [le4_len]; exact hk)]
    rw [hb 0 0 rfl (by omega), hb 1 1 rfl (by omega), hb 2 2 rfl (by omega), hb 3 3 rfl (by omega)]
    exact word_back c.toUInt64 (by rw [tU (by omega)]; omega)
  unfold RA.m RA.l1
  rw [hlen, hhd, if_neg (by rw [UInt64.lt_iff_toNat_lt, tU (by omega)]; simp),
    if_pos (by apply beq_iff_eq.2; apply u64; wnorm; omega),
    show ((4 + 4 * ws.length).toUInt64 - 4) >>> 2 = ws.length.toUInt64 from
      u64 (by wnorm; rw [UInt64.toNat_sub, UInt64.toNat_ofNat']; simp; omega)]
  simp only []
  have hs : c.toUInt64 * RA.z0 = (c * 32000).toUInt64 :=
    u64 (by rw [UInt64.toNat_mul, tU (by omega), tU (by omega)]; simp [RA.z0]; omega)
  have he : (if (c * 32000).toUInt64 + RA.z0 < ws.length.toUInt64 then (c * 32000).toUInt64 + RA.z0
      else ws.length.toUInt64) = (min ((c + 1) * 32000) ws.length).toUInt64 := by
    have e1 : (c * 32000).toUInt64 + RA.z0 = ((c + 1) * 32000).toUInt64 :=
      u64 (by rw [UInt64.toNat_add, tU (by omega), tU (by omega)]; simp [RA.z0]; omega)
    rw [e1]; simp only [ltU (show (c + 1) * 32000 < 2 ^ 64 by omega) (show ws.length < 2 ^ 64 by omega)]
    split
    · congr 1; omega
    · congr 1; omega
  rw [hs, he]
  have hc1 := c1_all x ws.length (by omega) (len' x) 0 (by omega) (by unfold len'; omega)
  by_cases hV : ∀ k (h : k < ws.length), RA.c0 ws[k] k.toUInt64 ws.length.toUInt64 = 1
  · rw [if_pos hV, if_pos (by
      apply beq_iff_eq.2; apply hc1.2; intro k _ h2; rw [hwx k h2]; exact hV k h2)]
    rw [l0_eq x _ _ (by omega) F (len' x) (c * 32000) [] (by omega) (by unfold len'; omega)
      (fun k _ h2 o' => by rw [hwx k (by omega), ← hx]; exact hF k (by omega) (hV k (by omega)) o'), List.nil_append]
  · rw [if_neg hV, if_neg]
    intro e; apply hV; intro k h
    have := (hc1.1 (beq_iff_eq.1 e)) k (by omega) h
    rwa [hwx k h] at this
theorem chunks (F : Nat → List UInt8) (n : Nat) : ∀ K, (List.range K).flatMap (fun c =>
    (List.range' (c * 32000) (min ((c + 1) * 32000) n - c * 32000)).flatMap F) =
    (List.range' 0 (min (K * 32000) n)).flatMap F
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.flatMap_append, chunks F n K, List.flatMap_singleton, ← List.flatMap_append]
    congr 1
    by_cases h : K * 32000 ≤ n
    · rw [show min (K * 32000) n = K * 32000 by omega]
      have := List.range'_append_1 (s := 0) (m := K * 32000) (n := min ((K + 1) * 32000) n - K * 32000)
      rw [Nat.zero_add] at this; rw [this]; congr 1; omega
    · rw [show min ((K + 1) * 32000) n - K * 32000 = 0 by omega, show min ((K + 1) * 32000) n = min (K * 32000) n by omega]
      simp

theorem fm_congr {α : Type} {f g : α → List UInt8} : ∀ (L : List α), (∀ x ∈ L, f x = g x) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | a :: L, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), fm_congr L (fun x hx => h x (by simp [hx]))]

theorem range_flat {α : Type} (G : α → List UInt8) (d : α) : ∀ (L : List α) (s : Nat),
    (List.range' s L.length).flatMap (fun k => G (L.getD (k - s) d)) = L.flatMap G
  | [], s => by simp
  | a :: L, s => by
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.flatMap_cons, Nat.sub_self]
    congr 1
    rw [← range_flat G d L (s + 1)]
    apply fm_congr; intro k hk
    rw [List.mem_range'_1] at hk
    rw [show k - s = (k - (s + 1)) + 1 by omega]; rfl

/-- **the rv2arm translator as a Lean function on bytes** (`rv2arm.sh`: one `RA.m` run per chunk of 32000 RV words,
with the chunk index as a 4-byte header, concatenated) -/
def rv2arm (code : List UInt8) : List UInt8 :=
  (List.range ((code.length / 4 + 31999) / 32000)).flatMap fun c => RA.m (le4 c.toUInt64 ++ code)

/-- **rv2arm on Gen's words**: when it emits anything, it emits every instruction's block, and the program is
`progOK` (rv2arm's validation, `armOK` at every index) -/
theorem rv2arm_ok (Cj : List J) (hn : Cj.length < 2 ^ 18) (hJ : ∀ j ∈ Cj, JOK j)
    (hne : rv2arm ((Cj.map encG).flatMap le4) ≠ []) :
    rv2arm ((Cj.map encG).flatMap le4) = Cj.flatMap bytesJ ∧ progOK Cj = true := by
  have hJk : ∀ k (h : k < Cj.length), JOK Cj[k] := fun k h => hJ _ (List.getElem_mem h)
  have hw : ∀ k (h : k < (Cj.map encG).length), (Cj.map encG)[k].toNat < 2 ^ 32 := fun k h => by
    rw [List.getElem_map]; exact encG_lt _ (hJk k (by simpa using h)).1
  have hl : ((Cj.map encG).flatMap le4).length / 4 = Cj.length := by rw [flat_len]; simp
  let F : Nat → List UInt8 := fun k => bytesJ (Cj.getD k (.jalr 0 0))
  have hF : ∀ c : Nat, ∀ k (h : k < (Cj.map encG).length), RA.c0 (Cj.map encG)[k] k.toUInt64 (Cj.map encG).length.toUInt64 = 1 →
      ∀ o, RA.t0 (le4 c.toUInt64 ++ (Cj.map encG).flatMap le4) o (Cj.map encG)[k] = o ++ F k := by
    intro c k h hc o
    have hk : k < Cj.length := by simpa using h
    rw [List.getElem_map] at hc ⊢
    simp only [List.length_map] at hc
    have hok := c0_ok _ (hJk k hk) k Cj.length hk (by omega) hc
    rw [t0_ok _ _ _ _ _ (hJk k hk) hok]
    simp only [emit, F, bytesJ, blockJ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  unfold rv2arm at hne ⊢
  rw [hl] at hne ⊢
  have hm : ∀ c, c < (Cj.length + 31999) / 32000 → RA.m (le4 c.toUInt64 ++ (Cj.map encG).flatMap le4) =
      if ∀ k (h : k < (Cj.map encG).length), RA.c0 (Cj.map encG)[k] k.toUInt64 (Cj.map encG).length.toUInt64 = 1 then
        (List.range' (c * 32000) (min ((c + 1) * 32000) (Cj.map encG).length - c * 32000)).flatMap F
      else [] := fun c hc =>
    m_eq c (by omega) _ (by simp; omega) hw F (by simp; omega) (hF c)
  rw [fm_congr _ (fun c hc => hm c (List.mem_range.1 hc))] at hne ⊢
  by_cases hV : ∀ k (h : k < (Cj.map encG).length), RA.c0 (Cj.map encG)[k] k.toUInt64 (Cj.map encG).length.toUInt64 = 1
  · rw [fm_congr _ (fun c _ => if_pos hV)]
    simp only [List.length_map]
    rw [chunks F Cj.length, show min ((Cj.length + 31999) / 32000 * 32000) Cj.length = Cj.length by omega]
    refine ⟨?_, ?_⟩
    · have := range_flat bytesJ (.jalr 0 0) Cj 0
      simp only [Nat.sub_zero] at this; exact this
    · unfold progOK; rw [List.all_eq_true]; intro i hi
      rw [List.mem_range] at hi
      rw [List.getElem?_eq_getElem hi]
      have hc := hV i (by simpa using hi)
      rw [List.getElem_map] at hc; simp only [List.length_map] at hc
      exact c0_ok _ (hJk i hi) i Cj.length hi (by omega) hc
  · rw [fm_congr _ (fun c _ => if_neg hV)] at hne; simp at hne
end ArmRA

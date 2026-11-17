import Nano.V2Boot.ParseS3
namespace Nano.V2B
open Nano.V2S

theorem bsizeS_eq (l : List UInt64) : bsizeS l = l.length.toUInt64 := by
  induction l with
  | nil => rfl
  | cons a r ih => simp [bsizeS, ih]

theorem nthS_eq : ∀ (l : List UInt64) (i : UInt64), nthS l i = l.getD i.toNat 0
  | [], _ => by simp [nthS]
  | x :: r, i => by
    unfold nthS
    by_cases h : i = 0
    · subst h; simp
    · have hi : i.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
      rw [if_neg (by simpa using h), nthS_eq r (i - 1)]
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      obtain ⟨n, hn⟩ : ∃ n, i.toNat = n + 1 := ⟨i.toNat - 1, by omega⟩
      simp [hn]

theorem bgetS_eq (b : List UInt64) (i : UInt64) (h : b.length < 2 ^ 64) : bgetS b.reverse i = bget b i := by
  unfold bgetS bget
  rw [bsizeS_eq, List.length_reverse]
  have hL : b.length.toUInt64.toNat = b.length := by simp; omega
  by_cases hi : i.toNat < b.length
  · have h1 : i < b.length.toUInt64 := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [if_pos h1, nthS_eq]
    have h3 : (b.length.toUInt64 - 1).toNat = b.length - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hL]
    have h2 : (b.length.toUInt64 - 1 - i).toNat = b.length - 1 - i.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h3]
    rw [h2]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by omega)]
    congr 2; omega
  · have h1 : ¬ i < b.length.toUInt64 := by intro hlt; rw [UInt64.lt_iff_toNat_lt, hL] at hlt; omega
    rw [if_neg h1, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

set_option maxRecDepth 10000 in
theorem tokOk_all : ∀ n : Fin 256, (tokOk (UInt64.ofNat n) == 1) =
    (((1 ≤ UInt64.ofNat n && UInt64.ofNat n ≤ 4) || (6 ≤ UInt64.ofNat n && UInt64.ofNat n ≤ 13)) : Bool) := by
  decide +kernel

theorem tokOk_eq (c : UInt64) (h : c < 256) : (tokOk c == 1) =
    (((1 ≤ c && c ≤ 4) || (6 ≤ c && c ≤ 13)) : Bool) := by
  have := tokOk_all ⟨c.toNat, by rw [UInt64.lt_iff_toNat_lt] at h; simpa using h⟩
  simpa using this

theorem ty34_eq (c : UInt64) : (ty34 c == 1) = (c == 3 || c == 4) := by
  unfold ty34; by_cases h3 : c == 3 <;> by_cases h4 : c == 4 <;> simp_all

variable (xs : List UInt8)

theorem idVS_eq : ∀ (n : Nat) (q : UInt64), n < 2 ^ 64 → idVS n.toUInt64 xs q = idV n xs q
  | 0, _, _ => by rw [idVS, dif_pos fuel_zero, idV]
  | n + 1, q, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun q => idVS_eq n q (by omega)
    rw [idVS, dif_neg h1, idV]; simp only [rdS_eq, lenS_eq, h2, ih]
    by_cases ha : q < len xs
    · simp only [ha, if_true]
      by_cases h0 : rd xs q = 0
      · simp [h0]
      · by_cases h1' : rd xs q = 1
        · by_cases h3 : q + 1 < len xs <;> simp [h0, h1', h3]
        · simp [h0, h1']
    · simp [ha]

theorem tnxS_eq (n : Nat) (p : UInt64) (h : n < 2 ^ 64) : tnxS n.toUInt64 xs p = tnx n xs p := by
  simp only [tnxS, tnx, rdS_eq, idVS_eq xs n _ h]

theorem vldS_eq : ∀ (n : Nat) (p : UInt64), n < 2 ^ 64 → vldS n.toUInt64 xs p = vld n xs p
  | 0, _, _ => by rw [vldS, dif_pos fuel_zero, vld]
  | n + 1, p, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun p => vldS_eq n p (by omega)
    rw [vldS, dif_neg h1, vld]; simp only [rdS_eq, lenS_eq, h2, ih, tokOk_eq _ (rd_lt _ _), idVS_eq xs n _ (by omega)]


theorem ntokS_eq : ∀ (n : Nat) (p c : UInt64), n < 2 ^ 64 → ntokS n.toUInt64 xs p c = ntok n xs p c
  | 0, _, _, _ => by rw [ntokS, dif_pos fuel_zero, ntok]
  | n + 1, p, c, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun p c => ntokS_eq n p c (by omega)
    rw [ntokS, dif_neg h1, ntok]; simp only [lenS_eq, h2, ih, tnxS_eq xs n _ (by omega)]

theorem nmEqS_eq : ∀ (n : Nat) (a b : UInt64), n < 2 ^ 64 → nmEqS n.toUInt64 xs a b = nmEq n xs a b
  | 0, _, _, _ => by rw [nmEqS, dif_pos fuel_zero, nmEq]
  | n + 1, a, b, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun a b => nmEqS_eq n a b (by omega)
    rw [nmEqS, dif_neg h1, nmEq]; simp only [rdS_eq, h2, ih]
    by_cases ha1 : rd xs a = 1 <;> by_cases hb1 : rd xs b = 1 <;> by_cases ha0 : rd xs a = 0 <;>
      by_cases hb0 : rd xs b = 0 <;> simp_all

theorem lookVS_eq (S : List UInt64) (hS : S.length < 2 ^ 64) :
    ∀ (n : Nat) (i g : UInt64), n < 2 ^ 64 → lookVS n.toUInt64 xs S.reverse i g = lookV n xs S i g
  | 0, _, _, _ => by rw [lookVS, dif_pos fuel_zero, lookV]
  | n + 1, i, g, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i => lookVS_eq S hS n i g (by omega)
    rw [lookVS, dif_neg h1, lookV]; simp only [h2, ih, bgetS_eq _ _ hS, nmEqS_eq xs n _ _ (by omega)]

theorem findVS_eq (D : List UInt64) (hD : D.length < 2 ^ 64) :
    ∀ (n : Nat) (i g : UInt64), n < 2 ^ 64 → findVS n.toUInt64 xs D.reverse i g = findV n xs D i g
  | 0, _, _, _ => by rw [findVS, dif_pos fuel_zero, findV]
  | n + 1, i, g, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := fun i => findVS_eq D hD n i g (by omega)
    rw [findVS, dif_neg h1, findV]; simp only [h2, ih, bgetS_eq _ _ hD, nmEqS_eq xs n _ _ (by omega)]

theorem rdWS_eq (p : UInt64) : rdWS xs p = rdW xs p := by simp only [rdWS, rdW, rdS_eq]


theorem putR2_rev (o : List UInt8) (m x : UInt64) : putR2 o.reverse m x = (put2 o m x).reverse := by
  simp [putR2, putR, put2, put]

theorem putLiS_rev (o : List UInt8) (v : UInt64) : putLiS o.reverse v = (putLi o v).reverse := by
  simp only [putLiS, putLi, putR2_rev]

theorem putCallS_rev (o : List UInt8) (j k : UInt64) : putCallS o.reverse j k = (putCall o j k).reverse := by
  simp only [putCallS, putCall, putR2_rev]

theorem fpushS_rev (F : List UInt64) (t a b : UInt64) : fpushS F.reverse t a b = (fpush F t a b).reverse := by
  simp [fpushS, fpush, bpush]

theorem bpopS_rev (l : List UInt64) : bpopS l.reverse = (bpop l).reverse := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · rfl
  · simp [bpopS, bpop]

theorem fpopS_rev (F : List UInt64) : fpopS F.reverse = (fpop F).reverse := by
  simp only [fpopS, fpop, bpopS_rev]

theorem sat'_eq (a b : UInt64) : sat' a b = sat a b := rfl

/-- the reversed state -/
def rv : PS → PSR
  | (c, f, x, y, p, d, na, cg, cf, o, S, D, F) => (c, f, x, y, p, d, na, cg, cf, o.reverse, S.reverse, D.reverse, F.reverse)


theorem rv_mk (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    rv (c, f, x, y, p, d, na, cg, cf, o, S, D, F) = (c, f, x, y, p, d, na, cg, cf, o.reverse, S.reverse, D.reverse, F.reverse) := rfl

/-- the buffers are short enough for their sizes to be words -/
def Lens (s : PS) : Prop := match s with
  | (_, _, _, _, _, _, _, _, _, _, S, D, F) => S.length < 2 ^ 62 ∧ D.length < 2 ^ 62 ∧ F.length < 2 ^ 62

theorem stIdS_eq (n : Nat) (hn : n < 2 ^ 64) (f a : UInt64) (s : PS) (hs : Lens s) :
    stIdS n.toUInt64 xs f a (rv s) = rv (stId n xs f a s) := by
  obtain ⟨c, f0, x, y, p, d, na, cg, cf, o, S, D, F⟩ := s
  obtain ⟨hS, hD, hF⟩ := hs
  simp only [rv_mk, stIdS, stId, bsizeS_eq, List.length_reverse, bsize, lookVS_eq xs S (by omega) n _ _ hn,
    findVS_eq xs D (by omega) n _ _ hn, bgetS_eq _ _ (show D.length < 2 ^ 64 by omega), tnxS_eq xs n _ hn,
    putR2_rev, putCallS_rev, fpushS_rev, sat'_eq, apply_ite rv]
  split <;> (try split) <;> (try split) <;> simp_all [rv_mk]


theorem stRetFS_eq (n : Nat) (hn : n < 2 ^ 64) (s : PS) (hs : Lens s) :
    stRetFS n.toUInt64 xs (rv s) = rv (stRetF n xs s) := by
  obtain ⟨c, f, x, y, p, d, na, cg, cf, o, S, D, F⟩ := s
  obtain ⟨hS, hD, hF⟩ := hs
  simp only [rv_mk, stRetFS, stRetF, bsizeS_eq, List.length_reverse, bsize, bgetS_eq _ _ (show F.length < 2 ^ 64 by omega),
    rdS_eq, putR2_rev, putCallS_rev, fpushS_rev, fpopS_rev, bpopS_rev, sat'_eq, apply_ite rv]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> simp_all [rv_mk, bpush]


theorem stIdS_eq' (n : Nat) (hn : n < 2 ^ 64) (f a c f0 x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (hS : S.length < 2 ^ 62) (hD : D.length < 2 ^ 62) (hF : F.length < 2 ^ 62) :
    stIdS n.toUInt64 xs f a (c, f0, x, y, p, d, na, cg, cf, o.reverse, S.reverse, D.reverse, F.reverse) =
      rv (stId n xs f a (c, f0, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  have := stIdS_eq xs n hn f a (c, f0, x, y, p, d, na, cg, cf, o, S, D, F) ⟨hS, hD, hF⟩
  rwa [rv_mk] at this

theorem stRetFS_eq' (n : Nat) (hn : n < 2 ^ 64) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (hS : S.length < 2 ^ 62) (hD : D.length < 2 ^ 62) (hF : F.length < 2 ^ 62) :
    stRetFS n.toUInt64 xs (c, f, x, y, p, d, na, cg, cf, o.reverse, S.reverse, D.reverse, F.reverse) =
      rv (stRetF n xs (c, f, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  have := stRetFS_eq xs n hn (c, f, x, y, p, d, na, cg, cf, o, S, D, F) ⟨hS, hD, hF⟩
  rwa [rv_mk] at this

set_option maxHeartbeats 0 in
theorem pstepS_eq (n : Nat) (hn : n < 2 ^ 64) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (hS : S.length < 2 ^ 62) (hD : D.length < 2 ^ 62) (hF : F.length < 2 ^ 62) :
    pstepS n.toUInt64 xs (c, f, x, y, p, d, na, cg, cf, o.reverse, S.reverse, D.reverse, F.reverse) =
      rv (pstep n xs (c, f, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  simp only [pstepS, pstep, rdS_eq, tnxS_eq xs n _ hn, findVS_eq xs D (by omega) n _ _ hn, lenS_eq, bsizeS_eq,
    List.length_reverse, bsize, stIdS_eq' xs n hn (hS := hS) (hD := hD) (hF := hF), stRetFS_eq' xs n hn (hS := hS) (hD := hD) (hF := hF), putR2_rev, putLiS_rev, putCallS_rev, fpushS_rev,
    rdWS_eq, sat'_eq, ty34_eq, apply_ite rv, rv_mk]
  by_cases h1 : c = 1
  · subst h1; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h2 : c = 2
  · subst h2; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h3 : c = 3
  · subst h3; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h4 : c = 4
  · subst h4; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h5 : c = 5
  · subst h5; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h6 : c = 6
  · subst h6; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h7 : c = 7
  · subst h7; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h8 : c = 8
  · subst h8; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h9 : c = 9
  · subst h9; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h10 : c = 10
  · subst h10; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h11 : c = 11
  · subst h11; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  by_cases h12 : c = 12
  · subst h12; simp <;> (repeat' split) <;> simp_all [rv_mk, bpush]
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]


def LensB (k : Nat) (s : PS) : Prop := match s with
  | (_, _, _, _, _, _, _, _, _, _, S, D, F) => S.length < k ∧ D.length < k ∧ F.length < k

theorem LensB_mk (k : Nat) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    LensB k (c, f, x, y, p, d, na, cg, cf, o, S, D, F) ↔ (S.length < k ∧ D.length < k ∧ F.length < k) := Iff.rfl

theorem LensB_mono (k m : Nat) (h : k ≤ m) (s : PS) : LensB k s → LensB m s := by
  obtain ⟨c, f, x, y, p, d, na, cg, cf, o, S, D, F⟩ := s
  simp only [LensB_mk]; omega

theorem stId_lens (n : Nat) (f a : UInt64) (k : Nat) (c f0 x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (h : S.length < k ∧ D.length < k ∧ F.length < k) : LensB (k + 3) (stId n xs f a (c, f0, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  simp only [stId, apply_ite (LensB (k + 3)), LensB_mk, fpush, bpush]
  obtain ⟨h1, h2, h3⟩ := h
  repeat' split
  all_goals first | omega | (simp_all <;> omega) | simp_all

theorem stRetF_lens (n : Nat) (k : Nat) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (h : S.length < k ∧ D.length < k ∧ F.length < k) : LensB (k + 3) (stRetF n xs (c, f, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  simp only [stRetF, apply_ite (LensB (k + 3)), LensB_mk, fpush, fpop, bpush, bpop]
  obtain ⟨h1, h2, h3⟩ := h
  repeat' split
  all_goals first | omega | (simp_all <;> omega) | simp_all

set_option maxHeartbeats 0 in
theorem pstep_lens (n : Nat) (k : Nat) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (h : S.length < k ∧ D.length < k ∧ F.length < k) : LensB (k + 3) (pstep n xs (c, f, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  have hs := fun f1 a1 => stId_lens xs n f1 a1 k c f x y p d na cg cf o S D F h
  have hr := stRetF_lens xs n k c f x y p d na cg cf o S D F h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [pstep, apply_ite (LensB (k + 3)), LensB_mk, fpush, bpush]
  by_cases hc1 : c = 1
  · subst hc1; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc2 : c = 2
  · subst hc2; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc3 : c = 3
  · subst hc3; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc4 : c = 4
  · subst hc4; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc5 : c = 5
  · subst hc5; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc6 : c = 6
  · subst hc6; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc7 : c = 7
  · subst hc7; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc8 : c = 8
  · subst hc8; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc9 : c = 9
  · subst hc9; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc10 : c = 10
  · subst hc10; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc11 : c = 11
  · subst hc11; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  by_cases hc12 : c = 12
  · subst hc12; simp <;> (repeat' split) <;> first | exact hs _ _ | exact hr | omega | (simp_all <;> omega) | simp_all
  simp [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12]; omega


theorem prunS_eq (n : Nat) (hn : n < 2 ^ 64) : ∀ (g k : Nat) (s : PS), g < 2 ^ 64 → LensB k s → k + 3 * g < 2 ^ 62 →
    prunS g.toUInt64 n.toUInt64 xs (rv s) = (prun g n xs s).reverse
  | 0, k, s, _, _, _ => by rw [prunS, dif_pos fuel_zero]; simp [prun]
  | g + 1, k, (c, f, x, y, p, d, na, cg, cf, o, S, D, F), hg, hL, hk => by
    obtain ⟨hh1, hh2⟩ := fuel_succ g hg
    have hL' := hL
    obtain ⟨h1, h2, h3⟩ := hL
    have hp := pstepS_eq xs n hn c f x y p d na cg cf o S D F (by omega) (by omega) (by omega)
    have hl := pstep_lens xs n k c f x y p d na cg cf o S D F ⟨h1, h2, h3⟩
    rw [prunS, dif_neg hh1, rv_mk, hp]
    simp only [prun]
    generalize e : pstep n xs (c, f, x, y, p, d, na, cg, cf, o, S, D, F) = s' at hl ⊢
    obtain ⟨c', f', x', y', p', d', na', cg', cf', o', S', D', F'⟩ := s'
    simp only [rv_mk, cOf, oOf]
    have ih := prunS_eq n hn g (k + 3) (c', f', x', y', p', d', na', cg', cf', o', S', D', F') (by omega) hl (by omega)
    rw [hh2]
    by_cases hc0 : c' = 0
    · simp [hc0]
    · by_cases hc13 : c' = 13
      · simp [hc13]
      · simp only [rv_mk] at ih
        simp [hc0, hc13, ih]


theorem hd12_eq (b : UInt64) : (hd12 b == 1) = (b == 1 || b == 2) := by
  unfold hd12; by_cases h1 : b == 1 <;> by_cases h2 : b == 2 <;> simp_all

/-- **the bridge**: the S3 form of the v2 parser is `p2bV` on every input of length < 2^27 -/
theorem p2bVS_eq (xs : List UInt8) (hx : xs.length < 2 ^ 27) : p2bVS xs = p2bV xs := by
  have hn : 16 * xs.length + 16 < 2 ^ 64 := by omega
  have hG : 13 * xs.length + 6 < 2 ^ 64 := by omega
  have e1 : 16 * lenS xs + 16 = (16 * xs.length + 16).toUInt64 := by rw [lenS_eq]; simp [len]
  have e2 : 13 * lenS xs + 6 = (13 * xs.length + 6).toUInt64 := by rw [lenS_eq]; simp [len]
  unfold p2bVS p2bV
  simp only [e1, e2, hd12_eq, rdS_eq, vldS_eq xs _ _ hn, ntokS_eq xs _ _ _ hn]
  by_cases h1 : (rd xs 0 == 1 || rd xs 0 == 2) = true
  · by_cases h2 : (vld (16 * xs.length + 16) xs 1 == 1) = true
    · have := prunS_eq xs (16 * xs.length + 16) hn (13 * xs.length + 6) 1
        (1, ntok (16 * xs.length + 16) xs 1 0 + 1, 0, 0, 1, 0, 0, 0, 0, [], [], [], []) hG
        (by simp [LensB_mk]) (by omega)
      rw [rv_mk] at this
      simp only [List.reverse_nil] at this
      simp only [h1, h2, if_true]
      rw [this, List.reverse_reverse]; simp
    · simp [h1, h2]
  · simp [h1]

end Nano.V2B

/- Nano/V2Self/Proof/OwnP29: `o42` (the verify flags buffer: clamped kinds read from inference's f, then zero flags). -/
import Nano.V2Self.Proof.OwnP28
namespace OwnP
open C OwnSpec ParSpec

theorem o42_eq (f : Buf) : ∀ (m : Nat) (y : Buf) (j n : Nat), j ≤ y.length → y.length < 2 ^ 62 → 2 * n - j ≤ m →
    j ≤ 2 * n → n < 2 ^ 20 →
    (o42 m y f (u j) (u n)).length = max y.length (2 * n) ∧
    ∀ q, (o42 m y f (u j) (u n)).getD q 0 =
      if j ≤ q ∧ q < 2 * n then (if q < n then cl (f.getD q 0) else 0) else y.getD q 0 := by
  intro m; induction m with
  | zero => intro y j n hj hy hm hjn hn; rw [o42]; exact ⟨by omega, fun q => by rw [if_neg (by omega)]⟩
  | succ m ih =>
    intro y j n hj hy hm hjn hn
    rw [o42]
    have e2 : (2 : UInt64) * u n = u (2 * n) := by rw [show (2 : UInt64) = u 2 from rfl, u_mul]
    rw [e2]
    by_cases h : j < 2 * n
    · rw [if_pos ((u_lt (by omega) (by omega)).mpr h)]
      simp only [bget_u f (show j < 2 ^ 64 by omega), u_lt' (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega),
        show u j + 1 = u (j + 1) from u_add j 1]
      generalize hw : (if j < n then (if f.getD j 0 < 2 then f.getD j 0 else 2) else (0 : UInt64)) = w
      have s0 := o0_step (b := y) hj hy w
      have := ih (o0 y (u j) w) (j + 1) n (by rw [s0.1]; omega) (by rw [s0.1]; omega) (by omega) (by omega) hn
      refine ⟨by rw [this.1, s0.1]; omega, fun q => ?_⟩
      rw [this.2, s0.2]
      by_cases hq : j + 1 ≤ q ∧ q < 2 * n
      · rw [if_pos hq, if_pos (show j ≤ q ∧ q < 2 * n by omega)]
      · rw [if_neg hq]; by_cases hq2 : q = j
        · subst hq2; rw [if_pos rfl, if_pos (by omega), ← hw]; rfl
        · rw [if_neg hq2, if_neg (by omega)]
    · rw [if_neg (fun e => h ((u_lt (by omega) (by omega)).mp e))]
      exact ⟨by omega, fun q => by rw [if_neg (by omega)]⟩

end OwnP

namespace OwnP
open C OwnSpec ParSpec

/-- the verify side between defs: cursor `i`, defs done `|ps|`, table -/
def VInv (x : Buf) (ps rs : List (List Nat)) (a b c t : Buf) (i : Nat) : Prop :=
  16 ≤ a.length ∧ a.length < 2 ^ 62 ∧ bget a 0 = u i ∧ bget a 1 = 0 ∧ bget a 13 = u ps.length ∧ ps.length ≤ 4096 ∧
  b.length < 2 ^ 62 ∧ c.length < 2 ^ 62 ∧ x.length < 2 ^ 40 ∧ TInv ps rs t

def WFD (d : DefA) : Prop := d.npw < 2 ^ 64 ∧ d.nslots < 2 ^ 64 ∧ d.nres < 2 ^ 64 ∧ WFB d.body

theorem defOk_eq (ps rs : List (List Nat)) (K : List Nat) (d : DefA) (h1 : K.length = d.nslots) (h2 : d.npw ≤ d.nslots) :
    defOk ps rs K d = (rootR ⟨ps, rs, K, d.npw⟩ (List.replicate d.nslots false) d.body).bind
      fun k => if k.length = d.nres then some k else none := by
  unfold defOk; rw [if_pos ⟨h1, h2⟩]; simp only; congr 1

theorem rt_of' {x t : Buf} {ps rs : List (List Nat)} {K : List Nat} {npw : Nat} (h1 : ps.length = rs.length)
    (hd : ps.length < 4096) (hl : t.length < 2 ^ 40) (hE : EntA ps rs t) : RT ⟨x, t, ps, rs, K, npw⟩ :=
  ⟨h1, hd, hl, fun c hc => by obtain ⟨a, -, rest⟩ := hE c hc; exact ⟨a, rest⟩⟩

theorem u_toNat_self (y : UInt64) : u y.toNat = y := UInt64.ofNat_toNat

@[simp] theorem bset_len (y : Buf) (k w : UInt64) : (bset y k w).length = y.length := by simp [bset]

theorem ite4 (A B C D : Prop) [Decidable A] [Decidable B] [Decidable C] [Decidable D] :
    (if A then (1 : UInt64) else if B then 1 else if C then 1 else if D then 1 else 0) = if A ∨ B ∨ C ∨ D then 1 else 0 := by
  by_cases A <;> by_cases B <;> by_cases C <;> by_cases D <;> simp_all

theorem bget_bset (y : Buf) (k k' w : UInt64) :
    bget (bset y k w) k' = if k.toNat = k'.toNat ∧ k.toNat < y.length then w else bget y k' := by
  simp only [bget, bset]; rw [getD_set]

theorem o38_ok {x s f v a b c t : Buf} {ps rs : List (List Nat)} {i : Nat} (hI : VInv x ps rs a b c t i) {d : DefA}
    {rest : List UInt64} (hx : x.drop i = d.ser ++ rest) (hw : WFD d)
    (hok : bget (o38 x s f v a b c t).2.2.2.1 1 ≠ 1) :
    ∃ K R, defOk ps rs K d = some R ∧ (∀ k ∈ K, k ≤ 2) ∧
      VInv x (ps ++ [K.take d.npw]) (rs ++ [R]) (o38 x s f v a b c t).2.2.2.1 (o38 x s f v a b c t).2.2.2.2.1
        (o38 x s f v a b c t).2.2.2.2.2.1 (o38 x s f v a b c t).2.2.2.2.2.2 (i + d.ser.length) := by
  obtain ⟨hl, hl2, h0, h1, h13, hps, hb, hc, hx40, hT⟩ := hI
  obtain ⟨wp, wn, wr, wb⟩ := hw
  have hxl := drop_len hx (by simp [DefA.ser]); simp only [DefA.ser, List.length_append, List.length_cons] at hxl
  have x2 : bget x (u i + 2) = u d.npw := by
    rw [show (2 : UInt64) = u 2 from rfl, u_add, xw hx (k := 2) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser]; rfl
  have x3 : bget x (u i + 3) = u d.nslots := by
    rw [show (3 : UInt64) = u 3 from rfl, u_add, xw hx (k := 3) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser]; rfl
  have x5 : bget x (u i + 5) = u d.nres := by
    rw [show (5 : UInt64) = u 5 from rfl, u_add, xw hx (k := 5) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser]; rfl
  have e5 : ∀ {y : Buf}, 16 ≤ y.length → bget (o5 y) 1 = 1 := fun h => err_o5 (by omega)
  generalize hO : o38 x s f v a b c t = O at hok ⊢
  unfold o38 at hO
  rw [h0] at hO
  dsimp only at hO
  rw [x2, x3, x5, h13] at hO
  have c1 : ((1048575 : UInt64) < u d.npw) = (1048575 < d.npw) := u_lt' (a := 1048575) (by omega) wp
  have c2 : ((1048575 : UInt64) < u d.nslots) = (1048575 < d.nslots) := u_lt' (a := 1048575) (by omega) wn
  have c3 : ((1048575 : UInt64) < u d.nres) = (1048575 < d.nres) := u_lt' (a := 1048575) (by omega) wr
  have c4 : (u d.nslots < u d.npw) = (d.nslots < d.npw) := u_lt' wn wp
  simp only [c1, c2, c3, c4] at hO
  by_cases k1 : 1048575 < d.npw
  · simp only [k1, ↓reduceIte, beq_self_eq_true] at hO; subst hO; exact absurd (e5 hl) hok
  by_cases k2 : 1048575 < d.nslots
  · simp only [k1, k2, ↓reduceIte, beq_self_eq_true] at hO; subst hO; exact absurd (e5 hl) hok
  by_cases k3 : 1048575 < d.nres
  · simp only [k1, k2, k3, ↓reduceIte, beq_self_eq_true] at hO; subst hO; exact absurd (e5 hl) hok
  by_cases k4 : d.nslots < d.npw
  · simp only [k1, k2, k3, k4, ↓reduceIte, beq_self_eq_true] at hO; subst hO; exact absurd (e5 hl) hok
  simp only [k1, k2, k3, k4, ↓reduceIte] at hO
  revert hO; split
  · rename_i h; exact absurd h (by decide)
  intro hO
  have c5 : (u ps.length < (4096 : UInt64)) = (ps.length < 4096) := u_lt' (b := 4096) (by omega) (by omega)
  simp only [c5] at hO
  have hd : ps.length < 4096 := by
    rcases Nat.lt_or_ge ps.length 4096 with hd | hd
    · exact hd
    · rw [if_neg (show ¬ ps.length < 4096 by omega)] at hO; subst hO; exact absurd (e5 hl) hok
  rw [if_pos hd] at hO
  generalize hZ : o36 1000 x (bset (bset (bset (bset (bset (bset s 1 0) 2 (u d.npw)) 3 (u d.nres)) 6 (u d.nslots)) 12
    (u i + 6)) 13 (u ps.length)) (o22 16777216 (o22 16777216 f 0 0 0 (2 * u d.nslots) 3) 0 0 0 (u d.npw) 4) v t = Z at hO
  obtain ⟨s2, f2, v2⟩ := Z
  dsimp only at hO
  generalize hT1 : o37 16777216 (bpush (bpush (bset t (u ps.length) (bsize t)) (u d.npw)) (u d.nres)) f2 0 (u d.npw) 1
    = T1 at hO
  generalize hB1 : o42 2097152 b f2 0 (u d.nslots) = B1 at hO
  generalize hA1 : bset (bset (bset (bset a 1 0) 2 (u d.npw)) 6 (u d.nslots)) 12 (u i + 6) = A1 at hO
  have hn20 : d.nslots < 2 ^ 20 := by omega
  -- the kinds
  generalize hK : (List.range d.nslots).map (fun q => (cl (f2.getD q 0)).toNat) = K
  have hKl : K.length = d.nslots := by rw [← hK]; simp
  have hKv : ∀ q < d.nslots, K.getD q 0 = (cl (f2.getD q 0)).toNat := by
    intro q hq; rw [← hK]; simp [List.getD_eq_getElem?_getD, hq]
  have hK2 : ∀ k ∈ K, k ≤ 2 := by
    intro k hk; rw [← hK] at hk; simp at hk; obtain ⟨q, -, rfl⟩ := hk; exact cl_le _
  -- the table during verify
  obtain ⟨e1, hE1, hl1⟩ := tab1 hT hd (p := d.npw) (r := d.nres) (by omega) (by omega) f2
  have hT1u : o37 16777216 (bpush (bpush (bset t (u ps.length) (u t.length)) (u d.npw)) (u d.nres)) f2 (u 0) (u d.npw) (u 1)
      = T1 := hT1
  rw [hT1u] at e1 hE1 hl1
  have hTl := hT.2.2.1
  -- the verify flags buffer
  have h42 := o42_eq f2 2097152 b 0 d.nslots (by omega) hb (by omega) (by omega) hn20
  have hB1u : o42 2097152 b f2 (u 0) (u d.nslots) = B1 := hB1
  rw [hB1u] at h42
  have hA1l : A1.length = a.length := by rw [← hA1]; simp [bset]
  have la : 12 < a.length := by omega
  have gA1 : bget A1 1 = 0 := by rw [← hA1]; simp [bget_bset, la, h1]
  have gA2 : bget A1 2 = u d.npw := by rw [← hA1]; simp [bget_bset, la]; omega
  have gA6 : bget A1 6 = u d.nslots := by rw [← hA1]; simp [bget_bset, la]; omega
  have gA12 : bget A1 12 = u (i + 6) := by rw [← hA1, ← u_add]; simp [bget_bset, la]; rfl
  have gA13 : bget A1 13 = u ps.length := by rw [← hA1]; simp [bget_bset, h13]
  let W : WCx := ⟨x, T1, ps, rs, K, d.npw⟩
  have hPre : Pre W A1 B1 c (i + 6) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc, ?_, by simp [W, hKl]; omega, by simp [W, hKl]; omega,
      hK2, hx40, by omega⟩
    · exact gA1
    · exact gA2
    · show bget A1 6 = u K.length; rw [hKl]; exact gA6
    · exact gA12
    · exact gA13
    · show 2 * K.length ≤ B1.length; rw [hKl, h42.1]; omega
    · rw [h42.1]; omega
    · intro q hq; change q < K.length at hq; change B1.getD q 0 = u (K.getD q 0); rw [hKl] at hq
      rw [h42.2, if_pos ⟨by omega, by omega⟩, if_pos hq, hKv q hq, u_toNat_self]
    · exact rt_of' hT.1 hd (by omega) hE1
  have hxb : x.drop (i + 6) = d.body.ser ++ ([21] ++ rest) := by
    have := drop_hdr (x := x) (i := i) (hdr := [20, d.id.toUInt64, d.npw.toUInt64, d.nslots.toUInt64, d.kind.toUInt64,
      d.nres.toUInt64]) (l := d.body.ser) (rest := [21] ++ rest) (by rw [hx]; simp [DefA.ser]) rfl
    simpa using this
  have hq : bget (o35 x A1 B1 c T1 0).1 1 ≠ 1 := by
    intro hq; rw [if_pos (by rw [hq]; rfl)] at hO; subst hO; exact hok hq
  rw [if_neg (by rw [beq_iff_eq]; exact hq)] at hO
  obtain ⟨ks, hroot, hpost⟩ := o35_ok (W := W) hPre wb hxb hq
  revert hO hpost; generalize o35 x A1 B1 c T1 0 = Q; obtain ⟨s3, f3, v3⟩ := Q; intro hO hpost
  obtain ⟨p1, p2, p3, p4, p7, p13, pf, pK, pf2, pv, pvv, pkl, pk1⟩ := hpost
  dsimp only at hO p1 p2 p3 p4 p7 p13 pf pK pf2 pv pvv
  have hj : bget x (u (i + 6 + d.body.ser.length)) = 21 := by
    rw [show i + 6 + d.body.ser.length = i + (6 + d.body.ser.length) by omega, xw hx (by simp [DefA.ser]; omega) (by omega)]
    simp only [DefA.ser, List.append_assoc]
    rw [show 6 + d.body.ser.length = [(20 : UInt64), d.id.toUInt64, d.npw.toUInt64, d.nslots.toUInt64, d.kind.toUInt64,
      d.nres.toUInt64].length + (d.body.ser.length + 0) from rfl, getD_app_right, getD_app_right]; rfl
  rw [p3, hj, if_pos (by decide), p7, u_beq (by omega) wr] at hO
  have hr : ks.length = d.nres := by
    rcases Nat.lt_or_ge 0 1 with _ | _
    · by_cases hr : ks.length = d.nres
      · exact hr
      · rw [if_neg (by simp [hr])] at hO; subst hO; exact absurd (e5 p1) hok
    · omega
  rw [if_pos (by simp [hr])] at hO
  subst hO
  have hroot' : rootR ⟨ps, rs, K, d.npw⟩ (List.replicate d.nslots false) d.body = some ks := by
    have := hroot
    change rootR ⟨ps, rs, K, d.npw⟩ (List.replicate K.length false) d.body = some ks at this
    rw [hKl] at this; exact this
  refine ⟨K, ks, ?_, hK2, ?_⟩
  · rw [defOk_eq ps rs K d hKl (by omega), hroot']; simp [hr]
  have hPl : (K.take d.npw).length = d.npw := by simp; omega
  have h2 := tab2 hT hd (P := K.take d.npw) (R := ks) (by omega) (by omega)
    (fun k hk => hK2 k (List.mem_of_mem_take hk)) pk1 f2 f3 v3
    (fun q hq => by
      rw [hPl] at hq
      have := pK q (by show q < K.length; omega)
      rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_take, hq]; rfl)
    pvv
  rw [hPl, hr, hT1u] at h2
  dsimp only
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, by simp; omega, pf, pv, hx40, h2⟩
  · rw [bget_bset, if_neg (by simp), bget_bset, if_pos ⟨rfl, by simp; omega⟩]
    show u (i + 6 + d.body.ser.length) + u 1 = _
    rw [u_add, show i + 6 + d.body.ser.length + 1 = i + d.ser.length by simp [DefA.ser]; omega]
  · rw [bget_bset, if_neg (by simp), bget_bset, if_neg (by simp)]; exact p4
  · rw [bget_bset, if_pos ⟨rfl, by simp; omega⟩]
    show u ps.length + u 1 = _
    rw [u_add]; simp only [List.length_append, List.length_singleton]



end OwnP

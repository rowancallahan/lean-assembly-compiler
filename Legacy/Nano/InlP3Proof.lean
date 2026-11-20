/- `inlP3 = inlB` (branch `nano-closeB`): the proof of `Nano/InlPProof.lean` for the slim step `mn3`
(`Nano/InlP3.lean`); only the step lemmas differ. -/
import Legacy.Nano.InlPProof
import Legacy.Nano.InlP3

set_option linter.unusedSimpArgs false

namespace Nano.IP
open Nano Nano.U

theorem m3_end (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat)
    (h : ¬ i < src.size) : mn3 ob src i ph m w n hi cp rem cs = ob := by
  rw [mn3, if_neg h]

/-- a copy step -/
theorem m3_copy (ob : Array Nat) (src : ByteArray) (i m w n hi cp rem cs : Nat)
    (h : i < src.size) (hr : 0 < rem) (hw : w < WCAP) : mn3 ob src i 0 m w n hi cp rem cs =
    mn3 (ob.set! (BASE + w) ob[BASE + cp]!) src i 0 m (w + 1) n hi (cp + 1) (rem - 1) cs := by
  rw [mn3, if_pos h]
  simp only [hr, if_true, hw]

/-- the first byte of a pair, a plain micro-op -/
theorem m3_a (ob : Array Nat) (src : ByteArray) (i m0 w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : b ≠ 13) (h14 : b ≠ 14) (h15 : b ≠ 15) (hw : w < WCAP) :
    mn3 ob src i 0 m0 w n hi cp 0 cs = mn3 (ob.set! (BASE + w) b.toNat) src (i + 1) 1 b.toNat (w + 1) n hi cp 0 cs := by
  have n13 : b.toNat ≠ 13 := fun e => h13 (UInt8.toNat_inj.mp (e.trans rfl))
  have n14 : b.toNat ≠ 14 := fun e => h14 (UInt8.toNat_inj.mp (e.trans rfl))
  have n15 : b.toNat ≠ 15 := fun e => h15 (UInt8.toNat_inj.mp (e.trans rfl))
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, n13, n14, n15, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    not_false_eq_true]

/-- the first byte of a pair, `13`/`14`/`15` -/
theorem m3_a' (ob : Array Nat) (src : ByteArray) (i m0 w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hm : b = 13 ∨ b = 14 ∨ b = 15) :
    mn3 ob src i 0 m0 w n hi cp 0 cs = mn3 ob src (i + 1) 1 b.toNat w n hi cp 0 cs := by
  have hw : True := trivial
  rw [mn3, if_pos h]
  rcases hm with rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `13`: close the def -/
theorem m3_b13 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hw : w < WCAP) :
    mn3 ob src i 1 13 w n hi cp 0 cs =
    mn3 (((ob.set! (BASE + w) b.toNat).set! (if n < 65536 then n + 1 else 65537) (w + 1)).set! HD
      (cs * 16777216 + w + 1)) src (i + 1) 0 13 (w + 1) (n + 1) hi cp 0 (w + 1) := by
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `14` -/
theorem m3_b14 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) :
    mn3 ob src i 1 14 w n hi cp 0 cs = mn3 ob src (i + 1) 0 14 w n b.toNat cp 0 cs := by
  have hw : True := trivial
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `15`, a def in the table -/
theorem m3_b15 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs a len : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : hi * 256 + b.toNat < n) (ha : ob[hi * 256 + b.toNat]! = a)
    (ha1 : ob[hi * 256 + b.toNat + 1]! = a + len + 1) (haW : a < WCAP) (hlW : len < WCAP) :
    mn3 ob src i 1 15 w n hi cp 0 cs = mn3 ob src (i + 1) 0 15 w n hi a len cs := by
  have hw : True := trivial
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj, ha, ha1, haW, show a + len + 1 - 1 - a = len by omega, hlW]

/-- the second byte, after `15`, no such def -/
theorem m3_b15' (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : ¬ hi * 256 + b.toNat < n) :
    mn3 ob src i 1 15 w n hi cp 0 cs = mn3 ob src (i + 1) 0 15 w n hi cp 0 cs := by
  have hw : True := trivial
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj]

/-- the second byte, after a plain micro-op -/
theorem m3_bx (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : m ≠ 13) (h14 : m ≠ 14) (h15 : m ≠ 15) (hw : w < WCAP) :
    mn3 ob src i 1 m w n hi cp 0 cs = mn3 (ob.set! (BASE + w) b.toNat) src (i + 1) 0 m (w + 1) n hi cp 0 cs := by
  rw [mn3, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, h13, h14, h15, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    not_false_eq_true]

theorem m3_copyAll : ∀ (c : List UInt8) (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat),
    i < src.size → w + c.length ≤ WCAP → cp + c.length ≤ w → ob.size = CAP →
    (∀ q (hq : q < c.length), ob[BASE + cp + q]! = c[q].toNat) →
    ∃ ob', ob'.size = CAP ∧ (∀ a, a < BASE + w → ob'[a]! = ob[a]!) ∧
      (∀ q (hq : q < c.length), ob'[BASE + w + q]! = c[q].toNat) ∧
      mn3 ob src i 0 m w n hi cp c.length cs = mn3 ob' src i 0 m (w + c.length) n hi (cp + c.length) 0 cs
  | [], ob, src, i, m, w, n, hi, cp, cs, _, _, _, hs, _ =>
    ⟨ob, hs, fun _ _ => rfl, fun q hq => absurd hq (Nat.not_lt_zero _), rfl⟩
  | b :: c, ob, src, i, m, w, n, hi, cp, cs, hi', hw, hcp, hs, hc => by
    simp only [List.length_cons] at hw hcp
    have h0 := hc 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hs1 : (ob.set! (BASE + w) b.toNat).size = CAP := by rw [aset_size, hs]
    obtain ⟨ob', hs', hlo, hc', he⟩ := m3_copyAll c (ob.set! (BASE + w) b.toNat) src i m (w + 1) n hi (cp + 1) cs hi'
      (by omega) (by omega) hs1 (fun q hq => by
        rw [get_set_lt _ _ _ _ (by omega), show BASE + (cp + 1) + q = BASE + cp + (q + 1) by omega,
          hc (q + 1) (by simp; omega)]; simp)
    refine ⟨ob', hs', fun a ha => by rw [hlo a (by omega), get_set_lt _ _ _ _ ha], fun q hq => ?_, ?_⟩
    · cases q with
      | zero =>
        rw [hlo _ (by omega), Nat.add_zero, get_set_self _ _ _ (by rw [hs]; unfold BASE CAP WCAP at *; omega)]; rfl
      | succ q =>
        rw [show BASE + w + (q + 1) = BASE + (w + 1) + q by omega, hc' q (by simp at hq; omega)]; rfl
    · show mn3 ob src i 0 m w n hi cp (c.length + 1) cs =
        mn3 ob' src i 0 m (w + (c.length + 1)) n hi (cp + (c.length + 1)) 0 cs
      rw [m3_copy ob src i m w n hi cp (c.length + 1) cs hi' (by omega) (by unfold WCAP at *; omega),
        Nat.add_sub_cancel, h0, he]
      congr 1 <;> omega

theorem m3_main : ∀ (rest : List UInt8) (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat)
    (tab : List (List UInt8)) (cur : List UInt8) (k : Nat) (last : List UInt8),
    src.data.toList.drop i = rest → Inv ob tab cur w n cs k last → hi < 256 →
    tot (inlS rest tab cur hi k last).1 (inlS rest tab cur hi k last).2.1 < WCAP →
    Post (mn3 ob src i 0 m w n hi cp 0 cs) (inlS rest tab cur hi k last).2.2.1 (inlS rest tab cur hi k last).2.2.2
  | [], ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, _, _ => by
    rw [m3_end _ _ _ _ _ _ _ _ _ _ _ (src_nil _ _ hr)]
    exact hdr_post _ _ _ _ hI.2.2.2.2.2.2.2.2 (by obtain ⟨_, _, _, h1, h2, _⟩ := hI; omega)
  | [b], ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, _, hf => by
    obtain ⟨hi1, hb, hr'⟩ := src_cons _ _ _ _ hr
    have hn := src_nil _ _ hr'
    have hcs : cs ≤ WCAP := by obtain ⟨_, _, _, h1, h2, _⟩ := hI; omega
    by_cases hm : b = 13 ∨ b = 14 ∨ b = 15
    · rw [m3_a' _ _ _ _ _ _ _ _ _ _ hi1 hb hm, m3_end _ _ _ _ _ _ _ _ _ _ _ hn]
      exact hdr_post _ _ _ _ hI.2.2.2.2.2.2.2.2 hcs
    · have hw : w < WCAP := by
        have := tot_lt _ _ _ _ _ _ hf; obtain ⟨_, _, h1, h2, _⟩ := hI; simp only [tot, inlS] at hf; omega
      rw [m3_a _ _ _ _ _ _ _ _ _ _ hi1 hb (fun e => hm (.inl e)) (fun e => hm (.inr (.inl e)))
        (fun e => hm (.inr (.inr e))) hw, m3_end _ _ _ _ _ _ _ _ _ _ _ hn]
      refine hdr_post _ cs _ _ (hdr_mono ob _ cs cs k last hI.2.2.2.2.2.2.2.2 (Nat.le_refl _) fun a ha => ?_) hcs
      obtain ⟨_, _, _, h1, _⟩ := hI
      exact get_set_lt _ _ _ _ (by omega)
  | m0 :: b :: r, ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, hhi, hf => by
    obtain ⟨hi1, hb0, hr1⟩ := src_cons _ _ _ _ hr
    obtain ⟨hi2, hb1, hr2⟩ := src_cons _ _ _ _ hr1
    have hI' := hI
    obtain ⟨hs, hn, hcs, hw0, hwW, ht, hbd, hcur, hh⟩ := hI'
    by_cases h13 : m0 = 13
    · subst h13
      rw [m3_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inl rfl), show (13 : UInt8).toNat = 13 from rfl]
      have e : inlS (13 :: b :: r) tab cur hi k last = inlS r (tab ++ [cur]) [] hi b.toNat cur := by
        rw [inlS, if_pos rfl]
      rw [e] at hf ⊢
      have := tot_lt _ _ _ _ _ _ hf
      simp only [tot, S_append, List.length_nil] at this
      rw [m3_b13 _ _ _ _ _ _ _ _ _ hi2 hb1 (by omega)]
      exact m3_main r _ src _ 13 (w + 1) (n + 1) hi cp (w + 1) _ _ _ _ hr2
        (inv13 ob tab cur w n cs k last b hI (by omega)) hhi hf
    by_cases h14 : m0 = 14
    · subst h14
      rw [m3_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inr (.inl rfl)), show (14 : UInt8).toNat = 14 from rfl, m3_b14 _ _ _ _ _ _ _ _ _ hi2 hb1]
      have e : inlS (14 :: b :: r) tab cur hi k last = inlS r tab cur b.toNat k last := by
        rw [inlS, if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      exact m3_main r ob src _ 14 w n b.toNat cp cs _ _ _ _ hr2 hI b.toNat_lt hf
    by_cases h15 : m0 = 15
    · subst h15
      rw [m3_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inr (.inr rfl)), show (15 : UInt8).toNat = 15 from rfl]
      have e : inlS (15 :: b :: r) tab cur hi k last =
          inlS r tab (cur ++ tab.getD (hi * 256 + b.toNat) []) hi k last := by
        rw [inlS, if_neg (by decide), if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      have hbl := b.toNat_lt
      by_cases hj : hi * 256 + b.toNat < n
      · have hjt : hi * 256 + b.toNat < tab.length := by omega
        have eg : tab.getD (hi * 256 + b.toNat) [] = tab[hi * 256 + b.toNat] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
        rw [eg] at hf ⊢
        have ht1 := tot_lt _ _ _ _ _ _ hf
        simp only [tot, List.length_append] at ht1
        have hlt := S_take_lt tab _ hjt
        rw [m3_b15 ob src _ w n hi cp cs (S (tab.take (hi * 256 + b.toNat))) (tab[hi * 256 + b.toNat]).length b hi2 hb1
          hj (ht _ (by omega) (by omega)) (by rw [ht _ (by omega) (by omega), S_take_succ _ _ hjt])
          (by omega) (by omega)]
        rcases r with _ | ⟨b2, r⟩
        · rw [m3_end _ _ _ _ _ _ _ _ _ _ _ (src_nil _ _ hr2)]
          exact hdr_post _ _ _ _ hh (by omega)
        · obtain ⟨hi3, -, -⟩ := src_cons _ _ _ _ hr2
          obtain ⟨ob', hs', hk', hc', he⟩ := m3_copyAll (tab[hi * 256 + b.toNat]) ob src _ 15 w n hi
            (S (tab.take (hi * 256 + b.toNat))) cs hi3 (by omega) (by omega) hs
            (fun q hq => hbd _ hjt q hq)
          rw [he]
          exact m3_main (b2 :: r) ob' src _ 15 _ n hi _ cs _ _ _ _ hr2
            (inv_keep ob ob' tab cur w n cs k last hI hs' hk' _ hc' (by omega)) hhi hf
      · have eg : tab.getD (hi * 256 + b.toNat) [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show tab.length ≤ hi * 256 + b.toNat by omega)]
        rw [eg, List.append_nil] at hf ⊢
        rw [m3_b15' _ _ _ _ _ _ _ _ _ hi2 hb1 hj]
        exact m3_main r ob src _ 15 w n hi cp cs _ _ _ _ hr2 hI hhi hf
    · have e : inlS (m0 :: b :: r) tab cur hi k last = inlS r tab (cur ++ [m0, b]) hi k last := by
        rw [inlS, if_neg h13, if_neg h14, if_neg h15]
      rw [e] at hf ⊢
      have ht1 := tot_lt _ _ _ _ _ _ hf
      simp only [tot, List.length_append, List.length_cons, List.length_nil] at ht1
      have n13 : m0.toNat ≠ 13 := fun h => h13 (UInt8.toNat_inj.mp (h.trans rfl))
      have n14 : m0.toNat ≠ 14 := fun h => h14 (UInt8.toNat_inj.mp (h.trans rfl))
      have n15 : m0.toNat ≠ 15 := fun h => h15 (UInt8.toNat_inj.mp (h.trans rfl))
      rw [m3_a _ _ _ _ _ _ _ _ _ _ hi1 hb0 h13 h14 h15 (by omega),
        m3_bx _ _ _ _ _ _ _ _ _ _ hi2 hb1 n13 n14 n15 (by omega)]
      have hs2 : ((ob.set! (BASE + w) m0.toNat).set! (BASE + (w + 1)) b.toNat).size = CAP := by
        simp only [aset_size, hs]
      have hI2 := inv_keep ob ((ob.set! (BASE + w) m0.toNat).set! (BASE + (w + 1)) b.toNat) tab cur w n cs k last hI
        hs2 (fun a ha => by rw [get_set_lt _ _ _ _ (by omega), get_set_lt _ _ _ _ ha]) [m0, b] (fun q hq => by
          match q, hq with
          | 0, _ =>
            simp only [Nat.add_zero]
            rw [get_set_lt _ _ _ _ (by omega), get_set_self _ _ _ (by rw [hs]; unfold CAP BASE WCAP at *; omega)]
            rfl
          | 1, _ =>
            rw [show BASE + w + 1 = BASE + (w + 1) by omega,
              get_set_self _ _ _ (by rw [aset_size, hs]; unfold CAP BASE WCAP at *; omega)]
            rfl) (by simp; omega)
      exact m3_main r _ src _ m0.toNat (w + 1 + 1) n hi cp cs _ _ _ _ hr2 hI2 hhi hf

/-! ## the stage -/

theorem inv0_3 (sz : Nat) (h : sz = CAP) : Inv (Array.replicate sz 0) [] [] 0 0 0 0 [] := by
  subst h
  have g : ∀ j, (Array.replicate CAP 0)[j]! = 0 := fun j => by
    rw [arr_get]; simp [List.getElem?_replicate]; split <;> rfl
  refine ⟨by simp, rfl, rfl, rfl, by unfold WCAP; omega, fun j h1 _ => ?_, fun j hj => absurd hj (by simp),
    fun q hq => absurd hq (by simp), .inl ⟨g _, rfl, rfl⟩⟩
  rw [g]; simp [S]

/-- the main loop on an input -/
def inlR3 (xs : ByteArray) : Array Nat := mn3 (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0

theorem inlP3_def (xs : ByteArray) : inlP3 xs =
    em (Array.replicate (20 * (if (inlR3 xs)[HD]! % 16777216 == 0 then 0 else
        (inlR3 xs)[BASE + ((inlR3 xs)[HD]! % 16777216 - 1)]! % 256) +
      ((inlR3 xs)[HD]! % 16777216 - 1 - (inlR3 xs)[HD]! / 16777216 % 16777216) % 262144 + 38) 0) (inlR3 xs) 0
    ((inlR3 xs)[HD]! / 16777216 % 16777216)
    (((inlR3 xs)[HD]! % 16777216 - 1 - (inlR3 xs)[HD]! / 16777216 % 16777216) % 262144)
    (if (inlR3 xs)[HD]! % 16777216 == 0 then 0 else (inlR3 xs)[BASE + ((inlR3 xs)[HD]! % 16777216 - 1)]! % 256) := rfl

/-- **the paged inliner computes `inlB`** whenever the inliner's table fits the buffer -/
theorem inlP3_eq (x : List UInt8) (h : inlFits x) : (inlP3 ⟨⟨x⟩⟩).toList = inlB x := by
  have hm : Post (inlR3 ⟨⟨x⟩⟩) (inlS x [] [] 0 0 []).2.2.1 (inlS x [] [] 0 0 []).2.2.2 :=
    m3_main x _ ⟨⟨x⟩⟩ 0 0 0 0 0 0 0 [] [] 0 [] (by simp) (inv0_3 _ (by simp)) (by decide) h
  rw [inlP3_def]
  generalize inlR3 ⟨⟨x⟩⟩ = R at hm ⊢
  obtain ⟨h1, h2, h3⟩ := hm
  rw [h2, h1, inlB, inlGo_inlS]
  exact em_wrap R _ _ _ h3

end Nano.IP

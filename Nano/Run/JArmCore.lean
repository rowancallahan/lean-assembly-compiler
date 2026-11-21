/- E4, layers L5 (pass 2) and the CORE theorem (FABLE-M4): on Gen's words `gw Cj` (`JOK`, fewer than 2^18
instructions), if the nano translator `e64` returns a non-empty word buffer, the specification encoder accepts `Cj`
and the buffer is its words: `e64_core`, `e64_natEncJ`.  From `JArmBits` and `StepOK`. -/
import Nano.Run.JArmPass
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

theorem e14_toNat : e_14.toNat = 18446744073709551615 := by decide

/-- an atom's words only read `π` at its jump targets -/
theorem NTm.a_congr (t : NTm) (π π' : Nat → Nat) (q h : Nat) (hπ : ∀ p ∈ t.tg q, π p = π' p) :
    t.a π q h = t.a π' q h := by
  cases t <;> simp_all [NTm.a, NTm.tg]

theorem wordsFrom_congr (π π' : Nat → Nat) : ∀ (l : List NAt) (q h : Nat), (∀ p ∈ tgs l q, π p = π' p) →
    wordsFrom π l q h = wordsFrom π' l q h
  | [], _, _, _ => rfl
  | x :: l, q, h, hπ => by
    simp only [wordsFrom]
    rw [NTm.a_congr x.t π π' q h (fun p hp => hπ p (by simp only [tgs, List.mem_append]; exact Or.inl hp)),
      wordsFrom_congr π π' l _ _ (fun p hp => hπ p (by simp only [tgs, List.mem_append]; exact Or.inr hp))]

/-- the table lookup at an entry `1 + w` -/
theorem zpi_eq {Z : Buf} {p w : Nat} (hp : p < Z.length) (hZ : Z.length < 2 ^ 63) (hw : w + 1 < 2 ^ 64)
    (hg : Z.getD p 0 = (w + 1).toUInt64) : zpi Z p = w := by
  have hb : bget Z p.toUInt64 = (w + 1).toUInt64 := by
    unfold bget; rw [ArmRA.toU_toNat (by omega)]; exact hg
  have hne : (w + 1).toUInt64 ≠ 0 := fun e => by
    have := congrArg UInt64.toNat e
    rw [ArmRA.toU_toNat hw] at this
    exact absurd this (by simp)
  unfold zpi e59
  rw [if_pos (by rw [bsize_tU]; exact (tU_lt (by omega) (by omega)).2 hp), hb, if_neg (by simpa using hne),
    ← tU_succ hw]
  have e : w.toUInt64 + 1 - 1 = w.toUInt64 := by
    apply ArmRA.u64
    rw [UInt64.toNat_sub, UInt64.toNat_add, ArmRA.toU_toNat (by omega)]
    simp
    omega
  rw [e, ArmRA.toU_toNat (by omega)]

/-- the pre-zeroed table -/
theorem e44_rep (L : Nat) (hL : L + 1 < 2 ^ 63) : ∀ (k m : Nat), m ≤ L + 1 → L + 1 ≤ m + k →
    e44 k (List.replicate m 0) L.toUInt64 = List.replicate (L + 1) 0
  | 0, m, h1, h2 => by
    have : m = L + 1 := by omega
    subst this; rfl
  | k + 1, m, h1, h2 => by
    simp only [e44]
    by_cases hm : m < L + 1
    · have hlt : bsize (List.replicate m (0 : UInt64)) < L.toUInt64 + 1 := by
        rw [bsize_tU, List.length_replicate, tU_succ (by omega)]
        exact (tU_lt (by omega) (by omega)).2 hm
      rw [if_pos hlt]
      have : bpush (List.replicate m (0 : UInt64)) 0 = List.replicate (m + 1) 0 := by
        unfold bpush; rw [List.replicate_succ']
      rw [this]
      exact e44_rep L hL k (m + 1) (by omega) (by omega)
    · have : m = L + 1 := by omega
      subst this
      have hnl : ¬ bsize (List.replicate (L + 1) (0 : UInt64)) < L.toUInt64 + 1 := by
        rw [bsize_tU, List.length_replicate, tU_succ (by omega)]
        exact fun h => absurd ((tU_lt (by omega) (by omega)).1 h) (by omega)
      rw [if_neg hnl]

theorem rep_getD (m p : Nat) : (List.replicate m (0 : UInt64)).getD p 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- `e64`, with the pair of pass 1 as projections -/
theorem e64_eq (c : Buf) : e64 c =
    if bsize c == 0 then bnew else if 262144 < bsize c then bnew else
    if bsize (e46 16777216 c (bsize c) 0 (e44 16777216 bnew (bsize c)) bnew).1 == 0 then bnew
    else e47 16777216 c (bsize c) (e46 16777216 c (bsize c) 0 (e44 16777216 bnew (bsize c)) bnew).1 0 bnew := by
  first | rfl | (unfold e64; rfl)

section
variable (B : JArmBits) (S : StepOK) {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18)
include B S hJ hl

/-- pass 2, an atom whose target check passes -/
theorem e47_s (k q : Nat) (Z o : Buf) (hq : q < Cj.length)
    (h48 : e48 (gw Cj) (bsize (gw Cj)) Z q.toUInt64 (candC (Cj.drop q)) ≠ 0) :
    e47 (k + 1) (gw Cj) (bsize (gw Cj)) Z q.toUInt64 o =
      e47 k (gw Cj) (bsize (gw Cj)) Z
        (q.toUInt64 + e36 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)))
        (e40 (gw Cj) (bsize (gw Cj)) Z o q.toUInt64 (candC (Cj.drop q))) := by
  have hi : q.toUInt64 < bsize (gw Cj) := by
    rw [bsize_gw]; exact (tU_lt (by omega) (by omega)).2 hq
  have he := e35_eq B hJ hl q (by omega)
  simp only [e47]
  rw [if_pos hi]
  simp only [he]
  rw [if_neg (by simpa using h48)]

/-- pass 2 rejects a target that is no boundary -/
theorem e47_f (k q : Nat) (Z o : Buf) (hq : q < Cj.length)
    (h48 : e48 (gw Cj) (bsize (gw Cj)) Z q.toUInt64 (candC (Cj.drop q)) = 0) :
    e47 (k + 1) (gw Cj) (bsize (gw Cj)) Z q.toUInt64 o = [] := by
  have hi : q.toUInt64 < bsize (gw Cj) := by
    rw [bsize_gw]; exact (tU_lt (by omega) (by omega)).2 hq
  have he := e35_eq B hJ hl q (by omega)
  simp only [e47]
  rw [if_pos hi]
  simp only [he, h48]
  rfl

/-- pass 2 at the end of the program -/
theorem e47_e (k : Nat) (Z o : Buf) : e47 (k + 1) (gw Cj) (bsize (gw Cj)) Z (bsize (gw Cj)) o = o := by
  simp [e47]

/-- a passed target check: the target is a table entry that is not 0 -/
theorem tgt_of_e48 (Z : Buf) (q p : Nat) (t : UInt64) (hp : p < 2 ^ 62)
    (he : e65 (gw Cj) (bsize (gw Cj)) q.toUInt64 t = p.toUInt64)
    (h48 : e48 (gw Cj) (bsize (gw Cj)) Z q.toUInt64 t ≠ 0) : p ≤ Cj.length ∧ Z.getD p 0 ≠ 0 := by
  have hne : p.toUInt64 ≠ e_14 := fun e => by
    have := congrArg UInt64.toNat e
    rw [ArmRA.toU_toNat (by omega), e14_toNat] at this
    omega
  unfold e48 at h48
  simp only [he] at h48
  rw [if_neg (by simpa using hne)] at h48
  by_cases hlt : p.toUInt64 < bsize (gw Cj) + 1
  · rw [if_pos hlt] at h48
    rw [bsize_gw, tU_succ (by omega)] at hlt
    have hle := (tU_lt (by omega) (by omega)).1 hlt
    refine ⟨by omega, fun hz => h48 ?_⟩
    have hb : bget Z p.toUInt64 = 0 := by
      unfold bget; rw [ArmRA.toU_toNat (by omega)]; exact hz
    rw [hb]; rfl
  · rw [if_neg hlt] at h48
    exact absurd rfl h48

/-- **pass 2**: a non-empty result is the words of the trace, and every jump target is a table entry -/
theorem pass2 (Z : Buf) : ∀ (k q : Nat) (ts : List NTm) (o : Buf), Tr Cj q ts →
    e47 k (gw Cj) (bsize (gw Cj)) Z q.toUInt64 o ≠ [] →
    e47 k (gw Cj) (bsize (gw Cj)) Z q.toUInt64 o = o ++ (wordsFrom (zpi Z) (ats ts) q o.length).map Nat.toUInt64 ∧
      ∀ p ∈ tgs (ats ts) q, p ≤ Cj.length ∧ Z.getD p 0 ≠ 0
  | 0, q, ts, o, _, h => absurd (by simp [e47, bnew]) h
  | k + 1, q, [], o, tr, _ => by
    have e : q = Cj.length := tr
    subst e
    rw [← bsize_gw, e47_e B S hJ hl k Z o]
    exact ⟨by simp [ats, wordsFrom], fun p hp => by simp [ats, tgs] at hp⟩
  | k + 1, q, T :: ts, o, tr, h => by
    obtain ⟨hlt, h0, h37, hmk, tr'⟩ := tr
    by_cases h48 : e48 (gw Cj) (bsize (gw Cj)) Z q.toUInt64 (candC (Cj.drop q)) = 0
    · exact absurd (e47_f B S hJ hl k q Z o hlt h48) h
    · obtain ⟨T', hmk', htk, -, -, -, hal, h36, htg, h40⟩ := S _ h0 Cj hJ hl q hlt rfl h37
      have eT : T' = T := Option.some.inj (hmk'.symm.trans hmk)
      subst eT
      have hjl : T'.j.length ≤ Cj.length - q := by
        have := congrArg List.length htk
        rw [List.length_take, List.length_drop] at this
        omega
      have es := e47_s B S hJ hl k q Z o hlt h48
      rw [h36, tU_add (by omega), h40 Z o] at es
      rw [es] at h ⊢
      have hlen : (o ++ (T'.a (zpi Z) q o.length).map Nat.toUInt64).length = o.length + T'.alen := by
        rw [List.length_append, List.length_map, NTm.a_len]
      obtain ⟨ew, tg⟩ := pass2 Z k (q + T'.j.length) ts _ tr' h
      rw [hlen] at ew
      refine ⟨?_, ?_⟩
      · rw [ew, ats_cons]
        simp only [wordsFrom, List.map_append, List.append_assoc]
      · intro p hp
        rw [ats_cons] at hp
        simp only [tgs, List.mem_append] at hp
        rcases hp with hp | hp
        · obtain ⟨hp62, he⟩ := htg p hp
          exact tgt_of_e48 B S hJ hl Z q p _ hp62 he h48
        · exact tg p hp

/-- the atoms of a trace are `ok` and kill nothing -/
theorem tr_all : ∀ (ts : List NTm) (q : Nat), Tr Cj q ts →
    ∀ T ∈ ts, T.ok = true ∧ T.kills 5 = false ∧ T.kills 6 = false
  | [], _, _, T, hT => by simp at hT
  | T0 :: ts, q, tr, T, hT => by
    obtain ⟨hlt, h0, h37, hmk, tr'⟩ := tr
    obtain ⟨T', hmk', -, hok, k5, k6, -, -, -, -⟩ := S _ h0 Cj hJ hl q hlt rfl h37
    have eT : T' = T0 := Option.some.inj (hmk'.symm.trans hmk)
    subst eT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact ⟨hok, k5, k6⟩
    · exact tr_all ts _ tr' T hT

/-- the spec's parse follows the trace -/
theorem atomize_tr : ∀ (ts : List NTm) (q k : Nat), Tr Cj q ts → Cj.length - q ≤ k →
    atomize k (Cj.drop q) = some ts
  | [], q, k, tr, _ => by
    have e : q = Cj.length := tr
    subst e
    rw [List.drop_length]
    cases k <;> rfl
  | T0 :: ts, q, k, tr, hk => by
    obtain ⟨hlt, h0, h37, hmk, tr'⟩ := tr
    obtain ⟨T', hmk', htk, -, -, -, -, -, -, -⟩ := S _ h0 Cj hJ hl q hlt rfl h37
    have eT : T' = T0 := Option.some.inj (hmk'.symm.trans hmk)
    subst eT
    have hjl : T'.j.length ≤ Cj.length - q := by
      have := congrArg List.length htk
      rw [List.length_take, List.length_drop] at this
      omega
    have hjp := T'.j_pos
    have ih := atomize_tr ts (q + T'.j.length) (k - 1) tr' (by omega)
    have ed : (Cj.drop q).drop T'.j.length = Cj.drop (q + T'.j.length) := by
      rw [List.drop_drop]
      first | rfl | (congr 1; omega)
    cases hd : Cj.drop q with
    | nil =>
      have := congrArg List.length hd
      rw [List.length_drop] at this
      simp at this
      omega
    | cons i l' =>
      rw [hd] at hmk' htk ed
      cases k with
      | zero => omega
      | succ k' =>
        simp only [atomize, cand]
        rw [hmk']
        simp only []
        rw [if_pos htk, ed]
        have ih' : atomize k' (Cj.drop (q + T'.j.length)) = some ts := ih
        rw [ih']
        rfl

/-- **the core theorem**: a non-empty result of the translator on Gen's words is the specification encoder's words -/
theorem e64_core (hne : e64 (gw Cj) ≠ []) :
    ∃ ts, atomize Cj.length Cj = some ts ∧ NChk (ats ts) ∧ e64 (gw Cj) = (wordsOf (ats ts)).map Nat.toUInt64 := by
  rw [e64_eq] at hne ⊢
  by_cases c1 : (bsize (gw Cj) == 0) = true
  · rw [if_pos c1] at hne; exact absurd rfl hne
  rw [if_neg c1] at hne ⊢
  by_cases c2 : 262144 < bsize (gw Cj)
  · rw [if_pos c2] at hne; exact absurd rfl hne
  rw [if_neg c2] at hne ⊢
  by_cases c3 : (bsize (e46 16777216 (gw Cj) (bsize (gw Cj)) 0 (e44 16777216 bnew (bsize (gw Cj))) bnew).1 == 0) = true
  · rw [if_pos c3] at hne; exact absurd rfl hne
  rw [if_neg c3] at hne ⊢
  have hZ0 : e44 16777216 bnew (bsize (gw Cj)) = List.replicate (Cj.length + 1) 0 := by
    rw [bsize_gw]
    exact e44_rep Cj.length (by omega) 16777216 0 (by omega) (by omega)
  rw [hZ0] at hne c3 ⊢
  have hz : (e46 16777216 (gw Cj) (bsize (gw Cj)) (0 : Nat).toUInt64 (List.replicate (Cj.length + 1) 0) bnew).1 ≠ [] :=
    fun e => c3 (by
      have e' : (e46 16777216 (gw Cj) (bsize (gw Cj)) 0 (List.replicate (Cj.length + 1) 0) bnew).1 = [] := e
      rw [e']; rfl)
  obtain ⟨ts, tr, zl, za, zb, sz⟩ := pass1 B S hJ hl 16777216 0 (List.replicate (Cj.length + 1) 0) bnew
    (Nat.zero_le _) (List.length_replicate ..) (Nat.zero_le _) hz
  have hne' : e47 16777216 (gw Cj) (bsize (gw Cj))
      (e46 16777216 (gw Cj) (bsize (gw Cj)) (0 : Nat).toUInt64 (List.replicate (Cj.length + 1) 0) bnew).1
      (0 : Nat).toUInt64 bnew ≠ [] := hne
  obtain ⟨ew, tg⟩ := pass2 B S hJ hl _ 16777216 0 ts bnew tr hne'
  have sz' : alenL (ats ts) < 2 ^ 18 := by
    have : ([] : Buf).length + alenL (ats ts) < 2 ^ 18 := sz
    simpa using this
  have hvis : ∀ p ∈ tgs (ats ts) 0, ∃ w, (p, w) ∈ bnd (ats ts) 0 0 := by
    intro p hp
    obtain ⟨-, hnz⟩ := tg p hp
    by_cases hb : ∃ w, (p, w) ∈ bnd (ats ts) 0 0
    · exact hb
    · exact absurd ((zb p (fun w hw => hb ⟨w, hw⟩)).trans (rep_getD _ _)) hnz
  refine ⟨ts, ?_, ⟨by rw [wordsOf_len]; exact sz', ?_, ?_⟩, ?_⟩
  · have := atomize_tr B S hJ hl ts 0 Cj.length tr (by omega)
    rw [List.drop_zero] at this
    exact this
  · intro x hx
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hok, k5, k6⟩ := tr_all B S hJ hl ts 0 tr T hT
    exact ⟨hok, rfl, rfl, k5, k6⟩
  · intro p hp
    obtain ⟨w, hw⟩ := hvis p hp
    exact List.mem_map.2 ⟨(p, w), hw, rfl⟩
  · have ew' : e47 16777216 (gw Cj) (bsize (gw Cj))
        (e46 16777216 (gw Cj) (bsize (gw Cj)) 0 (List.replicate (Cj.length + 1) 0) bnew).1 0 bnew
        = (wordsFrom (zpi (e46 16777216 (gw Cj) (bsize (gw Cj)) (0 : Nat).toUInt64
            (List.replicate (Cj.length + 1) 0) bnew).1) (ats ts) 0 0).map Nat.toUInt64 := by
      have := ew
      simpa [bnew] using this
    rw [ew']
    congr 1
    unfold wordsOf
    apply wordsFrom_congr
    intro p hp
    obtain ⟨w, hw⟩ := hvis p hp
    have hwle := bnd_le (ats ts) 0 0 p w hw
    have hple : p ≤ Cj.length := (tg p hp).1
    rw [widx_eq hw fun _ h => bnd_fun _ _ _ _ _ _ h hw]
    exact zpi_eq (by rw [zl]; omega) (by rw [zl]; omega) (by omega) (za p w hw)

/-- the translator's words are the specification encoder's -/
theorem e64_natEncJ (hne : e64 (gw Cj) ≠ []) :
    ∃ A : List Nat, natEncJ Cj = some (wordBytes A) ∧ e64 (gw Cj) = A.map Nat.toUInt64 := by
  obtain ⟨ts, hat, hch, hw⟩ := e64_core B S hJ hl hne
  refine ⟨wordsOf (ats ts), ?_, hw⟩
  unfold natEncJ
  rw [hat]
  show (if NChk (ats ts) then some (wordBytes (wordsOf (ats ts))) else none) = _
  rw [if_pos hch]

end

end JT

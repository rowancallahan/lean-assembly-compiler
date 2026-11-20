/- Bridge of the nano v2 parser (Nano/V2S/Parse.lean): `p2bV_eq : p2bV xs = stage2b xs` for every input of length
< 2^32. -/
import Legacy.Nano.V2S.Parse
import Legacy.Nano.V2S.LexProof

namespace Nano.V2S.ParseP
open Nano Nano.B Nano.PB Nano.PS Nano.V2S Nano.V2S.InlP Nano.V2S.LexP

/-! ## identifiers in the tag format -/

/-- an identifier's bytes after its tag are well formed: `[1, c]` pairs, then `0` -/
def wfL : List UInt8 → Bool
  | b :: r => if b = 0 then true else if b = 1 then (match r with | _ :: r' => wfL r' | [] => false) else false
  | [] => false

/-- its characters -/
def nmL : List UInt8 → List UInt8
  | b :: c :: r => if b = 1 then c :: nmL r else []
  | _ => []

/-- its length (up to and including the `0`) -/
def ilen : List UInt8 → Nat
  | b :: c :: r => if b = 1 then ilen r + 2 else 1
  | _ => 1

theorem decT2_id : ∀ (l acc : List UInt8), decT2 l (some acc) =
    if wfL l then consO (.id (acc.reverse ++ nmL l)) (decT2 (l.drop (ilen l)) none) else none
  | [], acc => by simp [decT2, wfL]
  | [b], acc => by
    by_cases h0 : b = 0
    · subst h0; simp [wfL, nmL, ilen, dI0]
    · by_cases h1 : b = 1
      · subst h1; rw [decT2.eq_def]; simp [wfL]
      · rw [decT2.eq_def]; simp [wfL, h0, h1]
  | b :: c :: r, acc => by
    by_cases h0 : b = 0
    · subst h0; simp [wfL, nmL, ilen, dI0]
    · by_cases h1 : b = 1
      · subst h1
        rw [dI1, decT2_id r (c :: acc)]
        simp [wfL, nmL, ilen]
      · rw [decT2.eq_def]; simp [wfL, h0, h1]

theorem wfL_ne (b : UInt8) (r : List UInt8) (h0 : ¬ b = 0) (h1 : ¬ b = 1) : wfL (b :: r) = false := by
  unfold wfL; simp [h0, h1]

theorem ilen_le : ∀ l : List UInt8, wfL l → ilen l ≤ l.length
  | b :: c :: r, h => by
    unfold wfL at h; unfold ilen
    by_cases h1 : b = 1
    · have := ilen_le r (by simp [h1] at h; by_cases h0 : (1 : UInt8) = 0 <;> simp_all)
      simp [h1]; omega
    · simp [h1]
  | [b], h => by simp [ilen]
  | [], h => by simp [wfL] at h

theorem idV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n q : Nat), q ≤ xs.length →
    xs.length < q + 2 * n → idV n xs q.toUInt64 = if wfL (xs.drop q) then (q + ilen (xs.drop q)).toUInt64 else 0
  | 0, q, h1, h2 => by omega
  | n + 1, q, h1, h2 => by
    unfold idV
    by_cases hl : q < xs.length
    · obtain ⟨b, hb, hd⟩ := byteAt xs hx q hl
      rw [if_pos ((ltL xs q hx h1).mpr hl), hb, hd]
      by_cases h0 : b = 0
      · subst h0; simp only [beqL 0 (nat_lit 0) (by decide), beq_self_eq_true, if_true]
        cases hr : xs.drop (q + 1) with
        | nil => simp [wfL, ilen]
        | cons c r => simp [wfL, ilen]
      · have n0 : (b == 0) = false := by simp [h0]
        rw [beqL b (nat_lit 0) (by decide), n0]; simp only [Bool.false_eq_true, if_false]
        by_cases h1' : b = 1
        · subst h1'
          by_cases hn : q + 1 < xs.length
          · obtain ⟨c, hc, hd2⟩ := byteAt xs hx (q + 1) hn
            have t : ((q + 1).toUInt64 < len xs) = True := propext ⟨fun _ => trivial, fun _ => (ltL xs (q + 1) hx (by omega)).mpr hn⟩
            rw [show q.toUInt64 + 1 = (q + 1).toUInt64 by simp]
            simp only [t, decide_true, beqL 1 (nat_lit 1) (by decide), beq_self_eq_true, Bool.true_and, if_true]
            rw [show q.toUInt64 + 2 = (q + 2).toUInt64 by simp, idV_eq xs hx n (q + 2) (by omega) (by omega), hd2]
            have e : xs.drop (q + 1 + 1) = xs.drop (q + 2) := rfl
            rw [wfL, ilen]
            simp only [e, show ¬ (1 : UInt8) = 0 by decide, if_false, if_true]
            split
            · congr 1; omega
            · rfl
          · have t : ((q + 1).toUInt64 < len xs) = False :=
              propext ⟨fun q' => hn ((ltL xs (q + 1) hx (by omega)).mp q'), False.elim⟩
            rw [show q.toUInt64 + 1 = (q + 1).toUInt64 by simp]
            simp only [t, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
            rw [show xs.drop (q + 1) = [] by simp; omega, wfL]; simp
        · rw [if_neg (by simp [beqL b (nat_lit 1) (by decide), h1'])]
          rw [wfL_ne b _ h0 h1']; rfl
    · rw [if_neg (fun q' => hl ((ltL xs q hx h1).mp q')), show xs.drop q = [] by simp; omega]; simp [wfL]

theorem wfL_cases : ∀ l : List UInt8, wfL l = true →
    (∃ r, l = 0 :: r) ∨ (∃ c r, l = 1 :: c :: r ∧ wfL r = true)
  | b :: r, h => by
    by_cases h0 : b = 0
    · exact Or.inl ⟨r, by rw [h0]⟩
    · by_cases h1 : b = 1
      · subst h1
        match r, h with
        | c :: r', h => exact Or.inr ⟨c, r', rfl, by unfold wfL at h; simpa using h⟩
        | [], h => simp [wfL] at h
      · rw [wfL_ne b r h0 h1] at h; cases h
  | [], h => by simp [wfL] at h

theorem drop_cons2 (xs : List UInt8) (a : Nat) (u c : UInt8) (r : List UInt8) (h : xs.drop a = u :: c :: r) :
    xs.drop (a + 2) = r := by
  rw [← List.drop_drop, h]; rfl

theorem rd_of_drop (xs : List UInt8) (hx : xs.length < 2 ^ 32) (a : Nat) (u : UInt8) (r : List UInt8)
    (h : xs.drop a = u :: r) : rd xs a.toUInt64 = u.toUInt64 := by
  have hl : a < xs.length := by
    have := congrArg List.length h; simp at this; omega
  rw [rdN xs a hl hx]
  have := List.drop_eq_getElem_cons hl
  rw [h] at this; injection this with h1; rw [h1]

theorem nmEq_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n a b : Nat), wfL (xs.drop a) = true →
    wfL (xs.drop b) = true → xs.length < a + 2 * n →
    nmEq n xs a.toUInt64 b.toUInt64 = if nmL (xs.drop a) = nmL (xs.drop b) then 1 else 0
  | 0, a, b, ha, hb, hn => by
    have : a < xs.length := by
      cases hd : xs.drop a with
      | nil => rw [hd] at ha; simp [wfL] at ha
      | cons _ _ => have := congrArg List.length hd; simp at this; omega
    omega
  | n + 1, a, b, ha, hb, hn => by
    unfold nmEq
    rcases wfL_cases _ ha with ⟨ra, hra⟩ | ⟨ca, ra, hra, wa⟩ <;>
      rcases wfL_cases _ hb with ⟨rb, hrb⟩ | ⟨cb, rb, hrb, wb⟩
    · rw [rd_of_drop xs hx a _ _ hra, rd_of_drop xs hx b _ _ hrb, hra, hrb]
      cases ra <;> cases rb <;> simp [nmL]
    · rw [rd_of_drop xs hx a _ _ hra, rd_of_drop xs hx b _ _ hrb, hra, hrb]
      cases ra <;> simp [nmL]
    · rw [rd_of_drop xs hx a _ _ hra, rd_of_drop xs hx b _ _ hrb, hra, hrb]
      cases rb <;> simp [nmL]
    · have a1 : xs.drop (a + 1) = ca :: ra := by rw [← List.drop_drop, hra]; rfl
      have b1 : xs.drop (b + 1) = cb :: rb := by rw [← List.drop_drop, hrb]; rfl
      have hl : a + 2 ≤ xs.length := by have := congrArg List.length hra; simp at this; omega
      rw [rd_of_drop xs hx a _ _ hra, rd_of_drop xs hx b _ _ hrb, show a.toUInt64 + 1 = (a + 1).toUInt64 by simp,
        show b.toUInt64 + 1 = (b + 1).toUInt64 by simp, rd_of_drop xs hx _ _ _ a1, rd_of_drop xs hx _ _ _ b1,
        show a.toUInt64 + 2 = (a + 2).toUInt64 by simp, show b.toUInt64 + 2 = (b + 2).toUInt64 by simp]
      have IH := nmEq_eq xs hx n (a + 2) (b + 2) (by rw [drop_cons2 xs a _ _ _ hra]; exact wa)
        (by rw [drop_cons2 xs b _ _ _ hrb]; exact wb) (by omega)
      rw [IH, drop_cons2 xs a _ _ _ hra, drop_cons2 xs b _ _ _ hrb, hra, hrb]
      simp only [nmL, if_true, List.cons.injEq, beq_self_eq_true, Bool.true_and, if_true]
      by_cases hc : ca = cb
      · subst hc; simp
      · have : (ca.toUInt64 == cb.toUInt64) = false := by
          simp; intro e; exact hc (UInt8.toUInt64_inj.mp e)
        simp [this, hc]

/-! ## tokens at a position -/

/-- the token `tok` starts at `p` (tag byte, numeral value, identifier characters) -/
def TokAt (xs : List UInt8) (p : Nat) : Tok → Prop
  | .kdef => rd xs p.toUInt64 = 1 | .klet => rd xs p.toUInt64 = 2
  | .kty b => rd xs p.toUInt64 = (if b then 4 else 3)
  | .num v => rd xs p.toUInt64 = 5 ∧ rdW xs (p.toUInt64 + 1) = v
  | .lp => rd xs p.toUInt64 = 6 | .rp => rd xs p.toUInt64 = 7 | .colon => rd xs p.toUInt64 = 8
  | .assign => rd xs p.toUInt64 = 9 | .plus => rd xs p.toUInt64 = 10 | .minus => rd xs p.toUInt64 = 11
  | .star => rd xs p.toUInt64 = 12 | .semi => rd xs p.toUInt64 = 13
  | .id g => rd xs p.toUInt64 = 14 ∧ wfL (xs.drop (p + 1)) = true ∧ nmL (xs.drop (p + 1)) = g

theorem drop_len (xs : List UInt8) (p : Nat) (b : UInt8) (r : List UInt8) (h : xs.drop p = b :: r) :
    p + 1 + r.length = xs.length := by
  have := congrArg List.length h; simp at this; omega

theorem drop_succ_of (xs : List UInt8) (p : Nat) (b : UInt8) (r : List UInt8) (h : xs.drop p = b :: r) :
    xs.drop (p + 1) = r := by
  rw [← List.drop_drop, h]; rfl

theorem rdW_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) (p : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8)
    (r : List UInt8) (h : xs.drop p = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r) :
    rdW xs p.toUInt64 = w4 b0 b1 b2 b3 + 4294967296 * w4 b4 b5 b6 b7 := by
  have g : ∀ k (u : UInt8) (r' : List UInt8), xs.drop (p + k) = u :: r' → rd xs (p.toUInt64 + k.toUInt64) = u.toUInt64 :=
    fun k u r' h' => by rw [toU_add]; exact rd_of_drop xs hx _ _ _ h'
  have d : ∀ k, xs.drop (p + k) = (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r).drop k := fun k => by
    rw [← List.drop_drop, h]
  unfold rdW w4
  rw [rd_of_drop xs hx p b0 _ h,
    show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, g 1 b1 _ (by rw [d]; rfl),
    show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, g 2 b2 _ (by rw [d]; rfl),
    show (3 : UInt64) = (3 : Nat).toUInt64 from rfl, g 3 b3 _ (by rw [d]; rfl),
    show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, g 4 b4 _ (by rw [d]; rfl),
    show (5 : UInt64) = (5 : Nat).toUInt64 from rfl, g 5 b5 _ (by rw [d]; rfl),
    show (6 : UInt64) = (6 : Nat).toUInt64 from rfl, g 6 b6 _ (by rw [d]; rfl),
    show (7 : UInt64) = (7 : Nat).toUInt64 from rfl, g 7 b7 _ (by rw [d]; rfl)]

/-- one step of the token decoder at a token boundary -/
def Step (xs : List UInt8) (n p : Nat) (ts : List Tok) : Prop :=
  (xs.length ≤ p ∧ ts = [] ∧ rd xs p.toUInt64 = 0) ∨
  ∃ tok ts' q, p < q ∧ q ≤ xs.length ∧ ts = tok :: ts' ∧ decT2 (xs.drop q) none = some ts' ∧
    tnx n xs p.toUInt64 = q.toUInt64 ∧ TokAt xs p tok

theorem step_simple (xs : List UInt8) (hx : xs.length < 2 ^ 32) (n p : Nat) (ts : List Tok) (b : UInt8)
    (r : List UInt8) (tok : Tok) (hd : xs.drop p = b :: r) (h5 : b ≠ 5) (h14 : b ≠ 14)
    (hdec : decT2 (b :: r) none = consO tok (decT2 r none)) (h : decT2 (xs.drop p) none = some ts)
    (ht : rd xs p.toUInt64 = b.toUInt64 → TokAt xs p tok) : Step xs n p ts := by
  rw [hd, hdec] at h
  have hl := drop_len xs p b r hd
  have hr := drop_succ_of xs p b r hd
  have hb := rd_of_drop xs hx p b r hd
  cases hrr : decT2 r none with
  | none => rw [hrr] at h; simp [consO] at h
  | some ts' =>
    rw [hrr] at h; simp only [consO, Option.some.injEq] at h
    refine Or.inr ⟨tok, ts', p + 1, by omega, by omega, h.symm, by rw [hr]; exact hrr, ?_, ht hb⟩
    unfold tnx
    rw [hb, beqL b (nat_lit 5) (by decide), beqL b (nat_lit 14) (by decide)]
    simp [h5, h14]

theorem ts_step (xs : List UInt8) (hx : xs.length < 2 ^ 32) (n p : Nat) (ts : List Tok) (hp : p ≤ xs.length)
    (hn : xs.length < p + 2 * n) (h : decT2 (xs.drop p) none = some ts) : Step xs n p ts := by
  cases hd : xs.drop p with
  | nil =>
    rw [hd] at h; simp [decT2] at h
    have : xs.length ≤ p := by have := congrArg List.length hd; simp at this; omega
    refine Or.inl ⟨this, h, ?_⟩
    unfold rd; simp; rw [List.getElem?_eq_none (by omega)]; rfl
  | cons b r =>
    have hb := rd_of_drop xs hx p b r hd
    by_cases e1 : b = 1
    · subst e1; exact step_simple xs hx n p ts 1 r .kdef hd (by decide) (by decide) (dT1 r) h (fun e => e)
    by_cases e2 : b = 2
    · subst e2; exact step_simple xs hx n p ts 2 r .klet hd (by decide) (by decide) (dT2 r) h (fun e => e)
    by_cases e3 : b = 3
    · subst e3; exact step_simple xs hx n p ts 3 r (.kty false) hd (by decide) (by decide) (dT3 r) h (fun e => e)
    by_cases e4 : b = 4
    · subst e4; exact step_simple xs hx n p ts 4 r (.kty true) hd (by decide) (by decide) (dT4 r) h (fun e => e)
    by_cases e6 : b = 6
    · subst e6; exact step_simple xs hx n p ts 6 r .lp hd (by decide) (by decide) (dT6 r) h (fun e => e)
    by_cases e7 : b = 7
    · subst e7; exact step_simple xs hx n p ts 7 r .rp hd (by decide) (by decide) (dT7 r) h (fun e => e)
    by_cases e8 : b = 8
    · subst e8; exact step_simple xs hx n p ts 8 r .colon hd (by decide) (by decide) (dT8 r) h (fun e => e)
    by_cases e9 : b = 9
    · subst e9; exact step_simple xs hx n p ts 9 r .assign hd (by decide) (by decide) (dT9 r) h (fun e => e)
    by_cases e10 : b = 10
    · subst e10; exact step_simple xs hx n p ts 10 r .plus hd (by decide) (by decide) (dT10 r) h (fun e => e)
    by_cases e11 : b = 11
    · subst e11; exact step_simple xs hx n p ts 11 r .minus hd (by decide) (by decide) (dT11 r) h (fun e => e)
    by_cases e12 : b = 12
    · subst e12; exact step_simple xs hx n p ts 12 r .star hd (by decide) (by decide) (dT12 r) h (fun e => e)
    by_cases e13 : b = 13
    · subst e13; exact step_simple xs hx n p ts 13 r .semi hd (by decide) (by decide) (dT13 r) h (fun e => e)
    have hl := drop_len xs p b r hd
    have hr := drop_succ_of xs p b r hd
    by_cases e5 : b = 5
    · subst e5
      match r, hd, hl, hr, h with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r', hd, hl, hr, h =>
        rw [hd, dT5] at h
        have hq : xs.drop (p + 9) = r' := by rw [← List.drop_drop, hd]; rfl
        cases hrr : decT2 r' none with
        | none => rw [hrr] at h; simp [consO] at h
        | some ts' =>
          rw [hrr] at h; simp only [consO, Option.some.injEq] at h
          simp at hl
          refine Or.inr ⟨_, ts', p + 9, by omega, by omega, h.symm, by rw [hq]; exact hrr, ?_, ⟨hb, ?_⟩⟩
          · unfold tnx; rw [hb]; simp
          · rw [show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, rdW_eq xs hx (p + 1) _ _ _ _ _ _ _ _ r' hr]
      | [], hd, _, _, h | [_], hd, _, _, h | [_, _], hd, _, _, h | [_, _, _], hd, _, _, h | [_, _, _, _], hd, _, _, h
      | [_, _, _, _, _], hd, _, _, h | [_, _, _, _, _, _], hd, _, _, h | [_, _, _, _, _, _, _], hd, _, _, h =>
        rw [hd, decT2.eq_def] at h; simp at h
    by_cases e14 : b = 14
    · subst e14
      rw [hd, dT14, decT2_id] at h
      by_cases hw : wfL r = true
      · rw [if_pos hw] at h
        have hil := ilen_le r hw
        cases hrr : decT2 (r.drop (ilen r)) none with
        | none => rw [hrr] at h; simp [consO] at h
        | some ts' =>
          rw [hrr] at h; simp only [consO, Option.some.injEq] at h
          refine Or.inr ⟨_, ts', p + 1 + ilen r, by have := ilen_le r hw; unfold ilen at *; split at * <;> omega, by omega,
            h.symm, by rw [← List.drop_drop, hr]; exact hrr, ?_, ⟨hb, by rw [hr]; exact hw, by rw [hr]; simp⟩⟩
          unfold tnx; rw [hb]; simp only [show ((14 : UInt8).toUInt64 == 5) = false from rfl,
            show ((14 : UInt8).toUInt64 == 14) = true from rfl, Bool.false_eq_true, if_false, if_true]
          rw [show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, idV_eq xs hx n (p + 1) (by omega) (by omega), hr,
            if_pos hw]
      · rw [if_neg hw] at h; cases h
    rw [hd, decT2.eq_def] at h
    simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14] at h

theorem decT2_simple (b : UInt8) (r : List UInt8) (h : (1 ≤ b.toNat ∧ b.toNat ≤ 4) ∨ (6 ≤ b.toNat ∧ b.toNat ≤ 13)) :
    ∃ tok, decT2 (b :: r) none = consO tok (decT2 r none) := by
  have : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 := by
    have t : ∀ k : Nat, k < 256 → b.toNat = k → b = k.toUInt8 := fun k hk e => by
      apply UInt8.toNat_inj.mp; simp; omega
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : b.toNat = 1 ∨ b.toNat = 2 ∨ b.toNat = 3 ∨ b.toNat = 4 := by omega
      rcases this with e | e | e | e
      · exact Or.inl (t 1 (by decide) e)
      · exact Or.inr (Or.inl (t 2 (by decide) e))
      · exact Or.inr (Or.inr (Or.inl (t 3 (by decide) e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t 4 (by decide) e))))
    · have : b.toNat = 6 ∨ b.toNat = 7 ∨ b.toNat = 8 ∨ b.toNat = 9 ∨ b.toNat = 10 ∨ b.toNat = 11 ∨ b.toNat = 12 ∨
        b.toNat = 13 := by omega
      rcases this with e | e | e | e | e | e | e | e
      all_goals (have := t _ (by decide) e; simp only [Nat.toUInt8_eq] at this; subst this; simp)
  rcases this with e | e | e | e | e | e | e | e | e | e | e | e <;> subst e
  all_goals first
    | exact ⟨_, dT1 r⟩ | exact ⟨_, dT2 r⟩ | exact ⟨_, dT3 r⟩ | exact ⟨_, dT4 r⟩ | exact ⟨_, dT6 r⟩
    | exact ⟨_, dT7 r⟩ | exact ⟨_, dT8 r⟩ | exact ⟨_, dT9 r⟩ | exact ⟨_, dT10 r⟩ | exact ⟨_, dT11 r⟩
    | exact ⟨_, dT12 r⟩ | exact ⟨_, dT13 r⟩

theorem isSome_consO (t : Tok) (o : Option (List Tok)) : (consO t o).isSome = o.isSome := by cases o <;> rfl

theorem vld_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n p : Nat), p ≤ xs.length → xs.length < p + n →
    vld n xs p.toUInt64 = if (decT2 (xs.drop p) none).isSome then 1 else 0
  | 0, p, h1, h2 => by omega
  | n + 1, p, h1, h2 => by
    unfold vld
    by_cases hl : p < xs.length
    · obtain ⟨b, hb, hd⟩ := byteAt xs hx p hl
      rw [if_pos ((ltL xs p hx h1).mpr hl), hb, hd]
      simp only [leL b (nat_lit 1) (by decide), leR b (nat_lit 4) (by decide), leL b (nat_lit 6) (by decide),
        leR b (nat_lit 13) (by decide), beqL b (nat_lit 5) (by decide), beqL b (nat_lit 14) (by decide)]
      by_cases hs : (1 ≤ b ∧ b ≤ 4) ∨ (6 ≤ b ∧ b ≤ 13)
      · have hs' : (1 ≤ b.toNat ∧ b.toNat ≤ 4) ∨ (6 ≤ b.toNat ∧ b.toNat ≤ 13) := by
          simp only [UInt8.le_iff_toNat_le] at hs; simpa using hs
        rw [if_pos (by simpa using hs)]
        obtain ⟨tok, ht⟩ := decT2_simple b _ hs'
        rw [ht, isSome_consO, show p.toUInt64 + 1 = (p + 1).toUInt64 by simp,
          vld_eq xs hx n (p + 1) (by omega) (by omega), drop_succ_of xs p b _ hd]
      · rw [if_neg (by simpa using hs)]
        by_cases h5 : b = 5
        · subst h5
          simp only [beq_self_eq_true, if_true]
          by_cases h9 : p + 9 ≤ xs.length
          · have t : (p.toUInt64 + 9 ≤ len xs) = True := propext ⟨fun _ => trivial, fun _ => by
              unfold len; rw [UInt64.le_iff_toNat_le]; simp; omega⟩
            simp only [t, if_true]
            rw [show p.toUInt64 + 9 = (p + 9).toUInt64 by simp,
              vld_eq xs hx n (p + 9) (by omega) (by omega)]
            have hl' := drop_len xs p 5 _ hd
            match hr : xs.drop (p + 1), hd with
            | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r', hd =>
              rw [dT5]
              have : xs.drop (p + 9) = r' := by rw [show p + 9 = (p + 1) + 8 by omega, ← List.drop_drop, hr]; rfl
              rw [isSome_consO, this]
            | [], hd | [_], hd | [_, _], hd | [_, _, _], hd | [_, _, _, _], hd | [_, _, _, _, _], hd
            | [_, _, _, _, _, _], hd | [_, _, _, _, _, _, _], hd =>
              have := drop_len xs p 5 _ hd; simp at this; omega
          · have t : (p.toUInt64 + 9 ≤ len xs) = False := propext ⟨fun q => h9 (by
              unfold len at q; rw [UInt64.le_iff_toNat_le] at q; simp at q; omega), False.elim⟩
            simp only [t, if_false]
            have hl' := drop_len xs p 5 _ hd
            match hr : xs.drop (p + 1), hd with
            | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r', hd =>
              have := congrArg List.length hr; simp at this; omega
            | [], hd | [_], hd | [_, _], hd | [_, _, _], hd | [_, _, _, _], hd | [_, _, _, _, _], hd
            | [_, _, _, _, _, _], hd | [_, _, _, _, _, _, _], hd => rw [decT2.eq_def]; simp
        · have n5 : (b == 5) = false := by simp [h5]
          rw [n5]; simp only [Bool.false_eq_true, if_false]
          by_cases h14 : b = 14
          · subst h14
            simp only [beq_self_eq_true, if_true]
            have hr := drop_succ_of xs p 14 _ hd
            rw [show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, idV_eq xs hx n (p + 1) (by omega) (by omega), hr,
              dT14, decT2_id]
            by_cases hw : wfL (xs.drop (p + 1)) = true
            · have hil := ilen_le _ hw
              have hpos : 1 ≤ ilen (xs.drop (p + 1)) := by
                unfold ilen; split
                · split <;> omega
                · omega
              rw [← hr] at hd ⊢
              rw [if_pos hw, if_pos hw]
              have hne : ((p + 1 + ilen (xs.drop (p + 1))).toUInt64 == 0) = false := by
                simp; intro e; have := congrArg UInt64.toNat e; simp at this; simp at hil; omega
              rw [hne]; simp only [Bool.false_eq_true, if_false]
              simp at hil
              rw [vld_eq xs hx n _ (by omega) (by omega), isSome_consO, List.drop_drop]
            · rw [← hr] at hd ⊢
              rw [if_neg hw, if_neg hw]; simp
          · have n14 : (b == 14) = false := by simp [h14]
            rw [n14]; simp only [Bool.false_eq_true, if_false]
            simp only [UInt8.le_iff_toNat_le] at hs
            rw [decT2.eq_def]
            simp only [UInt8.toNat_ofNat] at hs
            have : ¬ b = 1 ∧ ¬ b = 2 ∧ ¬ b = 3 ∧ ¬ b = 4 ∧ ¬ b = 6 ∧ ¬ b = 7 ∧ ¬ b = 8 ∧ ¬ b = 9 ∧ ¬ b = 10 ∧
                ¬ b = 11 ∧ ¬ b = 12 ∧ ¬ b = 13 := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp at hs)
            obtain ⟨n1, n2, n3, n4, n6, n7, n8, n9, n10, n11, n12, n13⟩ := this
            simp [n1, n2, n3, n4, n6, n7, n8, n9, n10, n11, n12, n13, h5, h14]
    · rw [if_neg (fun q => hl ((ltL xs p hx h1).mp q)), show xs.drop p = [] by simp; omega]; rfl

theorem ntok_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n p c : Nat) (ts : List Tok), p ≤ xs.length →
    xs.length < p + n → decT2 (xs.drop p) none = some ts → c + (xs.length - p) < 2 ^ 32 →
    ntok n xs p.toUInt64 c.toUInt64 = (c + ts.length).toUInt64
  | 0, p, c, ts, h1, h2, _, _ => by omega
  | n + 1, p, c, ts, h1, h2, h, hc => by
    unfold ntok
    by_cases hl : p < xs.length
    · rcases ts_step xs hx n p ts h1 (by omega) h with ⟨hl', -, -⟩ | ⟨tok, ts', q, hpq, hq, hts, hdq, htn, -⟩
      · omega
      · rw [if_pos ((ltL xs p hx h1).mpr hl), htn, show c.toUInt64 + 1 = (c + 1).toUInt64 by simp,
          ntok_eq xs hx n q (c + 1) ts' hq (by omega) hdq (by omega), hts, List.length_cons]
        congr 1; omega
    · rw [if_neg (fun q' => hl ((ltL xs p hx h1).mp q')), show xs.drop p = [] by simp; omega] at *
      simp [decT2] at h; subst h; simp

/-! ## the state relation -/

/-- position `a` holds an identifier token named `g` -/
def NameAt (xs : List UInt8) (a : UInt64) (g : List UInt8) : Prop :=
  a.toNat < xs.length ∧ wfL (xs.drop (a.toNat + 1)) = true ∧ nmL (xs.drop (a.toNat + 1)) = g

/-- the scope buffer holds the scope (pairs, the newest at the end) -/
def ScR (xs : List UInt8) (V : Nat) : List UInt64 → List (List UInt8 × Nat) → Prop
  | S, [] => S = []
  | S, (g, k) :: sc => ∃ S' a, S = S' ++ [a, k.toUInt64] ∧ NameAt xs a g ∧ k ≤ V ∧ ScR xs V S' sc

/-- the def table buffer holds the def table (triples) -/
def DsR (xs : List UInt8) (V : Nat) : List UInt64 → List (List UInt8 × Nat × Nat) → Prop
  | D, [] => D = []
  | D, (g, k, j) :: ds => ∃ D' a, D = D' ++ [a, k.toUInt64, j.toUInt64] ∧ NameAt xs a g ∧ k ≤ V ∧ j ≤ V ∧
      DsR xs V D' ds

/-- a frame as three words -/
def FrR (xs : List UInt8) (V : Nat) (t a b : UInt64) : Fr → Prop
  | .letV f x => t = 1 ∧ a = f.toUInt64 ∧ f ≤ V ∧ NameAt xs b x
  | .letB => t = 2
  | .exprAdd f => t = 3 ∧ a = f.toUInt64 ∧ f ≤ V
  | .addOp f op => t = 4 ∧ a = f.toUInt64 ∧ f ≤ V ∧ b = op.toUInt64
  | .mulT f => t = 5 ∧ a = f.toUInt64 ∧ f ≤ V
  | .mulOp f => t = 6 ∧ a = f.toUInt64 ∧ f ≤ V
  | .call j k => t = 7 ∧ a = j.toUInt64 ∧ b = k.toUInt64 ∧ j ≤ V ∧ k ≤ V
  | .args f k => t = 8 ∧ a = f.toUInt64 ∧ b = k.toUInt64 ∧ f ≤ V ∧ k ≤ V
  | .paren => t = 9

/-- the frame buffer holds the frame stack -/
def KR (xs : List UInt8) (V : Nat) : List UInt64 → List Fr → Prop
  | F, [] => F = []
  | F, fr :: K => ∃ F' t a b, F = F' ++ [t, a, b] ∧ FrR xs V t a b fr ∧ KR xs V F' K ∧ K.length < V

/-- the control -/
def CtlR (V : Nat) (c f x y : UInt64) : Ctl → Prop
  | .defs f' => c = 1 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .params f' n => c = 2 ∧ f = f'.toUInt64 ∧ x = n.toUInt64 ∧ f' ≤ V ∧ n ≤ V
  | .names f' fp n => c = 3 ∧ f = f'.toUInt64 ∧ x = fp.toUInt64 ∧ y = n.toUInt64 ∧ f' ≤ V ∧ fp ≤ V ∧ n ≤ V
  | .dbody => c = 4
  | .expr f' => c = 5 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .add f' => c = 6 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .mul f' => c = 7 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .mulT f' => c = 8 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .app f' => c = 9 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .args f' k => c = 10 ∧ f = f'.toUInt64 ∧ x = k.toUInt64 ∧ f' ≤ V ∧ k ≤ V
  | .atom f' => c = 11 ∧ f = f'.toUInt64 ∧ f' ≤ V
  | .ret => c = 12

/-- **the relation** between the v2 state and the machine's (every number ≤ `V`) -/
def Rel (xs : List UInt8) (V : Nat) (s : PS) (ctl : Ctl) (st : St) : Prop :=
  match s with
  | (c, f, x, y, p, d, na, cg, cf, o, S, D, F) =>
    CtlR V c f x y ctl ∧ p.toNat ≤ xs.length ∧ decT2 (xs.drop p.toNat) none = some st.ts ∧ o = st.out ∧
    d = st.d.toUInt64 ∧ st.d ≤ V ∧ na = st.na.toUInt64 ∧ st.na ≤ V ∧ cf = st.cf.toUInt64 ∧ st.cf ≤ V ∧
    ((∃ f', ctl = .defs f') ∨ NameAt xs cg st.cg) ∧ ScR xs V S st.sc ∧ DsR xs V D st.ds ∧ KR xs V F st.K ∧
    st.sc.length ≤ V ∧ st.ds.length ≤ V

/-! ## buffers -/

theorem bget_app (S T : List UInt64) (i : Nat) (h : i < S.length) (hi : i < 2 ^ 64) :
    bget (S ++ T) i.toUInt64 = bget S i.toUInt64 := by
  unfold bget
  rw [show i.toUInt64.toNat = i by simp; omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem bget_last (S : List UInt64) (T : List UInt64) (i : Nat) (h : i < T.length) (hi : S.length + i < 2 ^ 64) :
    bget (S ++ T) (S.length + i).toUInt64 = T[i] := by
  unfold bget
  rw [show (S.length + i).toUInt64.toNat = S.length + i by simp; omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), h]

theorem ScR_len (xs : List UInt8) (V : Nat) : ∀ (S : List UInt64) (sc : List (List UInt8 × Nat)),
    ScR xs V S sc → S.length = 2 * sc.length
  | S, [], h => by simp [ScR] at h; simp [h]
  | S, (g, k) :: sc, h => by
    obtain ⟨S', a, rfl, -, -, h'⟩ := h
    have := ScR_len xs V S' sc h'; simp; omega

theorem DsR_len (xs : List UInt8) (V : Nat) : ∀ (D : List UInt64) (ds : List (List UInt8 × Nat × Nat)),
    DsR xs V D ds → D.length = 3 * ds.length
  | D, [], h => by simp [DsR] at h; simp [h]
  | D, (g, k, j) :: ds, h => by
    obtain ⟨D', a, rfl, -, -, -, h'⟩ := h
    have := DsR_len xs V D' ds h'; simp; omega

theorem KR_len (xs : List UInt8) (V : Nat) : ∀ (F : List UInt64) (K : List Fr), KR xs V F K → F.length = 3 * K.length
  | F, [], h => by simp [KR] at h; simp [h]
  | F, fr :: K, h => by
    obtain ⟨F', t, a, b, rfl, -, h', -⟩ := h
    have := KR_len xs V F' K h'; simp; omega

theorem lookV_app (xs : List UInt8) : ∀ (n : Nat) (S T : List UInt64) (i : Nat) (g : UInt64), 2 * i ≤ S.length →
    S.length < 2 ^ 40 → lookV n xs (S ++ T) i.toUInt64 g = lookV n xs S i.toUInt64 g
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, S, T, i, g, h, hS => by
    unfold lookV
    by_cases hi : i = 0
    · subst hi; simp
    · have e1 : 2 * i.toUInt64 - 2 = (2 * i - 2).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      have e2 : 2 * i.toUInt64 - 1 = (2 * i - 1).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      have e3 : i.toUInt64 - 1 = (i - 1).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      rw [e1, e2, e3, bget_app S T _ (by omega) (by omega), bget_app S T _ (by omega) (by omega),
        lookV_app xs n S T (i - 1) g (by omega) hS]

theorem findV_app (xs : List UInt8) : ∀ (n : Nat) (D T : List UInt64) (i : Nat) (g : UInt64), 3 * i ≤ D.length →
    D.length < 2 ^ 40 → findV n xs (D ++ T) i.toUInt64 g = findV n xs D i.toUInt64 g
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, D, T, i, g, h, hS => by
    unfold findV
    by_cases hi : i = 0
    · subst hi; simp
    · have e1 : 3 * i.toUInt64 - 3 = (3 * i - 3).toUInt64 := by
        have m : 3 * i % 2 ^ 64 = 3 * i := Nat.mod_eq_of_lt (by omega)
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [m]; omega)]
        simp [m]; omega
      have e3 : i.toUInt64 - 1 = (i - 1).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      rw [e1, e3, bget_app D T _ (by omega) (by omega), findV_app xs n D T (i - 1) g (by omega) hS]

theorem mulsub (k a c : Nat) (hc : c ≤ k * a) :
    (OfNat.ofNat k : UInt64) * a.toUInt64 - (OfNat.ofNat c : UInt64) = (k * a - c).toUInt64 := by
  show UInt64.ofNat k * UInt64.ofNat a - UInt64.ofNat c = UInt64.ofNat (k * a - c)
  rw [UInt64.ofNat_sub hc, UInt64.ofNat_mul]

theorem ms32 (e : Nat) (h : 2 ≤ 3 * e) : 3 * e.toUInt64 - 2 = (3 * e - 2).toUInt64 := mulsub (nat_lit 3) e (nat_lit 2) h
theorem ms31 (e : Nat) (h : 1 ≤ 3 * e) : 3 * e.toUInt64 - 1 = (3 * e - 1).toUInt64 := mulsub (nat_lit 3) e (nat_lit 1) h

theorem nm_eq_iff (xs : List UInt8) (hx : xs.length < 2 ^ 32) (m : Nat) (a g : UInt64) (x gn : List UInt8)
    (ha : NameAt xs a x) (hg : NameAt xs g gn) (hm : xs.length ≤ m) :
    nmEq m xs (a + 1) (g + 1) = if gn = x then 1 else 0 := by
  obtain ⟨ha0, ha1, ha2⟩ := ha
  obtain ⟨hg0, hg1, hg2⟩ := hg
  rw [show a + 1 = (a.toNat + 1).toUInt64 by simp, show g + 1 = (g.toNat + 1).toUInt64 by simp,
    nmEq_eq xs hx m _ _ ha1 hg1 (by omega), ha2, hg2]
  by_cases h : x = gn
  · subst h; simp
  · simp [h, Ne.symm h]

theorem lookV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (g : UInt64)
    (gn : List UInt8) (hg : NameAt xs g gn) : ∀ (sc : List (List UInt8 × Nat)) (S : List UInt64) (n : Nat),
    ScR xs V S sc → sc.length + xs.length ≤ n → sc.length ≤ V →
    lookV n xs S sc.length.toUInt64 g = match lookS gn sc with | some k => (k + 1).toUInt64 | none => 0
  | [], S, n, h, hn, _ => by cases n <;> simp [lookV, lookS]
  | (x, k) :: sc, S, n, h, hn, hl => by
    obtain ⟨S', a, rfl, ha, hk, h'⟩ := h
    have hS := ScR_len xs V S' sc h'
    try simp only [List.length_cons] at hn hl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    unfold lookV
    have ne : ¬ ((sc.length + 1 : Nat).toUInt64 == 0) = true := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp only [List.length_cons]; rw [if_neg ne]
    have e1 : 2 * (sc.length + 1 : Nat).toUInt64 - 2 = (S'.length + 0).toUInt64 := by
      rw [mulsub (nat_lit 2) _ (nat_lit 2) (by simp; omega)]; congr 1; simp; omega
    have e2 : 2 * (sc.length + 1 : Nat).toUInt64 - 1 = (S'.length + 1).toUInt64 := by
      rw [mulsub (nat_lit 2) _ (nat_lit 1) (by simp; omega)]; congr 1; simp; omega
    rw [e1, e2, bget_last S' _ 0 (by simp) (by omega), bget_last S' _ 1 (by simp) (by omega)]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [nm_eq_iff xs hx m a g x gn ha hg (by omega)]
    unfold lookS
    by_cases he : gn = x
    · simp [he]
    · simp only [he, if_false, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true]
      rw [show (sc.length + 1 : Nat).toUInt64 - 1 = sc.length.toUInt64 by simp,
        lookV_app xs m S' _ sc.length g (by omega) (by omega), lookV_eq xs hx V hV g gn hg sc S' m h' (by omega)
          (by omega)]
      simp [he]

theorem findV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (g : UInt64)
    (gn : List UInt8) (hg : NameAt xs g gn) : ∀ (ds : List (List UInt8 × Nat × Nat)) (D : List UInt64) (n : Nat),
    DsR xs V D ds → ds.length + xs.length ≤ n → ds.length ≤ V →
    (findD gn ds = none ∧ findV n xs D ds.length.toUInt64 g = 0) ∨
    (∃ k j e, findD gn ds = some (k, j) ∧ findV n xs D ds.length.toUInt64 g = e.toUInt64 ∧ 1 ≤ e ∧ e ≤ ds.length ∧
      bget D (3 * e.toUInt64 - 2) = k.toUInt64 ∧ bget D (3 * e.toUInt64 - 1) = j.toUInt64 ∧ k ≤ V ∧ j ≤ V)
  | [], D, n, h, hn, _ => by cases n <;> simp [findV, findD]
  | (x, k, j) :: ds, D, n, h, hn, hl => by
    obtain ⟨D', a, rfl, ha, hk, hj, h'⟩ := h
    have hD := DsR_len xs V D' ds h'
    try simp only [List.length_cons] at hn hl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hf : findV (m + 1) xs (D' ++ [a, k.toUInt64, j.toUInt64]) (ds.length + 1 : Nat).toUInt64 g =
        if gn = x then (ds.length + 1 : Nat).toUInt64 else findV m xs D' ds.length.toUInt64 g := by
      conv => lhs; unfold findV
      have ne : ¬ ((ds.length + 1 : Nat).toUInt64 == 0) = true := by
        simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
      rw [if_neg ne]
      have e1 : 3 * (ds.length + 1 : Nat).toUInt64 - 3 = (D'.length + 0).toUInt64 := by
        rw [mulsub (nat_lit 3) _ (nat_lit 3) (by simp; omega)]; congr 1; simp; omega
      rw [e1, bget_last D' _ 0 (by simp) (by omega)]
      simp only [List.getElem_cons_zero]
      simp only [nm_eq_iff xs hx m a g x gn ha hg (by omega)]
      by_cases he : gn = x
      · simp [he]
      · simp only [he, if_false, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true]
        rw [show (ds.length + 1 : Nat).toUInt64 - 1 = ds.length.toUInt64 by simp,
          findV_app xs m D' _ ds.length g (by omega) (by omega)]
    simp only [List.length_cons]
    rw [hf]
    unfold findD
    by_cases he : gn = x
    · simp only [he, if_true, beq_self_eq_true]
      right
      refine ⟨k, j, ds.length + 1, rfl, rfl, by omega, by simp, ?_, ?_, hk, hj⟩
      · rw [show 3 * (ds.length + 1 : Nat).toUInt64 - 2 = (D'.length + 1).toUInt64 by
          rw [mulsub (nat_lit 3) _ (nat_lit 2) (by simp; omega)]; congr 1; simp; omega, bget_last D' _ 1 (by simp) (by omega)]; rfl
      · rw [show 3 * (ds.length + 1 : Nat).toUInt64 - 1 = (D'.length + 2).toUInt64 by
          rw [mulsub (nat_lit 3) _ (nat_lit 1) (by simp; omega)]; congr 1; simp; omega, bget_last D' _ 2 (by simp) (by omega)]; rfl
    · have heq : (gn == x) = false := by simp [he]
      simp only [he, if_false, heq, Bool.false_eq_true]
      rcases findV_eq xs hx V hV g gn hg ds D' m h' (by omega) (by omega) with
        ⟨h1, h2⟩ | ⟨k', j', e, h1, h2, h3, h4, h5, h6, h7, h8⟩
      · exact Or.inl ⟨h1, h2⟩
      · refine Or.inr ⟨k', j', e, h1, h2, h3, by omega, ?_, ?_, h7, h8⟩
        · rw [ms32 e (by omega)] at h5 ⊢
          rw [bget_app D' _ _ (by omega) (by omega), h5]
        · rw [ms31 e (by omega)] at h6 ⊢
          rw [bget_app D' _ _ (by omega) (by omega), h6]

/-! ## the simulation -/

/-- the tag byte of a token -/
def tagT : Tok → UInt64
  | .kdef => 1 | .klet => 2 | .kty b => if b then 4 else 3 | .num _ => 5 | .lp => 6 | .rp => 7 | .colon => 8
  | .assign => 9 | .plus => 10 | .minus => 11 | .star => 12 | .semi => 13 | .id _ => 14

theorem tag_of (xs : List UInt8) (p : Nat) (tok : Tok) (h : TokAt xs p tok) : rd xs p.toUInt64 = tagT tok := by
  cases tok <;> simp only [TokAt] at h <;> first | exact h | exact h.1 | (simp only [tagT]; exact h)

/-- the v2 state `s'` after a step corresponds to the machine's result `r` -/
def Corr (xs : List UInt8) (V : Nat) (s' : PS) : Res → Prop
  | .go c st => Rel xs V s' c st
  | .done o => s'.1 = 0 ∧ s'.2.2.2.2.2.2.2.2.2.1 = o
  | .fail => s'.1 = 13

theorem ScR_mono (xs : List UInt8) (V : Nat) : ∀ S sc, ScR xs V S sc → ScR xs (V + 1) S sc
  | S, [], h => h
  | S, (g, k) :: sc, h => by
    obtain ⟨S', a, h1, h2, h3, h4⟩ := h; exact ⟨S', a, h1, h2, by omega, ScR_mono xs V S' sc h4⟩

theorem DsR_mono (xs : List UInt8) (V : Nat) : ∀ D ds, DsR xs V D ds → DsR xs (V + 1) D ds
  | D, [], h => h
  | D, (g, k, j) :: ds, h => by
    obtain ⟨D', a, h1, h2, h3, h4, h5⟩ := h; exact ⟨D', a, h1, h2, by omega, by omega, DsR_mono xs V D' ds h5⟩

theorem FrR_mono (xs : List UInt8) (V : Nat) (t a b : UInt64) (fr : Fr) (h : FrR xs V t a b fr) :
    FrR xs (V + 1) t a b fr := by
  cases fr with
  | letV f x => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, by omega, h4⟩
  | letB => exact h
  | exprAdd f => obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by omega⟩
  | addOp f op => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, by omega, h4⟩
  | mulT f => obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by omega⟩
  | mulOp f => obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by omega⟩
  | call j k => obtain ⟨h1, h2, h3, h4, h5⟩ := h; exact ⟨h1, h2, h3, by omega, by omega⟩
  | args f k => obtain ⟨h1, h2, h3, h4, h5⟩ := h; exact ⟨h1, h2, h3, by omega, by omega⟩
  | paren => exact h

theorem KR_mono (xs : List UInt8) (V : Nat) : ∀ F K, KR xs V F K → KR xs (V + 1) F K
  | F, [], h => h
  | F, fr :: K, h => by
    obtain ⟨F', t, a, b, h1, h2, h3, h4⟩ := h
    exact ⟨F', t, a, b, h1, FrR_mono xs V t a b fr h2, KR_mono xs V F' K h3, by omega⟩

theorem KR_lenV (xs : List UInt8) (V : Nat) : ∀ F K, KR xs V F K → K.length ≤ V
  | F, [], h => by simp
  | F, fr :: K, h => by obtain ⟨-, -, -, -, -, -, -, h4⟩ := h; simp; omega

theorem toNat_toU' (P : Nat) (h : P < 2 ^ 64) : P.toUInt64.toNat = P := by simp; omega

theorem pstep_1 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (1, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f ≠ 0 && rd xs p == 1 && rd xs (p + 1) == 14 then
        (2, f - 1, 0, y, tnx n xs (p + 1), d, na, p + 1, f - 1, o, [], D, F)
      else (13, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem stepNext (xs : List UInt8) (hx : xs.length < 2 ^ 32) (n P q : Nat) (tok : Tok) (hq : q ≤ xs.length)
    (hpq : P < q)
    (ht : TokAt xs P tok) (htn : tnx n xs P.toUInt64 = q.toUInt64) (h5 : tagT tok ≠ 5) (h14 : tagT tok ≠ 14) :
    q = P + 1 := by
  unfold tnx at htn
  rw [tag_of xs P tok ht] at htn
  have a5 : (tagT tok == 5) = false := by simp [h5]
  have a14 : (tagT tok == 14) = false := by simp [h14]
  rw [a5, a14] at htn; simp only [Bool.false_eq_true, if_false] at htn
  have := congrArg UInt64.toNat htn; simp at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega

theorem sim_defs (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' : Nat)
    (st : St) (h : Rel xs V (1, f, x, y, p, d, na, cg, cf, o, S, D, F) (.defs f') st) :
    Corr xs (V + 1) (pstep n xs (1, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.defs f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, -, hS, hD, hF, hsl, hdl⟩ := h
  subst hf
  have hP : p = p.toNat.toUInt64 := by simp
  generalize p.toNat = P at hp hts hP
  subst hP
  rw [pstep_1]
  simp only [stepS, stDefs]
  cases f' with
  | zero => simp [Corr]
  | succ m =>
    have hne : (m + 1).toUInt64 ≠ 0 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rcases ts_step xs hx n P st.ts hp (by omega) hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', q, hpq, hq, hcons, hq', htn, ht⟩
    · rw [hnil, hr]; simp [Corr]
    · rw [hcons, tag_of xs P tok ht]
      by_cases hk : tok = .kdef
      · subst hk
        have hq1 := stepNext xs hx n P q .kdef hq hpq ht htn (by decide) (by decide)
        subst hq1
        rcases ts_step xs hx n (P + 1) ts' hq (by omega) hq' with ⟨hl2, hnil2, hr2⟩ |
          ⟨tok2, ts'', q2, hpq2, hq2, hcons2, hq2', htn2, ht2⟩
        · rw [hnil2, show P.toUInt64 + 1 = (P + 1).toUInt64 by simp, hr2]; simp [Corr]
        · rw [hcons2, show P.toUInt64 + 1 = (P + 1).toUInt64 by simp, tag_of xs (P + 1) tok2 ht2]
          cases tok2 with
          | id g =>
            simp only [tagT, beq_self_eq_true, Bool.and_true, ne_eq, hne, not_false_eq_true, decide_true, if_true]
            obtain ⟨-, hw, hnm⟩ := ht2
            refine ⟨⟨rfl, by simp, rfl, by omega, by omega⟩, ?_, ?_, ho, hd, by dsimp only; omega, hna,
              by dsimp only; omega, ?_, by dsimp only; omega, Or.inr ⟨?_, ?_, ?_⟩, rfl, DsR_mono xs V D st.ds hD,
              KR_mono xs V F st.K hF, by simp, by dsimp only; omega⟩
            · rw [htn2, toNat_toU' _ (by omega)]; omega
            · rw [htn2, toNat_toU' _ (by omega)]; exact hq2'
            · simp
            · rw [toNat_toU' _ (by omega)]; omega
            · rw [toNat_toU' _ (by omega)]; exact hw
            · rw [toNat_toU' _ (by omega)]; exact hnm
          | kty b => cases b <;> simp [tagT, Corr]
          | _ => simp [tagT, Corr]
      · have : (tagT tok == 1) = false := by
          cases tok with
          | kty b => cases b <;> simp [tagT]
          | _ => simp_all [tagT]
        rw [this]; simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]
        cases tok <;> simp_all [Corr]

/-- the token after a one-byte token -/
theorem next1 (xs : List UInt8) (hx : xs.length < 2 ^ 32) (n P : Nat) (ts : List Tok) (hp : P ≤ xs.length)
    (hn : xs.length < P + 2 * n) (h : decT2 (xs.drop P) none = some ts) :
    (xs.length ≤ P ∧ ts = [] ∧ rd xs P.toUInt64 = 0) ∨
    (∃ tok ts', ts = tok :: ts' ∧ TokAt xs P tok ∧ (tagT tok ≠ 5 → tagT tok ≠ 14 →
      P + 1 ≤ xs.length ∧ decT2 (xs.drop (P + 1)) none = some ts') ∧
      ∃ q, P < q ∧ q ≤ xs.length ∧ decT2 (xs.drop q) none = some ts' ∧ tnx n xs P.toUInt64 = q.toUInt64) := by
  rcases ts_step xs hx n P ts hp hn h with h1 | ⟨tok, ts', q, hpq, hq, hcons, hq', htn, ht⟩
  · exact Or.inl h1
  · refine Or.inr ⟨tok, ts', hcons, ht, fun h5 h14 => ?_, q, hpq, hq, hq', htn⟩
    have := stepNext xs hx n P q tok hq hpq ht htn h5 h14
    subst this; exact ⟨hq, hq'⟩

theorem ne_tag (tok : Tok) (k : UInt64) (h : ∀ b, tok = .kty b → (if b then (4 : UInt64) else 3) ≠ k)
    (h2 : tok ≠ .kty false → tok ≠ .kty true → tagT tok ≠ k) : (tagT tok == k) = false := by
  cases tok with
  | kty b => have := h b rfl; cases b <;> simp_all [tagT]
  | _ => simp only [beq_eq_false_iff_ne]; exact h2 (by simp) (by simp)

theorem pstep_2 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (2, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 6 then (3, f - 1, f - 1, x, p + 1, d, na, cg, cf, o, S, D, F)
      else (4, f, x, y, p, d, x, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem pstep_3 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (3, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 14 then (3, f - 1, x, y + 1, tnx n xs p, d, na, cg, cf, o, bpush (bpush S p) y, D, F)
      else if rd xs p == 8 && (rd xs (p + 1) == 3 || rd xs (p + 1) == 4) && rd xs (p + 2) == 7 then
        (2, x, y, y, p + 3, d, na, cg, cf, o, S, D, F)
      else (13, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem relI (xs : List UInt8) (V : Nat) (c f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (ctl : Ctl) (st : St) (h1 : CtlR V c f x y ctl) (h2 : p.toNat ≤ xs.length)
    (h3 : decT2 (xs.drop p.toNat) none = some st.ts) (h4 : o = st.out) (h5 : d = st.d.toUInt64) (h6 : st.d ≤ V)
    (h7 : na = st.na.toUInt64) (h8 : st.na ≤ V) (h9 : cf = st.cf.toUInt64) (h10 : st.cf ≤ V)
    (h11 : (∃ f', ctl = .defs f') ∨ NameAt xs cg st.cg) (h12 : ScR xs V S st.sc) (h13 : DsR xs V D st.ds)
    (h14 : KR xs V F st.K) (h15 : st.sc.length ≤ V) (h16 : st.ds.length ≤ V) :
    Rel xs V (c, f, x, y, p, d, na, cg, cf, o, S, D, F) ctl st :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem toU1 (P : Nat) : P.toUInt64 + 1 = (P + 1).toUInt64 := by simp

theorem sim_params (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' k : Nat)
    (st : St) (h : Rel xs V (2, f, x, y, p, d, na, cg, cf, o, S, D, F) (.params f' k) st) :
    Corr xs (V + 1) (pstep n xs (2, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.params f' k) st) := by
  obtain ⟨⟨-, hf, hx', hfV, hkV⟩, hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, hcg, hS, hD, hF, hsl, hdl⟩ := h
  have hcg' : NameAt xs cg st.cg := by rcases hcg with ⟨_, h⟩ | h; cases h; exact h
  have hS' := ScR_mono xs V S _ hS
  have hD' := DsR_mono xs V D _ hD
  have hF' := KR_mono xs V F _ hF
  subst hf hx'
  have hP : p = p.toNat.toUInt64 := by simp
  generalize p.toNat = P at hp hts hP
  subst hP
  rw [pstep_2]
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stParams]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have hm1 : (m + 1).toUInt64 - 1 = m.toUInt64 := by simp
    rw [hne]; simp only [Bool.false_eq_true, if_false, hm1]
    have hPt := toNat_toU' P (by omega)
    rcases next1 xs hx n P st.ts hp (by omega) hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, -⟩
    · rw [hr, show stParams (m + 1) k st = Res.go .dbody { st with na := k } by unfold stParams; rw [hnil]]
      simp only [show ((0 : UInt64) == 6) = false from rfl, Bool.false_eq_true, if_false, Corr]
      apply relI
      all_goals first | assumption | exact Or.inr hcg' | rfl | (dsimp only; omega) | (rw [hPt]; assumption)
    · rw [tag_of xs P tok ht]
      by_cases hk : tok = .lp
      · subst hk
        obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
        rw [show stParams (m + 1) k st = Res.go (.names m m k) { st with ts := ts' } by unfold stParams; rw [hcons]]
        simp only [tagT, beq_self_eq_true, if_true, Corr]
        apply relI
        all_goals first | assumption | exact Or.inr hcg' | (dsimp only; omega) | skip
        · exact ⟨rfl, rfl, rfl, rfl, by omega, by omega, by omega⟩
        · rw [toU1, toNat_toU' _ (by omega)]; exact hq
        · rw [toU1, toNat_toU' _ (by omega)]; exact hq'
      · have : (tagT tok == 6) = false := ne_tag tok 6 (fun b _ => by cases b <;> decide) (fun _ _ => by
          cases tok <;> simp_all [tagT])
        rw [this]; simp only [Bool.false_eq_true, if_false]
        rw [show stParams (m + 1) k st = Res.go .dbody { st with na := k } by
          unfold stParams; rw [hcons]; cases tok <;> simp_all]
        simp only [Corr]
        apply relI
        all_goals first | assumption | exact Or.inr hcg' | rfl | (dsimp only; omega) | (rw [hPt]; assumption)

theorem bpush2 (S : List UInt64) (a b : UInt64) : bpush (bpush S a) b = S ++ [a, b] := by simp [bpush]

theorem nameAt_of (xs : List UInt8) (hx : xs.length < 2 ^ 32) (P : Nat) (g : List UInt8) (hP : P < xs.length)
    (ht : TokAt xs P (.id g)) :
    NameAt xs P.toUInt64 g := by
  obtain ⟨-, hw, hn⟩ := ht
  have : P.toUInt64.toNat = P := by simp; omega
  exact ⟨by rw [this]; exact hP, by rw [this]; exact hw, by rw [this]; exact hn⟩

theorem sim_names (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (f' fp k : Nat) (st : St) (h : Rel xs V (3, f, x, y, p, d, na, cg, cf, o, S, D, F) (.names f' fp k) st) :
    Corr xs (V + 1) (pstep n xs (3, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.names f' fp k) st) := by
  obtain ⟨⟨-, hf, hx', hy', hfV, hfpV, hkV⟩, hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, hcg, hS, hD, hF, hsl, hdl⟩ := h
  have hcg' : NameAt xs cg st.cg := by rcases hcg with ⟨_, h⟩ | h; cases h; exact h
  have hS' := ScR_mono xs V S _ hS
  have hD' := DsR_mono xs V D _ hD
  have hF' := KR_mono xs V F _ hF
  subst hf hx' hy'
  have hP : p = p.toNat.toUInt64 := by simp
  generalize p.toNat = P at hp hts hP
  subst hP
  rw [pstep_3]
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stNames]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have hm1 : (m + 1).toUInt64 - 1 = m.toUInt64 := by simp
    rw [hne]; simp only [Bool.false_eq_true, if_false, hm1]
    have hPt := toNat_toU' P (by omega)
    rcases next1 xs hx n P st.ts hp (by omega) hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, q, hpq, hq, hq', htn⟩
    · rw [hr, show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hnil]]
      simp [Corr]
    · rw [tag_of xs P tok ht]
      cases tok with
      | id g =>
        rw [show stNames (m + 1) fp k st = Res.go (.names m fp (k + 1)) { st with ts := ts', sc := (g, k) :: st.sc } by
          unfold stNames; rw [hcons]]
        simp only [tagT, beq_self_eq_true, if_true, Corr, bpush2]
        apply relI
        all_goals first | assumption | exact Or.inr hcg' | rfl | (dsimp only; omega) | (simp; omega) | skip
        · exact ⟨rfl, rfl, rfl, by simp, by omega, by omega, by omega⟩
        · rw [htn, toNat_toU' _ (by omega)]; exact hq
        · rw [htn, toNat_toU' _ (by omega)]; exact hq'
        · exact ⟨S, P.toUInt64, by simp, nameAt_of xs hx P g (by omega) ht, by omega, hS'⟩
      | colon =>
        obtain ⟨hq1, hq1'⟩ := hnx (by decide) (by decide)
        simp only [tagT, beq_self_eq_true, Bool.true_and, show ((8 : UInt64) == 14) = false from rfl,
          Bool.false_eq_true, if_false]
        rcases next1 xs hx n (P + 1) ts' hq1 (by omega) hq1' with ⟨hl2, hnil2, hr2⟩ |
          ⟨tok2, ts2, hcons2, ht2, hnx2, -⟩
        · rw [toU1, hr2, show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons, hnil2]]
          simp [Corr]
        · rw [toU1, tag_of xs (P + 1) tok2 ht2]
          cases tok2 with
          | kty b =>
            obtain ⟨hq2, hq2'⟩ := hnx2 (by cases b <;> decide) (by cases b <;> decide)
            have hb : ((if b = true then (4 : UInt64) else 3) == 3 || (if b = true then (4 : UInt64) else 3) == 4) = true := by
              cases b <;> decide
            simp only [tagT, hb, Bool.true_and]
            rcases next1 xs hx n (P + 1 + 1) ts2 hq2 (by omega) hq2' with ⟨hl3, hnil3, hr3⟩ |
              ⟨tok3, ts3, hcons3, ht3, hnx3, -⟩
            · rw [show P.toUInt64 + 2 = (P + 1 + 1).toUInt64 by rw [show P + 1 + 1 = P + 2 by omega]; simp, hr3,
                show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons, hcons2, hnil3]]
              simp [Corr]
            · rw [show P.toUInt64 + 2 = (P + 1 + 1).toUInt64 by rw [show P + 1 + 1 = P + 2 by omega]; simp, tag_of xs (P + 1 + 1) tok3 ht3]
              cases tok3 with
              | rp =>
                obtain ⟨hq3, hq3'⟩ := hnx3 (by decide) (by decide)
                rw [show stNames (m + 1) fp k st = Res.go (.params fp k) { st with ts := ts3 } by
                  unfold stNames; rw [hcons, hcons2, hcons3]]
                simp only [tagT, beq_self_eq_true, if_true, Corr]
                apply relI
                all_goals first | assumption | exact Or.inr hcg' | rfl | (dsimp only; omega) | (simp; omega) | skip
                · exact ⟨rfl, rfl, rfl, by omega, by omega⟩
                · rw [show P.toUInt64 + 3 = (P + 1 + 1 + 1).toUInt64 by rw [show P + 1 + 1 + 1 = P + 3 by omega]; simp, toNat_toU' _ (by omega)]
                  exact hq3'
              | kty b' => rw [show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons, hcons2, hcons3]]
                          cases b' <;> simp [tagT, Corr]
              | _ => rw [show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons, hcons2, hcons3]]
                     simp [tagT, Corr]
          | _ => rw [show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons, hcons2]]
                 simp [tagT, Corr]
      | kty b => rw [show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons]]
                 cases b <;> simp [tagT, Corr]
      | _ => rw [show stNames (m + 1) fp k st = Res.fail by unfold stNames; rw [hcons]]
             simp [tagT, Corr]

/-! ### shared facts for the remaining cases -/

theorem fpush_eq (F : List UInt64) (t a b : UInt64) : fpush F t a b = F ++ [t, a, b] := by simp [fpush, bpush]

theorem fpop_eq (F : List UInt64) (t a b : UInt64) : fpop (F ++ [t, a, b]) = F := by
  simp [fpop, bpop, List.dropLast_append_cons]

theorem bpop2_eq (S : List UInt64) (a b : UInt64) : bpop (bpop (S ++ [a, b])) = S := by
  simp [bpop, List.dropLast_append_cons]

theorem bsize_div (l : List UInt64) (k m : Nat) (hm : 0 < m) (hm8 : m < 8) (h : l.length = m * k) (hk : k < 2 ^ 32) :
    bsize l / (OfNat.ofNat m : UInt64) = k.toUInt64 := by
  unfold bsize; rw [h]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div]
  show (m * k).toUInt64.toNat / (UInt64.ofNat m).toNat = k.toUInt64.toNat
  simp
  rw [Nat.mod_eq_of_lt (show m * k < 2 ^ 64 by have := Nat.mul_le_mul_right k (show m ≤ 8 by omega); omega),
    Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mul_div_cancel_left k hm

theorem put2_eq (o : List UInt8) (m x : UInt64) : put2 o m x = o ++ [m.toUInt8, x.toUInt8] := by simp [put2, put]

theorem u8_of (k : Nat) : k.toUInt64.toUInt8 = k.toUInt8 := by
  apply UInt8.toNat_inj.mp; simp

theorem u8N_of (k : Nat) : u8N k = k.toUInt8 := u8N_eq k

theorem sat_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : sat a.toUInt64 b.toUInt64 = (a - b).toUInt64 := by
  unfold sat
  by_cases h : b ≤ a
  · rw [if_pos (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    show UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b)
    rw [UInt64.ofNat_sub h]
  · rw [if_neg (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    rw [show a - b = 0 by omega]; rfl

theorem top3 (F : List UInt64) (t a b : UInt64) (hF : F.length + 3 < 2 ^ 64) :
    bget (F ++ [t, a, b]) (bsize (F ++ [t, a, b]) - 3) = t ∧
    bget (F ++ [t, a, b]) (bsize (F ++ [t, a, b]) - 2) = a ∧
    bget (F ++ [t, a, b]) (bsize (F ++ [t, a, b]) - 1) = b := by
  have e : ∀ k, k ≤ 3 → bsize (F ++ [t, a, b]) - (OfNat.ofNat k : UInt64) = (F.length + (3 - k)).toUInt64 := by
    intro k hk
    unfold bsize
    show UInt64.ofNat (F ++ [t, a, b]).length - UInt64.ofNat k = _
    rw [← UInt64.ofNat_sub (by simp; omega)]; congr 1; simp; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [e 3 (by decide), bget_last F _ 0 (by simp) (by omega)]; rfl
  · rw [e 2 (by decide), bget_last F _ 1 (by simp) (by omega)]; rfl
  · rw [e 1 (by decide), bget_last F _ 2 (by simp) (by omega)]; rfl

theorem pstep_4 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (4, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if rd xs p == 8 && (rd xs (p + 1) == 3 || rd xs (p + 1) == 4) && rd xs (p + 2) == 9 then
        (if findV n xs D (bsize D / 3) cg == 0 then (5, cf, x, y, p + 3, na, na, cg, cf, o, S, D, [])
         else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
      else (13, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem sim_dbody (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (hVn : V + xs.length ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (st : St) (h : Rel xs V (4, f, x, y, p, d, na, cg, cf, o, S, D, F) .dbody st) :
    Corr xs (V + 1) (pstep n xs (4, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS .dbody st) := by
  obtain ⟨-, hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, hcg, hS, hD, hF, hsl, hdl⟩ := h
  have hcg' : NameAt xs cg st.cg := by rcases hcg with ⟨_, h⟩ | h; cases h; exact h
  have hS' := ScR_mono xs V S _ hS
  have hD' := DsR_mono xs V D _ hD
  have hP : p = p.toNat.toUInt64 := by simp
  generalize p.toNat = P at hp hts hP
  subst hP
  rw [pstep_4]
  simp only [stepS]
  have hPt := toNat_toU' P (by omega)
  have fail_of : ∀ (h : stDbody st = Res.fail), Corr xs (V + 1) (13, f, x, y, P.toUInt64, d, na, cg, cf, o, S, D, F)
      (stDbody st) := fun h => by rw [h]; rfl
  rcases next1 xs hx n P st.ts hp (by omega) hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, -⟩
  · rw [hr]; exact fail_of (by unfold stDbody; rw [hnil])
  · rw [tag_of xs P tok ht]
    cases tok with
    | colon =>
      obtain ⟨hq1, hq1'⟩ := hnx (by decide) (by decide)
      simp only [tagT, beq_self_eq_true, Bool.true_and]
      rcases next1 xs hx n (P + 1) ts' hq1 (by omega) hq1' with ⟨hl2, hnil2, hr2⟩ | ⟨tok2, ts2, hcons2, ht2, hnx2, -⟩
      · rw [toU1, hr2]; exact fail_of (by unfold stDbody; rw [hcons, hnil2])
      · rw [toU1, tag_of xs (P + 1) tok2 ht2]
        cases tok2 with
        | kty b =>
          obtain ⟨hq2, hq2'⟩ := hnx2 (by cases b <;> decide) (by cases b <;> decide)
          have hb : ((if b = true then (4 : UInt64) else 3) == 3 || (if b = true then (4 : UInt64) else 3) == 4) = true := by
            cases b <;> decide
          simp only [tagT, hb, Bool.true_and]
          have p2 : P.toUInt64 + 2 = (P + 1 + 1).toUInt64 := by rw [show P + 1 + 1 = P + 2 by omega]; simp
          rcases next1 xs hx n (P + 1 + 1) ts2 hq2 (by omega) hq2' with ⟨hl3, hnil3, hr3⟩ | ⟨tok3, ts3, hcons3, ht3, hnx3, -⟩
          · rw [p2, hr3]; exact fail_of (by unfold stDbody; rw [hcons, hcons2, hnil3])
          · rw [p2, tag_of xs (P + 1 + 1) tok3 ht3]
            cases tok3 with
            | assign =>
              obtain ⟨hq3, hq3'⟩ := hnx3 (by decide) (by decide)
              simp only [tagT, beq_self_eq_true, if_true]
              have hsz := bsize_div D st.ds.length 3 (by decide) (by decide) (DsR_len xs V D _ hD) (by omega)
              rw [hsz]
              rcases findV_eq xs hx V hV cg st.cg hcg' st.ds D n hD (by omega) hdl with ⟨hf1, hf2⟩ |
                ⟨k, j, e, hf1, hf2, he1, he2, -⟩
              · rw [hf2, show stDbody st = Res.go (.expr st.cf) { st with ts := ts3, d := st.na, K := [] } by
                  unfold stDbody; rw [hcons, hcons2, hcons3]; simp [hf1]]
                simp only [beq_self_eq_true, if_true, Corr]
                apply relI
                all_goals first | assumption | exact Or.inr hcg' | rfl | (dsimp only; omega) | (simp; omega) | skip
                · exact ⟨rfl, hcf, by omega⟩
                · rw [show P.toUInt64 + 3 = (P + 1 + 1 + 1).toUInt64 by rw [show P + 1 + 1 + 1 = P + 3 by omega]; simp,
                    toNat_toU' _ (by omega)]; exact hq3'
              · have hne : (e.toUInt64 == 0) = false := by
                  simp; intro e'; have := congrArg UInt64.toNat e'; simp at this; omega
                rw [hf2, hne]; simp only [Bool.false_eq_true, if_false]
                exact fail_of (by unfold stDbody; rw [hcons, hcons2, hcons3]; simp [hf1])
            | kty b' => cases b' <;> simp only [tagT] <;> exact fail_of (by unfold stDbody; rw [hcons, hcons2, hcons3])
            | _ => simp only [tagT]; exact fail_of (by unfold stDbody; rw [hcons, hcons2, hcons3])
        | _ => simp only [tagT]; exact fail_of (by unfold stDbody; rw [hcons, hcons2])
    | kty b => cases b <;> simp only [tagT] <;> exact fail_of (by unfold stDbody; rw [hcons])
    | _ => simp only [tagT]; exact fail_of (by unfold stDbody; rw [hcons])

theorem pstep_6 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (6, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 10 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 4 (f - 1) 24)
      else if rd xs p == 11 then (7, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 4 (f - 1) 32)
      else (12, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem pstep_7 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (7, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else (9, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 5 (f - 1) 0) := by
  simp only [pstep]; rfl

theorem pstep_8 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (8, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 12 then (9, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 6 (f - 1) 0)
      else (12, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem pstep_10 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (10, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if x == 0 then (12, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 8 (f - 1) (x - 1)) := by
  simp only [pstep]; rfl

/-- the hypotheses every case starts from -/
structure Hyp (xs : List UInt8) (V : Nat) (P : Nat) (d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (st : St) : Prop where
  hp : P ≤ xs.length
  hts : decT2 (xs.drop P) none = some st.ts
  ho : o = st.out
  hd : d = st.d.toUInt64
  hdV : st.d ≤ V
  hna : na = st.na.toUInt64
  hnaV : st.na ≤ V
  hcf : cf = st.cf.toUInt64
  hcfV : st.cf ≤ V
  hcg : NameAt xs cg st.cg
  hS : ScR xs V S st.sc
  hD : DsR xs V D st.ds
  hF : KR xs V F st.K
  hsl : st.sc.length ≤ V
  hdl : st.ds.length ≤ V

theorem hyp_of (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (c f x y p d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (ctl : Ctl) (st : St) (h : Rel xs V (c, f, x, y, p, d, na, cg, cf, o, S, D, F) ctl st)
    (hc : ∀ f', ctl ≠ .defs f') :
    CtlR V c f x y ctl ∧ p = p.toNat.toUInt64 ∧ Hyp xs V p.toNat d na cg cf o S D F st := by
  obtain ⟨h1, hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, hcg, hS, hD, hF, hsl, hdl⟩ := h
  have hcg' : NameAt xs cg st.cg := by rcases hcg with ⟨f', h⟩ | h; exact absurd h (hc f'); exact h
  exact ⟨h1, by simp, ⟨hp, hts, ho, hd, hdV, hna, hnaV, hcf, hcfV, hcg', hS, hD, hF, hsl, hdl⟩⟩

/-- the same state, control `ret` (`.go .ret s`) -/
theorem rel_ret (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V P : Nat) (f x y d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (st : St) (H : Hyp xs V P d na cg cf o S D F st) :
    Rel xs (V + 1) (12, f, x, y, P.toUInt64, d, na, cg, cf, o, S, D, F) .ret st := by
  have hPt := toNat_toU' P (by have := H.hp; omega)
  exact ⟨rfl, by rw [hPt]; exact H.hp, by rw [hPt]; exact H.hts, H.ho, H.hd, by have := H.hdV; omega, H.hna,
    by have := H.hnaV; omega, H.hcf, by have := H.hcfV; omega, Or.inr H.hcg, ScR_mono xs V S _ H.hS,
    DsR_mono xs V D _ H.hD, KR_mono xs V F _ H.hF, by have := H.hsl; omega, by have := H.hdl; omega⟩

/-- a new control and frame, same cursor (`p` = `q`) -/
theorem rel_push (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V P q : Nat) (c f x y t a b d na cg cf : UInt64)
    (o : List UInt8) (S D F : List UInt64) (st : St) (ctl : Ctl) (fr : Fr) (ts : List Tok)
    (H : Hyp xs V P d na cg cf o S D F st) (hc : CtlR (V + 1) c f x y ctl) (hq : q ≤ xs.length)
    (hts : decT2 (xs.drop q) none = some ts) (hfr : FrR xs (V + 1) t a b fr) (hnd : ∀ f', ctl ≠ .defs f') :
    Rel xs (V + 1) (c, f, x, y, q.toUInt64, d, na, cg, cf, o, S, D, F ++ [t, a, b]) ctl
      { st with ts := ts, K := fr :: st.K } := by
  have hPt := toNat_toU' q (by omega)
  exact ⟨hc, by rw [hPt]; exact hq, by rw [hPt]; exact hts, H.ho, H.hd, by dsimp only; have := H.hdV; omega, H.hna,
    by dsimp only; have := H.hnaV; omega, H.hcf, by dsimp only; have := H.hcfV; omega, Or.inr H.hcg, ScR_mono xs V S _ H.hS,
    DsR_mono xs V D _ H.hD, ⟨F, t, a, b, rfl, hfr, KR_mono xs V F _ H.hF, by have := KR_lenV xs V F _ H.hF; omega⟩, by dsimp only; have := H.hsl; omega,
    by dsimp only; have := H.hdl; omega⟩

theorem sim_mul (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' : Nat) (st : St)
    (h : Rel xs V (7, f, x, y, p, d, na, cg, cf, o, S, D, F) (.mul f') st) :
    Corr xs (V + 1) (pstep n xs (7, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.mul f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_7]
  simp only [stepS, stMul]
  cases f' with
  | zero => simp [Corr]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp, fpush_eq, Corr]
    exact rel_push xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.app m) (.mulT m) st.ts H ⟨rfl, rfl, by omega⟩ H.hp
      H.hts ⟨rfl, rfl, by omega⟩ (by intro _ e; cases e)

theorem sim_mulT (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' : Nat)
    (st : St) (h : Rel xs V (8, f, x, y, p, d, na, cg, cf, o, S, D, F) (.mulT f') st) :
    Corr xs (V + 1) (pstep n xs (8, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.mulT f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_8]
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stMulT]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp, fpush_eq]
    rcases next1 xs hx n _ st.ts H.hp (by omega) H.hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, -⟩
    · rw [hr, show stMulT (m + 1) st = Res.go .ret st by unfold stMulT; rw [hnil]]
      exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H
    · rw [tag_of xs _ tok ht]
      cases tok with
      | star =>
        obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
        rw [show stMulT (m + 1) st = Res.go (.app m) { st with ts := ts', K := .mulOp m :: st.K } by
          unfold stMulT; rw [hcons]]
        simp only [tagT, beq_self_eq_true, if_true, Corr, toU1]
        exact rel_push xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.app m) (.mulOp m) ts' H ⟨rfl, rfl, by omega⟩ hq hq'
          ⟨rfl, rfl, by omega⟩ (by intro _ e; cases e)
      | kty b =>
        rw [show stMulT (m + 1) st = Res.go .ret st by unfold stMulT; rw [hcons]]
        cases b <;> simp only [tagT] <;> exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H
      | _ =>
        rw [show stMulT (m + 1) st = Res.go .ret st by unfold stMulT; rw [hcons]]
        simp only [tagT]; exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H

theorem sim_add (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' : Nat)
    (st : St) (h : Rel xs V (6, f, x, y, p, d, na, cg, cf, o, S, D, F) (.add f') st) :
    Corr xs (V + 1) (pstep n xs (6, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.add f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_6]
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stAdd]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp, fpush_eq]
    rcases next1 xs hx n _ st.ts H.hp (by omega) H.hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, -⟩
    · rw [hr, show stAdd (m + 1) st = Res.go .ret st by unfold stAdd; rw [hnil]]
      exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H
    · rw [tag_of xs _ tok ht]
      cases tok with
      | plus =>
        obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
        rw [show stAdd (m + 1) st = Res.go (.mul m) { st with ts := ts', K := .addOp m 24 :: st.K } by
          unfold stAdd; rw [hcons]]
        simp only [tagT, beq_self_eq_true, if_true, Corr, toU1]
        exact rel_push xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.mul m) (.addOp m 24) ts' H ⟨rfl, rfl, by omega⟩
          hq hq' ⟨rfl, rfl, by omega, rfl⟩ (by intro _ e; cases e)
      | minus =>
        obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
        rw [show stAdd (m + 1) st = Res.go (.mul m) { st with ts := ts', K := .addOp m 32 :: st.K } by
          unfold stAdd; rw [hcons]]
        simp only [tagT, show ((11 : UInt64) == 10) = false from rfl, beq_self_eq_true, Bool.false_eq_true, if_false,
          if_true, Corr, toU1]
        exact rel_push xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.mul m) (.addOp m 32) ts' H ⟨rfl, rfl, by omega⟩
          hq hq' ⟨rfl, rfl, by omega, rfl⟩ (by intro _ e; cases e)
      | kty b =>
        rw [show stAdd (m + 1) st = Res.go .ret st by unfold stAdd; rw [hcons]]
        cases b <;> simp only [tagT] <;> exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H
      | _ =>
        rw [show stAdd (m + 1) st = Res.go .ret st by unfold stAdd; rw [hcons]]
        simp only [tagT]; exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H

theorem sim_args (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' k : Nat) (st : St)
    (h : Rel xs V (10, f, x, y, p, d, na, cg, cf, o, S, D, F) (.args f' k) st) :
    Corr xs (V + 1) (pstep n xs (10, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.args f' k) st) := by
  obtain ⟨⟨-, hf, hx', hfV, hkV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf hx'; rw [hP, pstep_10]
  simp only [stepS, stArgs]
  cases f' with
  | zero => simp [Corr]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp, fpush_eq]
    cases k with
    | zero => simp only [show ((0 : Nat).toUInt64 == 0) = true from rfl, if_true]
              exact rel_ret xs hx V _ _ _ _ _ _ _ _ _ _ _ _ st H
    | succ j =>
      have hne' : ((j + 1).toUInt64 == 0) = false := by
        simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
      rw [hne']; simp only [Bool.false_eq_true, if_false, show (j + 1).toUInt64 - 1 = j.toUInt64 by simp, Corr]
      exact rel_push xs hx V _ p.toNat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.atom m) (.args m j) st.ts H
        ⟨rfl, rfl, by omega⟩ H.hp H.hts ⟨rfl, rfl, rfl, by omega, by omega⟩ (by intro _ e; cases e)

theorem pstep_5 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (5, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 2 && rd xs (p + 1) == 14 && rd xs (tnx n xs (p + 1)) == 9 then
        (5, f - 1, x, y, tnx n xs (p + 1) + 1, d, na, cg, cf, o, S, D, fpush F 1 (f - 1) (p + 1))
      else (7, f - 1, x, y, p, d, na, cg, cf, o, S, D, fpush F 3 (f - 1) 0) := by
  simp only [pstep]; rfl

theorem sim_expr (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (f' : Nat)
    (st : St) (h : Rel xs V (5, f, x, y, p, d, na, cg, cf, o, S, D, F) (.expr f') st) :
    Corr xs (V + 1) (pstep n xs (5, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.expr f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_5]
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stExpr]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp, fpush_eq]
    have hmul : ∀ (hst : stExpr (m + 1) st = Res.go (.mul m) { st with K := .exprAdd m :: st.K }),
        Corr xs (V + 1) (7, m.toUInt64, x, y, p.toNat.toUInt64, d, na, cg, cf, o, S, D, F ++ [3, m.toUInt64, 0])
          (stExpr (m + 1) st) := fun hst => by
      rw [hst]
      exact rel_push xs hx V _ p.toNat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.mul m) (.exprAdd m) st.ts H
        ⟨rfl, rfl, by omega⟩ H.hp H.hts ⟨rfl, rfl, by omega⟩ (by intro _ e; cases e)
    have P0 := H.hp
    rcases next1 xs hx n _ st.ts H.hp (by omega) H.hts with ⟨hl, hnil, hr⟩ | ⟨tok, ts', hcons, ht, hnx, -⟩
    · rw [hr]; simp only [show ((0 : UInt64) == 2) = false from rfl, Bool.false_and, Bool.false_eq_true, if_false]
      exact hmul (by unfold stExpr; rw [hnil])
    · rw [tag_of xs _ tok ht]
      cases tok with
      | klet =>
        obtain ⟨hq1, hq1'⟩ := hnx (by decide) (by decide)
        simp only [tagT, beq_self_eq_true, Bool.true_and]
        rcases next1 xs hx n _ ts' hq1 (by omega) hq1' with ⟨hl2, hnil2, hr2⟩ |
          ⟨tok2, ts2, hcons2, ht2, -, q2, hpq2, hq2, hq2', htn2⟩
        · rw [toU1, hr2]; simp only [show ((0 : UInt64) == 14) = false from rfl, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact hmul (by unfold stExpr; rw [hcons, hnil2])
        · rw [toU1, tag_of xs _ tok2 ht2]
          cases tok2 with
          | id g =>
            simp only [tagT, beq_self_eq_true, Bool.true_and]
            rw [htn2]
            rcases next1 xs hx n q2 ts2 hq2 (by omega) hq2' with ⟨hl3, hnil3, hr3⟩ | ⟨tok3, ts3, hcons3, ht3, hnx3, -⟩
            · rw [hr3]; simp only [show ((0 : UInt64) == 9) = false from rfl, Bool.false_eq_true, if_false]
              exact hmul (by unfold stExpr; rw [hcons, hcons2, hnil3])
            · rw [tag_of xs _ tok3 ht3]
              cases tok3 with
              | assign =>
                obtain ⟨hq3, hq3'⟩ := hnx3 (by decide) (by decide)
                simp only [tagT, beq_self_eq_true, if_true, toU1]
                rw [show stExpr (m + 1) st = Res.go (.expr m) { st with ts := ts3, K := .letV m g :: st.K } by
                  unfold stExpr; rw [hcons, hcons2, hcons3]]
                exact rel_push xs hx V _ (q2 + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.expr m) (.letV m g) ts3 H
                  ⟨rfl, rfl, by omega⟩ hq3 hq3' ⟨rfl, rfl, by omega, nameAt_of xs hx _ g (by omega) ht2⟩
                  (by intro _ e; cases e)
              | kty b =>
                cases b <;> simp only [tagT] <;> exact hmul (by unfold stExpr; rw [hcons, hcons2, hcons3])
              | _ => simp only [tagT]; exact hmul (by unfold stExpr; rw [hcons, hcons2, hcons3])
          | kty b => cases b <;> simp only [tagT] <;> exact hmul (by unfold stExpr; rw [hcons, hcons2])
          | _ => simp only [tagT]; exact hmul (by unfold stExpr; rw [hcons, hcons2])
      | kty b => cases b <;> simp only [tagT] <;> exact hmul (by unfold stExpr; rw [hcons])
      | _ => simp only [tagT]; exact hmul (by unfold stExpr; rw [hcons])

theorem stId_eq (n : Nat) (xs : List UInt8) (f a : UInt64) (c f0 x y p d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) : stId n xs f a (c, f0, x, y, p, d, na, cg, cf, o, S, D, F) =
      if lookV n xs S (bsize S / 2) p ≠ 0 then
        (12, f0, x, y, tnx n xs p, d + 1, na, cg, cf,
          put2 (put2 o 7 (sat (sat d 1) (lookV n xs S (bsize S / 2) p - 1))) 3 0, S, D, F)
      else if findV n xs D (bsize D / 3) p == 0 then (13, f0, x, y, p, d, na, cg, cf, o, S, D, F)
      else if a == 1 then
        (if bget D (3 * findV n xs D (bsize D / 3) p - 2) == 0 then
          (12, f0, x, y, tnx n xs p, d + 1, na, cg, cf, putCall o (bget D (3 * findV n xs D (bsize D / 3) p - 1)) 0,
            S, D, F)
         else (13, f0, x, y, p, d, na, cg, cf, o, S, D, F))
      else (10, f, bget D (3 * findV n xs D (bsize D / 3) p - 2), y, tnx n xs p, d, na, cg, cf, o, S, D,
        fpush F 7 (bget D (3 * findV n xs D (bsize D / 3) p - 1)) (bget D (3 * findV n xs D (bsize D / 3) p - 2))) := by
  simp only [stId]

theorem sVar_out (o : List UInt8) (d k : Nat) (hd : d < 2 ^ 40) (hk : k < 2 ^ 40) :
    put2 (put2 o 7 (sat (sat d.toUInt64 1) ((k + 1).toUInt64 - 1))) 3 0 = o ++ sVarS d k := by
  rw [show (k + 1).toUInt64 - 1 = k.toUInt64 by simp, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl,
    sat_eq d 1 (by omega) (by omega), sat_eq _ k (by omega) (by omega)]
  simp [put2_eq, sVarS, mo, u8_of, u8N_of, subN_eq]

theorem call_out (o : List UInt8) (j k : Nat) :
    putCall o j.toUInt64 k.toUInt64 = o ++ sCallS j k := by
  simp only [putCall, put2_eq, sCallS, mo, natW_eq, u8N_of, u8_of, List.append_assoc, List.cons_append,
    List.nil_append]; rfl

/-- what `app` does on an identifier -/
def appRes (m : Nat) (g : List UInt8) (ts : List Tok) (st : St) : Res :=
  match lookS g st.sc with
  | some k => .go .ret { st with ts := ts, out := st.out ++ sVarS st.d k, d := st.d + 1 }
  | none =>
    match findD g st.ds with
    | some (k, j) => .go (.args m k) { st with ts := ts, K := .call j k :: st.K }
    | none => .fail

/-- what `atom` does on an identifier -/
def atomRes (g : List UInt8) (ts : List Tok) (st : St) : Res :=
  match lookS g st.sc with
  | some k => .go .ret { st with ts := ts, out := st.out ++ sVarS st.d k, d := st.d + 1 }
  | none =>
    match findD g st.ds with
    | some (k, j) =>
      match k with
      | 0 => .go .ret { st with ts := ts, out := st.out ++ sCallS j 0, d := st.d + 1 }
      | _ + 1 => .fail
    | none => .fail

theorem sim_id (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (hVn : V + xs.length ≤ n) (c f0 x y d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (P q m : Nat) (a : UInt64) (g : List UInt8) (ts : List Tok) (st : St)
    (H : Hyp xs V P d na cg cf o S D F st) (hm : m ≤ V) (ht : TokAt xs P (.id g)) (hPL : P < xs.length)
    (hq : q ≤ xs.length) (hq' : decT2 (xs.drop q) none = some ts) (htn : tnx n xs P.toUInt64 = q.toUInt64)
    (ha : a = 0 ∨ a = 1) :
    Corr xs (V + 1) (stId n xs m.toUInt64 a (c, f0, x, y, P.toUInt64, d, na, cg, cf, o, S, D, F))
      (if a = 1 then atomRes g ts st else appRes m g ts st) := by
  rw [stId_eq]
  have hname := nameAt_of xs hx P g hPL ht
  have hsz := bsize_div S st.sc.length 2 (by decide) (by decide) (ScR_len xs V S _ H.hS) (by have := H.hsl; omega)
  have hsz3 := bsize_div D st.ds.length 3 (by decide) (by decide) (DsR_len xs V D _ H.hD) (by have := H.hdl; omega)
  rw [hsz, hsz3, lookV_eq xs hx V hV _ g hname st.sc S n H.hS (by have := H.hsl; omega) H.hsl, htn]
  have hd := H.hd; have hdV := H.hdV
  subst hd
  cases hl : lookS g st.sc with
  | some k =>
    have hk : k ≤ V := by
      have : ∀ (sc : List (List UInt8 × Nat)) S k, ScR xs V S sc → lookS g sc = some k → k ≤ V := by
        intro sc; induction sc with
        | nil => intro S k _ h; simp [lookS] at h
        | cons e sc ih =>
          intro S k hS h
          obtain ⟨g', k'⟩ := e
          obtain ⟨S', a', -, -, hk', hS'⟩ := hS
          unfold lookS at h
          split at h
          · cases h; exact hk'
          · exact ih S' k hS' h
      exact this st.sc S k H.hS hl
    have hne : (k + 1).toUInt64 ≠ 0 := by intro e; have := congrArg UInt64.toNat e; simp at this; omega
    simp only [ne_eq, hne, not_false_eq_true, if_true]
    have hres : (if a = 1 then atomRes g ts st else appRes m g ts st) =
        .go .ret { st with ts := ts, out := st.out ++ sVarS st.d k, d := st.d + 1 } := by
      rcases ha with rfl | rfl <;> simp [atomRes, appRes, hl]
    rw [hres]; simp only [Corr]
    apply relI
    all_goals first | assumption | exact H.hcg' | exact Or.inr H.hcg | (dsimp only; omega) | skip
    · exact rfl
    · rw [toNat_toU' _ (by omega)]; exact hq
    · rw [toNat_toU' _ (by omega)]; exact hq'
    · rw [H.ho, sVar_out _ _ _ (by omega) (by omega)]
    · simp
    · exact H.hna
    · dsimp only; have := H.hnaV; omega
    · exact H.hcf
    · dsimp only; have := H.hcfV; omega
    · exact ScR_mono xs V S _ H.hS
    · exact DsR_mono xs V D _ H.hD
    · exact KR_mono xs V F _ H.hF
    · dsimp only; have := H.hsl; omega
    · dsimp only; have := H.hdl; omega
  | none =>
    simp only [ne_eq, show ((0 : Nat).toUInt64 : UInt64) = 0 from rfl, not_true_eq_false, if_false]
    rcases findV_eq xs hx V hV _ g hname st.ds D n H.hD (by have := H.hdl; omega) H.hdl with ⟨hf1, hf2⟩ |
      ⟨k, j, e, hf1, hf2, he1, he2, hb1, hb2, hkV, hjV⟩
    · rw [hf2]
      have hres : (if a = 1 then atomRes g ts st else appRes m g ts st) = .fail := by
        rcases ha with rfl | rfl <;> simp [atomRes, appRes, hl, hf1]
      rw [hres]; rfl
    · have hne : (e.toUInt64 == 0) = false := by
        have := H.hdl
        simp; intro e'; have := congrArg UInt64.toNat e'; simp at this; omega
      rw [hf2, hne, hb1, hb2]; simp only [Bool.false_eq_true, if_false]
      rcases ha with rfl | rfl
      · have hres : (if (0 : UInt64) = 1 then atomRes g ts st else appRes m g ts st) =
            .go (.args m k) { st with ts := ts, K := .call j k :: st.K } := by
          simp [appRes, hl, hf1]
        rw [hres]; simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false, Corr, fpush_eq]
        exact rel_push xs hx V P q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.args m k) (.call j k) ts H
          ⟨rfl, rfl, rfl, by omega, by omega⟩ hq hq' ⟨rfl, rfl, rfl, by omega, by omega⟩ (by intro _ e; cases e)
      · rw [if_pos rfl]
        simp only [beq_self_eq_true, if_true]
        cases k with
        | zero =>
          have hres : atomRes g ts st =
              .go .ret { st with ts := ts, out := st.out ++ sCallS j 0, d := st.d + 1 } := by
            simp [atomRes, hl, hf1]
          rw [hres]; simp only [show ((0 : Nat).toUInt64 == 0) = true from rfl, if_true, Corr]
          apply relI
          all_goals first | (dsimp only; omega) | skip
          · exact rfl
          · rw [toNat_toU' _ (by omega)]; exact hq
          · rw [toNat_toU' _ (by omega)]; exact hq'
          · rw [H.ho, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, call_out]
          · simp
          · exact H.hna
          · dsimp only; have := H.hnaV; omega
          · exact H.hcf
          · dsimp only; have := H.hcfV; omega
          · exact Or.inr H.hcg
          · exact ScR_mono xs V S _ H.hS
          · exact DsR_mono xs V D _ H.hD
          · exact KR_mono xs V F _ H.hF
          · dsimp only; have := H.hsl; omega
          · dsimp only; have := H.hdl; omega
        | succ k' =>
          have hres : atomRes g ts st = .fail := by
            simp [atomRes, hl, hf1]
          have hne' : ((k' + 1).toUInt64 == 0) = false := by
            simp; intro e'; have := congrArg UInt64.toNat e'; simp at this; omega
          rw [hres, hne']; rfl

theorem pstep_9 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (9, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 14 then stId n xs (f - 1) 0 (9, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 11 && rd xs (p + 1) == 5 then
        (12, f, x, y, p + 10, d + 1, na, cg, cf, put2 (putLi o (0 - rdW xs (p + 2))) 3 0, S, D, F)
      else (11, f - 1, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem pstep_11 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (11, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if f == 0 then (13, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 5 then
        (12, f, x, y, p + 9, d + 1, na, cg, cf, put2 (putLi o (rdW xs (p + 1))) 3 0, S, D, F)
      else if rd xs p == 14 then stId n xs f 1 (11, f, x, y, p, d, na, cg, cf, o, S, D, F)
      else if rd xs p == 6 then (5, f - 1, x, y, p + 1, d, na, cg, cf, o, S, D, fpush F 9 0 0)
      else (13, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem putLi_eq (o : List UInt8) (v : UInt64) : putLi o v = o ++ sLi v := by
  simp [putLi, put2_eq, sLi, mo]

/-- a literal: `ret` with `d + 1` and the output extended -/
theorem rel_lit (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V P q : Nat) (f x y d na cg cf : UInt64)
    (o : List UInt8) (S D F : List UInt64) (st : St) (ts : List Tok) (w : List UInt8)
    (H : Hyp xs V P d na cg cf o S D F st) (hq : q ≤ xs.length) (hts : decT2 (xs.drop q) none = some ts) :
    Rel xs (V + 1) (12, f, x, y, q.toUInt64, d + 1, na, cg, cf, o ++ w, S, D, F) .ret
      { st with ts := ts, out := st.out ++ w, d := st.d + 1 } := by
  have hPt := toNat_toU' q (by omega)
  exact ⟨rfl, by rw [hPt]; exact hq, by rw [hPt]; exact hts, by rw [H.ho], by rw [H.hd]; simp,
    by dsimp only; have := H.hdV; omega, H.hna, by dsimp only; have := H.hnaV; omega, H.hcf,
    by dsimp only; have := H.hcfV; omega, Or.inr H.hcg, ScR_mono xs V S _ H.hS, DsR_mono xs V D _ H.hD,
    KR_mono xs V F _ H.hF, by dsimp only; have := H.hsl; omega, by dsimp only; have := H.hdl; omega⟩

theorem sim_app (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (hVn : V + xs.length ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (f' : Nat) (st : St) (h : Rel xs V (9, f, x, y, p, d, na, cg, cf, o, S, D, F) (.app f') st) :
    Corr xs (V + 1) (pstep n xs (9, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.app f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_9]
  generalize p.toNat = P at H
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stApp]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp]
    have hatom : ∀ (hst : stApp (m + 1) st = Res.go (.atom m) st),
        Corr xs (V + 1) (11, m.toUInt64, x, y, P.toUInt64, d, na, cg, cf, o, S, D, F) (stApp (m + 1) st) := fun hst => by
      rw [hst]
      have hPt := toNat_toU' P (by have := H.hp; omega)
      exact ⟨⟨rfl, rfl, by omega⟩, by rw [hPt]; exact H.hp, by rw [hPt]; exact H.hts, H.ho, H.hd,
        by have := H.hdV; omega, H.hna, by have := H.hnaV; omega, H.hcf, by have := H.hcfV; omega, Or.inr H.hcg,
        ScR_mono xs V S _ H.hS, DsR_mono xs V D _ H.hD, KR_mono xs V F _ H.hF, by have := H.hsl; omega,
        by have := H.hdl; omega⟩
    rcases next1 xs hx n _ st.ts H.hp (by have := H.hp; omega) H.hts with ⟨hl, hnil, hr⟩ |
      ⟨tok, ts', hcons, ht, hnx, q, hpq, hq, hq', htn⟩
    · rw [hr]; simp only [show ((0 : UInt64) == 14) = false from rfl, show ((0 : UInt64) == 11) = false from rfl,
        Bool.false_and, Bool.false_eq_true, if_false]
      exact hatom (by unfold stApp; rw [hnil])
    · rw [tag_of xs _ tok ht]
      cases tok with
      | id g =>
        simp only [tagT, beq_self_eq_true, if_true]
        have := sim_id xs hx V hV n hn hVn 9 (m + 1).toUInt64 x y d na cg cf o S D F P q m 0 g ts' st H (by omega) ht
          (by omega) hq hq' htn (Or.inl rfl)
        rw [if_neg (by decide)] at this
        rw [show stApp (m + 1) st = appRes m g ts' st by unfold stApp; rw [hcons]; rfl]
        exact this
      | minus =>
        obtain ⟨hq1, hq1'⟩ := hnx (by decide) (by decide)
        simp only [tagT, show ((11 : UInt64) == 14) = false from rfl, beq_self_eq_true, Bool.true_and,
          Bool.false_eq_true, if_false]
        rcases next1 xs hx n _ ts' hq1 (by omega) hq1' with ⟨hl2, hnil2, hr2⟩ |
          ⟨tok2, ts2, hcons2, ht2, -, q2, hpq2, hq2, hq2', htn2⟩
        · rw [toU1, hr2]; simp only [show ((0 : UInt64) == 5) = false from rfl, Bool.false_eq_true, if_false]
          exact hatom (by unfold stApp; rw [hcons, hnil2])
        · rw [toU1, tag_of xs _ tok2 ht2]
          cases tok2 with
          | num v =>
            simp only [tagT, beq_self_eq_true, if_true]
            obtain ⟨h5, hv⟩ := ht2
            have hq9 : q2 = P + 1 + 9 := by
              unfold tnx at htn2; rw [h5] at htn2; simp at htn2
              have := congrArg UInt64.toNat htn2; simp at this
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
            subst hq9
            have hst : stApp (m + 1) st =
                Res.go .ret { st with ts := ts2, out := st.out ++ (sLi (0 - v) ++ mo 3 0), d := st.d + 1 } := by
              unfold stApp; rw [hcons, hcons2]
            rw [hst]
            rw [show P.toUInt64 + 2 = (P + 1).toUInt64 + 1 by rw [toU1, show P + 1 + 1 = P + 2 by omega]; simp, hv, putLi_eq, put2_eq,
              show P.toUInt64 + 10 = (P + 1 + 9).toUInt64 by rw [show P + 1 + 9 = P + 10 by omega]; simp]
            have := rel_lit xs hx V P (P + 1 + 9) (m + 1).toUInt64 x y d na cg cf o S D F st ts2
              (sLi (0 - v) ++ mo 3 0) H hq2 hq2'
            simpa [mo] using this
          | kty b => cases b <;> simp only [tagT] <;> exact hatom (by unfold stApp; rw [hcons, hcons2])
          | _ => simp only [tagT]; exact hatom (by unfold stApp; rw [hcons, hcons2])
      | kty b => cases b <;> simp only [tagT] <;> exact hatom (by unfold stApp; rw [hcons])
      | _ => simp only [tagT]; exact hatom (by unfold stApp; rw [hcons])

theorem sim_atom (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (hVn : V + xs.length ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8)
    (S D F : List UInt64) (f' : Nat) (st : St) (h : Rel xs V (11, f, x, y, p, d, na, cg, cf, o, S, D, F) (.atom f') st) :
    Corr xs (V + 1) (pstep n xs (11, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS (.atom f') st) := by
  obtain ⟨⟨-, hf, hfV⟩, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  subst hf; rw [hP, pstep_11]
  generalize p.toNat = P at H
  simp only [stepS]
  cases f' with
  | zero => simp [Corr, stAtom]
  | succ m =>
    have hne : ((m + 1).toUInt64 == 0) = false := by
      simp; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    rw [hne]; simp only [Bool.false_eq_true, if_false, show (m + 1).toUInt64 - 1 = m.toUInt64 by simp]
    have hfail : ∀ (hst : stAtom (m + 1) st = Res.fail),
        Corr xs (V + 1) (13, (m + 1).toUInt64, x, y, P.toUInt64, d, na, cg, cf, o, S, D, F) (stAtom (m + 1) st) :=
      fun hst => by rw [hst]; rfl
    rcases next1 xs hx n _ st.ts H.hp (by have := H.hp; omega) H.hts with ⟨hl, hnil, hr⟩ |
      ⟨tok, ts', hcons, ht, hnx, q, hpq, hq, hq', htn⟩
    · rw [hr]; simp only [show ((0 : UInt64) == 5) = false from rfl, show ((0 : UInt64) == 14) = false from rfl,
        show ((0 : UInt64) == 6) = false from rfl, Bool.false_eq_true, if_false]
      exact hfail (by unfold stAtom; rw [hnil])
    · rw [tag_of xs _ tok ht]
      cases tok with
      | num v =>
        simp only [tagT, beq_self_eq_true, if_true]
        obtain ⟨h5, hv⟩ := ht
        have hq9 : q = P + 9 := by
          unfold tnx at htn; rw [h5] at htn; simp at htn
          have := congrArg UInt64.toNat htn; simp at this
          rw [Nat.mod_eq_of_lt (by have := H.hp; omega), Nat.mod_eq_of_lt (by omega)] at this; omega
        subst hq9
        have hst : stAtom (m + 1) st =
            Res.go .ret { st with ts := ts', out := st.out ++ (sLi v ++ mo 3 0), d := st.d + 1 } := by
          unfold stAtom; rw [hcons]
        rw [hst, hv, putLi_eq, put2_eq, show P.toUInt64 + 9 = (P + 9).toUInt64 by simp]
        have := rel_lit xs hx V P (P + 9) (m + 1).toUInt64 x y d na cg cf o S D F st ts' (sLi v ++ mo 3 0) H hq hq'
        simpa [mo] using this
      | id g =>
        simp only [tagT, show ((14 : UInt64) == 5) = false from rfl, beq_self_eq_true, Bool.false_eq_true,
          if_false, if_true]
        have := sim_id xs hx V hV n hn hVn 11 (m + 1).toUInt64 x y d na cg cf o S D F P q (m + 1) 1 g ts' st H
          (by omega) ht (by omega) hq hq' htn (Or.inr rfl)
        rw [if_pos rfl] at this
        rw [show stAtom (m + 1) st = atomRes g ts' st by unfold stAtom; rw [hcons]; rfl]
        exact this
      | lp =>
        obtain ⟨hq1, hq1'⟩ := hnx (by decide) (by decide)
        simp only [tagT, show ((6 : UInt64) == 5) = false from rfl, show ((6 : UInt64) == 14) = false from rfl,
          beq_self_eq_true, Bool.false_eq_true, if_false, if_true, fpush_eq, toU1]
        rw [show stAtom (m + 1) st = Res.go (.expr m) { st with ts := ts', K := .paren :: st.K } by
          unfold stAtom; rw [hcons]]
        exact rel_push xs hx V P (P + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st (.expr m) .paren ts' H ⟨rfl, rfl, by omega⟩
          hq1 hq1' rfl (by intro _ e; cases e)
      | kty b => cases b <;> simp only [tagT] <;> exact hfail (by unfold stAtom; rw [hcons])
      | _ => simp only [tagT]; exact hfail (by unfold stAtom; rw [hcons])

theorem pstep_12 (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) :
    pstep n xs (12, f, x, y, p, d, na, cg, cf, o, S, D, F) =
      if bsize F == 0 then
        (if p < len xs then (1, cf, x, y, p, d, na, cg, cf, put2 o 13 na, S,
            bpush (bpush (bpush D cg) na) (bsize D / 3), F)
         else (0, f, x, y, p, d, na, cg, cf, put2 o 13 na, S, D, F))
      else stRetF n xs (12, f, x, y, p, d, na, cg, cf, o, S, D, F) := by
  simp only [pstep]; rfl

theorem stRetF_eq (n : Nat) (xs : List UInt8) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64)
    (t a b : UInt64) (hF : F.length + 3 < 2 ^ 64) :
    stRetF n xs (12, f, x, y, p, d, na, cg, cf, o, S, D, F ++ [t, a, b]) =
      if t == 1 then
        (if rd xs p == 13 then (5, a, x, y, p + 1, d, na, cg, cf, o, bpush (bpush S b) (sat d 1), D, fpush F 2 0 0)
         else (13, f, x, y, p, d, na, cg, cf, o, S, D, F))
      else if t == 2 then (12, f, x, y, p, sat d 1, na, cg, cf, put2 o 9 1, bpop (bpop S), D, F)
      else if t == 3 then (6, a, x, y, p, d, na, cg, cf, o, S, D, F)
      else if t == 4 then (6, a, x, y, p, sat d 1, na, cg, cf, put2 o 8 b, S, D, F)
      else if t == 5 then (8, a, x, y, p, d, na, cg, cf, o, S, D, F)
      else if t == 6 then (8, a, x, y, p, sat d 1, na, cg, cf, put2 o 8 40, S, D, F)
      else if t == 7 then (12, f, x, y, p, sat (d + 1) b, na, cg, cf, putCall o a b, S, D, F)
      else if t == 8 then (10, a, b, y, p, d, na, cg, cf, o, S, D, F)
      else (if rd xs p == 7 then (12, f, x, y, p + 1, d, na, cg, cf, o, S, D, F)
            else (13, f, x, y, p, d, na, cg, cf, o, S, D, F)) := by
  obtain ⟨h1, h2, h3⟩ := top3 F t a b hF
  simp only [stRetF, h1, h2, h3, fpop_eq]

/-- `ret` into a frame that leaves cursor, scope and table alone -/
theorem rel_frame (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V P : Nat) (c f x y d d' na cg cf : UInt64)
    (o o' : List UInt8) (S D F : List UInt64) (st : St) (K : List Fr) (ctl : Ctl) (dn : Nat) (out' : List UInt8)
    {F0 : List UInt64} (H : Hyp xs V P d na cg cf o S D F0 st) (hK : KR xs V F K) (hc : CtlR (V + 1) c f x y ctl)
    (hnd : ∀ f', ctl ≠ .defs f') (hd' : d' = dn.toUInt64) (hdn : dn ≤ V + 1) (ho : o' = out') :
    Rel xs (V + 1) (c, f, x, y, P.toUInt64, d', na, cg, cf, o', S, D, F) ctl
      { st with out := out', d := dn, K := K } := by
  have hPt := toNat_toU' P (by have := H.hp; omega)
  exact ⟨hc, by rw [hPt]; exact H.hp, by rw [hPt]; exact H.hts, ho, hd', hdn, H.hna, by dsimp only; have := H.hnaV; omega,
    H.hcf, by dsimp only; have := H.hcfV; omega, Or.inr H.hcg, ScR_mono xs V S _ H.hS, DsR_mono xs V D _ H.hD,
    KR_mono xs V F _ hK, by dsimp only; have := H.hsl; omega, by dsimp only; have := H.hdl; omega⟩

theorem sat1 (d : Nat) (hd : d < 2 ^ 40) : sat d.toUInt64 1 = (subN d 1).toUInt64 := by
  rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, sat_eq d 1 (by omega) (by omega), subN_eq]

theorem sim_ret (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (f x y p d na cg cf : UInt64) (o : List UInt8) (S D F : List UInt64) (st : St)
    (h : Rel xs V (12, f, x, y, p, d, na, cg, cf, o, S, D, F) .ret st) :
    Corr xs (V + 1) (pstep n xs (12, f, x, y, p, d, na, cg, cf, o, S, D, F)) (stepS .ret st) := by
  obtain ⟨-, hP, H⟩ := hyp_of xs hx V _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h (by intro _ e; cases e)
  rw [hP, pstep_12]
  generalize p.toNat = P at H
  simp only [stepS, stRet]
  have hFl := KR_len xs V F _ H.hF
  have hd := H.hd; have ho := H.ho
  cases hK : st.K with
  | nil =>
    rw [hK] at hFl
    have hF0 : F = [] := by simp at hFl; exact hFl
    subst hF0
    simp only [show bsize ([] : List UInt64) = 0 from rfl, beq_self_eq_true, if_true]
    unfold endDefS
    rw [H.hna, put2_eq, u8_of, ho]
    cases hts : st.ts with
    | nil =>
      have hl : xs.length ≤ P := by
        have := H.hts; rw [hts] at this
        rcases ts_step xs hx (xs.length + 1) P [] H.hp (by omega) this with ⟨h1, -, -⟩ | ⟨_, _, _, _, _, h, _⟩
        · exact h1
        · cases h
      rw [if_neg (fun q => by have := (ltL xs P hx H.hp).mp q; omega)]
      simp [Corr, mo, u8N_of]
    | cons tok ts' =>
      have hl : P < xs.length := by
        have := H.hts; rw [hts] at this
        rcases ts_step xs hx (xs.length + 1) P _ H.hp (by omega) this with ⟨h1, h2, -⟩ | ⟨_, _, _, h, _, _⟩
        · cases h2
        · omega
      rw [if_pos ((ltL xs P hx H.hp).mpr hl)]
      simp only [Corr]
      have hsz3 := bsize_div D st.ds.length 3 (by decide) (by decide) (DsR_len xs V D _ H.hD) (by have := H.hdl; omega)
      rw [hsz3]
      have hPt := toNat_toU' P (by have := H.hp; omega)
      refine ⟨⟨rfl, H.hcf, by have := H.hcfV; omega⟩, by rw [hPt]; exact H.hp, by rw [hPt, ← hts]; exact H.hts,
        by simp [mo, u8N_of], hd, by dsimp only; have := H.hdV; omega, rfl, by dsimp only; have := H.hnaV; omega, H.hcf,
        by dsimp only; have := H.hcfV; omega, Or.inl ⟨_, rfl⟩, ScR_mono xs V S _ H.hS,
        ⟨D, cg, by simp [bpush], H.hcg, by have := H.hnaV; omega, by have := H.hdl; omega, DsR_mono xs V D _ H.hD⟩,
        by rw [hK]; rfl, by dsimp only; have := H.hsl; omega, by dsimp only; simp; have := H.hdl; omega⟩
  | cons fr K =>
    have hKR := H.hF; rw [hK] at hKR
    obtain ⟨F', t, a, b, rfl, hfr, hK', hKl⟩ := hKR
    have hF'l := KR_len xs V F' K hK'
    have hne : (bsize (F' ++ [t, a, b]) == 0) = false := by
      have hl : (F' ++ [t, a, b]).length = F'.length + 3 := by simp
      unfold bsize; rw [hl, beq_eq_false_iff_ne]
      intro e; have := congrArg UInt64.toNat e; rw [toNat_toU' _ (by omega)] at this; simp at this
    rw [hne]; simp only [Bool.false_eq_true, if_false]
    rw [stRetF_eq n xs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    have hdn := H.hdV
    have HF : Hyp xs V P d na cg cf o S D F' { st with K := K } :=
      ⟨H.hp, H.hts, H.ho, H.hd, H.hdV, H.hna, H.hnaV, H.hcf, H.hcfV, H.hcg, H.hS, H.hD, hK', H.hsl, H.hdl⟩
    have hd1 : sat d 1 = (subN st.d 1).toUInt64 := by rw [hd]; exact sat1 _ (by omega)
    cases fr with
    | letV f' x' =>
      obtain ⟨rfl, rfl, hfV, hnm⟩ := hfr
      simp only [show ((1 : UInt64) == 1) = true from rfl, if_true, retFS]
      rcases next1 xs hx n _ st.ts H.hp (by have := H.hp; omega) H.hts with ⟨hl, hnil, hr⟩ |
        ⟨tok, ts', hcons, ht, hnx, -⟩
      · rw [hr, hnil]; rfl
      · rw [tag_of xs _ tok ht, hcons]
        cases tok with
        | semi =>
          obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
          simp only [tagT, beq_self_eq_true, if_true, Corr, bpush2, fpush_eq, toU1, hd1]
          have hPt := toNat_toU' (P + 1) (by omega)
          refine ⟨⟨rfl, rfl, by omega⟩, by rw [hPt]; exact hq, by rw [hPt]; exact hq', H.ho, hd,
            by dsimp only; have := H.hdV; omega, H.hna, by dsimp only; have := H.hnaV; omega, H.hcf,
            by dsimp only; have := H.hcfV; omega, Or.inr H.hcg,
            ⟨S, b, rfl, hnm, by rw [subN_eq]; omega, ScR_mono xs V S _ H.hS⟩, DsR_mono xs V D _ H.hD,
            ⟨F', 2, 0, 0, rfl, rfl, KR_mono xs V F' K hK', by omega⟩, by dsimp only; simp; have := H.hsl; omega,
            by dsimp only; have := H.hdl; omega⟩
        | kty bb => cases bb <;> rfl
        | _ => rfl
    | letB =>
      obtain rfl := hfr
      simp only [show ((2 : UInt64) == 1) = false from rfl, show ((2 : UInt64) == 2) = true from rfl,
        Bool.false_eq_true, if_false, if_true, retFS, Corr, hd1]
      have hPt := toNat_toU' P (by have := H.hp; omega)
      refine ⟨rfl, by rw [hPt]; exact H.hp, by rw [hPt]; exact H.hts, by rw [H.ho, put2_eq]; rfl, rfl,
        by dsimp only; rw [subN_eq]; omega, H.hna, by dsimp only; have := H.hnaV; omega, H.hcf,
        by dsimp only; have := H.hcfV; omega, Or.inr H.hcg, ?_, DsR_mono xs V D _ H.hD, KR_mono xs V F' K hK',
        by dsimp only; simp; have := H.hsl; omega, by dsimp only; have := H.hdl; omega⟩
      have hS := H.hS
      cases hsc : st.sc with
      | nil => rw [hsc] at hS; simp only [ScR] at hS; subst hS; rfl
      | cons e sc' =>
        rw [hsc] at hS; obtain ⟨g', k'⟩ := e
        obtain ⟨S', a', rfl, -, -, hS'⟩ := hS
        rw [bpop2_eq]; exact ScR_mono xs V S' _ hS'
    | exprAdd f' =>
      obtain ⟨rfl, rfl, hfV⟩ := hfr
      simp only [show ((3 : UInt64) == 1) = false from rfl, show ((3 : UInt64) == 2) = false from rfl,
        show ((3 : UInt64) == 3) = true from rfl, Bool.false_eq_true, if_false, if_true, retFS, Corr]
      exact rel_frame xs hx V P _ _ _ _ d d na cg cf o o S D F' st K (.add f') st.d st.out H HF.hF ⟨rfl, rfl, by omega⟩
        (by intro _ e; cases e) hd (by omega) H.ho
    | addOp f' op =>
      obtain ⟨rfl, rfl, hfV, rfl⟩ := hfr
      simp only [show ((4 : UInt64) == 1) = false from rfl, show ((4 : UInt64) == 2) = false from rfl,
        show ((4 : UInt64) == 3) = false from rfl, show ((4 : UInt64) == 4) = true from rfl, Bool.false_eq_true,
        if_false, if_true, retFS, Corr, hd1]
      exact rel_frame xs hx V P _ _ _ _ d _ na cg cf o _ S D F' st K (.add f') (subN st.d 1) (st.out ++ mo 8 op) H HF.hF
        ⟨rfl, rfl, by omega⟩ (by intro _ e; cases e) rfl (by rw [subN_eq]; omega) (by rw [H.ho, put2_eq]; simp [mo])
    | mulT f' =>
      obtain ⟨rfl, rfl, hfV⟩ := hfr
      simp only [show ((5 : UInt64) == 1) = false from rfl, show ((5 : UInt64) == 2) = false from rfl,
        show ((5 : UInt64) == 3) = false from rfl, show ((5 : UInt64) == 4) = false from rfl,
        show ((5 : UInt64) == 5) = true from rfl, Bool.false_eq_true, if_false, if_true, retFS, Corr]
      exact rel_frame xs hx V P _ _ _ _ d d na cg cf o o S D F' st K (.mulT f') st.d st.out H HF.hF ⟨rfl, rfl, by omega⟩
        (by intro _ e; cases e) hd (by omega) H.ho
    | mulOp f' =>
      obtain ⟨rfl, rfl, hfV⟩ := hfr
      simp only [show ((6 : UInt64) == 1) = false from rfl, show ((6 : UInt64) == 2) = false from rfl,
        show ((6 : UInt64) == 3) = false from rfl, show ((6 : UInt64) == 4) = false from rfl,
        show ((6 : UInt64) == 5) = false from rfl, show ((6 : UInt64) == 6) = true from rfl, Bool.false_eq_true,
        if_false, if_true, retFS, Corr, hd1]
      exact rel_frame xs hx V P _ _ _ _ d _ na cg cf o _ S D F' st K (.mulT f') (subN st.d 1) (st.out ++ mo 8 40) H
        HF.hF ⟨rfl, rfl, by omega⟩ (by intro _ e; cases e) rfl (by rw [subN_eq]; omega) (by rw [H.ho, put2_eq]; rfl)
    | call j k =>
      obtain ⟨rfl, rfl, rfl, hjV, hkV⟩ := hfr
      simp only [show ((7 : UInt64) == 1) = false from rfl, show ((7 : UInt64) == 2) = false from rfl,
        show ((7 : UInt64) == 3) = false from rfl, show ((7 : UInt64) == 4) = false from rfl,
        show ((7 : UInt64) == 5) = false from rfl, show ((7 : UInt64) == 6) = false from rfl,
        show ((7 : UInt64) == 7) = true from rfl, Bool.false_eq_true, if_false, if_true, retFS, Corr]
      exact rel_frame xs hx V P _ _ _ _ d _ na cg cf o _ S D F' st K .ret (subN (st.d + 1) k) (st.out ++ sCallS j k) H
        HF.hF rfl (by intro _ e; cases e)
        (by rw [hd, show st.d.toUInt64 + 1 = (st.d + 1).toUInt64 by simp, sat_eq _ _ (by omega) (by omega), subN_eq])
        (by rw [subN_eq]; omega) (by rw [H.ho, call_out])
    | args f' k =>
      obtain ⟨rfl, rfl, rfl, hfV, hkV⟩ := hfr
      simp only [show ((8 : UInt64) == 1) = false from rfl, show ((8 : UInt64) == 2) = false from rfl,
        show ((8 : UInt64) == 3) = false from rfl, show ((8 : UInt64) == 4) = false from rfl,
        show ((8 : UInt64) == 5) = false from rfl, show ((8 : UInt64) == 6) = false from rfl,
        show ((8 : UInt64) == 7) = false from rfl, show ((8 : UInt64) == 8) = true from rfl, Bool.false_eq_true,
        if_false, if_true, retFS, Corr]
      exact rel_frame xs hx V P _ _ _ _ d d na cg cf o o S D F' st K (.args f' k) st.d st.out H HF.hF
        ⟨rfl, rfl, rfl, by omega, by omega⟩ (by intro _ e; cases e) hd (by omega) H.ho
    | paren =>
      obtain rfl := hfr
      simp only [show ((9 : UInt64) == 1) = false from rfl, show ((9 : UInt64) == 2) = false from rfl,
        show ((9 : UInt64) == 3) = false from rfl, show ((9 : UInt64) == 4) = false from rfl,
        show ((9 : UInt64) == 5) = false from rfl, show ((9 : UInt64) == 6) = false from rfl,
        show ((9 : UInt64) == 7) = false from rfl, show ((9 : UInt64) == 8) = false from rfl, Bool.false_eq_true,
        if_false, retFS]
      rcases next1 xs hx n _ st.ts H.hp (by have := H.hp; omega) H.hts with ⟨hl, hnil, hr⟩ |
        ⟨tok, ts', hcons, ht, hnx, -⟩
      · rw [hr, hnil]; rfl
      · rw [tag_of xs _ tok ht, hcons]
        cases tok with
        | rp =>
          obtain ⟨hq, hq'⟩ := hnx (by decide) (by decide)
          simp only [tagT, beq_self_eq_true, if_true, Corr, toU1]
          have hPt := toNat_toU' (P + 1) (by omega)
          exact ⟨rfl, by rw [hPt]; exact hq, by rw [hPt]; exact hq', H.ho, hd, by dsimp only; omega, H.hna,
            by dsimp only; have := H.hnaV; omega, H.hcf, by dsimp only; have := H.hcfV; omega, Or.inr H.hcg,
            ScR_mono xs V S _ H.hS, DsR_mono xs V D _ H.hD, KR_mono xs V F' K hK',
            by dsimp only; have := H.hsl; omega, by dsimp only; have := H.hdl; omega⟩
        | kty bb => cases bb <;> rfl
        | _ => rfl

/-! ## the run -/

theorem sim (xs : List UInt8) (hx : xs.length < 2 ^ 32) (V : Nat) (hV : V < 2 ^ 32) (n : Nat)
    (hn : 16 * xs.length + 16 ≤ n) (hVn : V + xs.length ≤ n) (s : PS) (ctl : Ctl) (st : St)
    (h : Rel xs V s ctl st) : Corr xs (V + 1) (pstep n xs s) (stepS ctl st) := by
  obtain ⟨c, f, x, y, p, d, na, cg, cf, o, S, D, F⟩ := s
  have hc := h.1
  cases ctl with
  | defs f' => obtain ⟨rfl, -⟩ := hc; exact sim_defs xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | params f' k => obtain ⟨rfl, -⟩ := hc; exact sim_params xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | names f' fp k => obtain ⟨rfl, -⟩ := hc; exact sim_names xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | dbody => obtain rfl := hc; exact sim_dbody xs hx V hV n hn hVn _ _ _ _ _ _ _ _ _ _ _ _ st h
  | expr f' => obtain ⟨rfl, -⟩ := hc; exact sim_expr xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | add f' => obtain ⟨rfl, -⟩ := hc; exact sim_add xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | mul f' => obtain ⟨rfl, -⟩ := hc; exact sim_mul xs hx V hV n _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | mulT f' => obtain ⟨rfl, -⟩ := hc; exact sim_mulT xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | app f' => obtain ⟨rfl, -⟩ := hc; exact sim_app xs hx V hV n hn hVn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | args f' k => obtain ⟨rfl, -⟩ := hc; exact sim_args xs hx V hV n _ _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | atom f' => obtain ⟨rfl, -⟩ := hc; exact sim_atom xs hx V hV n hn hVn _ _ _ _ _ _ _ _ _ _ _ _ _ st h
  | ret => obtain rfl := hc; exact sim_ret xs hx V hV n hn _ _ _ _ _ _ _ _ _ _ _ _ st h

theorem ctl_tag (V : Nat) (c f x y : UInt64) (ctl : Ctl) (h : CtlR V c f x y ctl) : c ≠ 0 ∧ c ≠ 13 := by
  cases ctl <;> simp only [CtlR] at h <;>
    first | (obtain ⟨rfl, -⟩ := h; decide) | (subst h; decide)

theorem prun_eq (xs : List UInt8) (hx : xs.length < 2 ^ 27) (n : Nat) (hn : 16 * xs.length + 16 ≤ n) :
    ∀ (g V : Nat) (s : PS) (ctl : Ctl) (st : St), Rel xs V s ctl st → V + g ≤ 14 * xs.length + 7 →
    prun g n xs s = (runS g ctl st).getD []
  | 0, _, _, _, _, _, _ => rfl
  | g + 1, V, s, ctl, st, h, hg => by
    have hc := sim xs (by omega) V (by omega) n hn (by omega) s ctl st h
    unfold prun runS
    generalize pstep n xs s = s' at hc
    obtain ⟨c, f, x, y, p, d, na, cg, cf, o, S, D, F⟩ := s'
    simp only []
    cases hr : stepS ctl st with
    | go c' st' =>
      rw [hr] at hc
      obtain ⟨h0, h13⟩ := ctl_tag _ _ _ _ _ _ hc.1
      have e0 : (c == 0) = false := by simp [h0]
      have e13 : (c == 13) = false := by simp [h13]
      rw [e0, e13]; simp only [Bool.false_eq_true, if_false]
      exact prun_eq xs hx n hn g (V + 1) _ c' st' hc (by omega)
    | done o' =>
      rw [hr] at hc
      obtain ⟨h0, ho⟩ := hc
      simp only at h0 ho
      subst h0; simp [ho]
    | fail =>
      rw [hr] at hc
      simp only [Corr] at hc
      subst hc; simp

theorem ts_len (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (k p : Nat) (ts : List Tok), xs.length - p ≤ k →
    p ≤ xs.length → decT2 (xs.drop p) none = some ts → ts.length ≤ xs.length - p
  | k, p, ts, hk, hp, h => by
    rcases ts_step xs hx (xs.length + 1) p ts hp (by omega) h with ⟨-, rfl, -⟩ | ⟨tok, ts', q, hpq, hq, rfl, hq', -, -⟩
    · simp
    · have := ts_len xs hx (xs.length - q) q ts' (Nat.le_refl _) hq hq'
      simp; omega
  termination_by k => k
  decreasing_by omega

/-- **the bridge**: the nano v2 source of parser stage 2b is `stage2b`, on every input of length < 2^27 -/
theorem p2bV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 27) : p2bV xs = stage2b xs := by
  unfold p2bV stage2b
  simp only []
  cases xs with
  | nil => simp [rd, decLT]
  | cons b r =>
    have hx' : (b :: r).length < 2 ^ 32 := by omega
    have hxr : r.length < 2 ^ 27 := by simp at hx; omega
    have h0 : rd (b :: r) 0 = b.toUInt64 := by simp [rd]
    have hd1 : (b :: r).drop 1 = r := rfl
    have hv := vld_eq (b :: r) hx' (16 * (b :: r).length + 16) 1 (by simp) (by simp; omega)
    rw [hd1] at hv
    rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl] at *
    rw [h0, hv]
    unfold decLT
    by_cases hb : b = 1 ∨ b = 2
    · cases hdec : decT2 r none with
      | none =>
        have e : ((b.toUInt64 == (1 : Nat).toUInt64 || b.toUInt64 == 2) && (if (none : Option (List Tok)).isSome = true
          then (1 : Nat).toUInt64 else 0) == (1 : Nat).toUInt64) = false := by simp
        rw [e]; rcases hb with rfl | rfl <;> simp [pairO, hdec]
      | some ts =>
        have hl := ts_len (b :: r) hx' _ 1 ts (Nat.le_refl _) (by simp) (by rw [hd1]; exact hdec)
        simp at hl
        have hn := ntok_eq (b :: r) hx' (16 * (b :: r).length + 16) 1 0 ts (by simp) (by simp; omega)
          (by rw [hd1]; exact hdec) (by simp; omega)
        have e : ((b.toUInt64 == (1 : Nat).toUInt64 || b.toUInt64 == 2) && (if (some ts).isSome = true
          then (1 : Nat).toUInt64 else 0) == (1 : Nat).toUInt64) = true := by
          rcases hb with rfl | rfl <;> simp
        rw [e]; simp only [if_true]
        have hrun : (runS (gasS ts) (.defs (ts.length + 1)) ⟨ts, [], 0, [], [], [], [], 0, 0⟩).getD [] =
            prun (13 * (b :: r).length + 6) (16 * (b :: r).length + 16) (b :: r)
              ((1 : Nat).toUInt64, (ts.length + 1).toUInt64, 0, 0, (1 : Nat).toUInt64, 0, 0, 0, 0, [], [], [], []) := by
          rw [prun_eq (b :: r) hx _ (Nat.le_refl _) _ (ts.length + 1) _ (.defs (ts.length + 1))
            ⟨ts, [], 0, [], [], [], [], 0, 0⟩ ?_ (by simp; omega)]
          · rw [runS_eq, runS_eq, gasS_eq]
            have := parseA_gas ts (13 * (b :: r).length + 6 - gasOf ts)
            unfold parseA st0 at this
            rw [show gasOf ts + (13 * (b :: r).length + 6 - gasOf ts) = 13 * (b :: r).length + 6 by
              unfold gasOf; simp; omega] at this
            rw [this]
          · refine ⟨⟨rfl, rfl, by omega⟩, by simp, by simp; exact hdec, rfl, rfl, Nat.zero_le _, rfl, Nat.zero_le _,
              rfl, Nat.zero_le _, Or.inl ⟨_, rfl⟩, rfl, rfl, rfl, by simp, by simp⟩
        have h1 : (0 + ts.length).toUInt64 + (1 : Nat).toUInt64 = (ts.length + 1).toUInt64 := by simp
        have hn' : ntok (16 * (b :: r).length + 16) (b :: r) (Nat.toUInt64 1) 0 = (0 + ts.length).toUInt64 := hn
        rw [hn', h1, ← hrun]
        rcases hb with rfl | rfl <;> simp [pairO, hdec]
    · have e : (b.toUInt64 == (1 : Nat).toUInt64 || b.toUInt64 == 2) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        constructor <;> intro e <;> apply hb
        · left; exact UInt8.toUInt64_inj.mp e
        · right; exact UInt8.toUInt64_inj.mp e
      rw [e]; simp only [Bool.false_and, Bool.false_eq_true, if_false]
      have n1 : (b == 1) = false := by simp; intro e; exact hb (Or.inl e)
      have n2 : (b == 2) = false := by simp; intro e; exact hb (Or.inr e)
      simp [n1, n2]

end Nano.V2S.ParseP

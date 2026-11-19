/- Nano/V2Self/Proof/ParInvArm: Layer-3 handlers for the fuel-loop ARMS (box G, taken over from the parser lead):
task 79 `mkLoop` (v140): the step arm's shape code equals the def's result code, then the LOOP node (tag 10, two children). -/
import Nano.V2Self.Proof.ParInvPair
import Nano.V2Self.Proof.ParInvHdr
import Nano.V2Self.Proof.ParInvNum
namespace ParInv
open C BufL ParSpec ParRun

/-- one code, one optional shape -/
theorem ShOpt.same {h : Buf} {c : UInt64} {o o' : Option Sh} (r : ShOpt h c o) (r' : ShOpt h c o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some s' => simp only [ShOpt] at r r'; subst r; exact absurd rfl r'.ne0
  | some s =>
    cases o' with
    | none => simp only [ShOpt] at r r'; subst r'; exact absurd rfl r.ne0
    | some s' => exact congrArg some (ShapeCode.det r r')

/-! ## task 79: `mkLoop` (v140) -/
theorem h_mkLoop {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.mkLoop :: fs)) (hD : inDefF fs = true)
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .mkLoop st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have ev : step h = (if bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3) then
      v5 g (10 : Nat).toUInt64 (0 : Nat).toUInt64 (0 : Nat).toUInt64 (bget g (d7 + 8 * bget g 12 + 3)) (b01 false) (2 : Nat).toUInt64
      else bset g 0 0) := by rw [E]; simp [v96, v140, b01]
  rw [ev] at hs ⊢
  by_cases c1 : bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3)
  · rw [if_pos c1] at hs ⊢
    have rA := R1.2.2.2.2.2.2.2.1
    have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
    have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← rD.1]; simp
    have hres : ShOpt g (bget g (d7 + 8 * bget g 12 + 3)) st.cur.res := by
      rw [h12]; have := rD.2.2.2.2.1; simp only [if_true] at this; exact this.1.2.2.2.1
    obtain ⟨st', em, R2⟩ := rep_v5 R1 hnf 2 10 0 0 st.cur.res false _ hres (by decide) (by decide) (by decide) (by decide) hs
    obtain ⟨hle, _⟩ := mkNode_inv em
    obtain ⟨s, rest, ev2⟩ : ∃ s rest, st.vals = s :: rest := by
      match hv : st.vals with
      | s :: rest => exact ⟨s, rest, rfl⟩
      | [] => simp [hv] at hle
    have l0 : 0 < st.vals.length := by rw [ev2]; simp
    have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
    simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
    obtain ⟨_, rs⟩ := val_rep rA 0 l0
    have fs' : ShOpt g (bget g (d5 + 8 * opAt g (st.vals.length - 1 - 0) + 3)) (st.vals[0]'l0).sh := rs.fields.2.2.2.1
    rw [← o0, c1] at fs'
    have hsh := ShOpt.same fs' hres
    simp only [ev2, List.getElem_cons_zero] at hsh
    exact ⟨[], st', by simp [stepF, ev2, hsh, em], R2⟩
  · rw [if_neg c1] at hs; exact absurd (stat0 _ (by omega)) hs

/-- the arm flag h[30] -/
theorem rep_arm {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (a : Bool) :
    Rep (bset h 30 (b01 a)) ts { st with arm := a } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have u : (30 : UInt64).toNat = 30 := rfl
  have e : ∀ i : UInt64, i.toNat ≠ 30 → bget (bset h 30 (b01 a)) i = bget h i := fun i a => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 30 (b01 a)) := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree h (bset h 30 (b01 a)) := fun i a _ => e i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [e 0 (by decide)]; exact r0,
    by rw [e 3 (by decide)]; exact tokAt_frame et hn r3, by rw [e 11 (by decide)]; exact r11,
    binds_frame rB (e 4 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    defs_frame rD (e 12 (by decide)) (e 27 (by decide)) (e 26 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
    fun s' hs' => by rw [e 25 (by decide)]; exact (r25 s' hs').frame es,
    fun x hx => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    bget_bset_eq _ _ _ _ rfl (by rw [u]; omega), by rw [e 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (e 5 (by decide)) (fun i _ _ => e i (by omega)) et hn es (fun i a _ => e i (by omega)) har⟩

/-- the state-slot counter h[32] -/
theorem rep_sslot {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (n : Nat) :
    Rep (bset h 32 n.toUInt64) ts { st with sslot := n } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have u : (32 : UInt64).toNat = 32 := rfl
  have e : ∀ i : UInt64, i.toNat ≠ 32 → bget (bset h 32 n.toUInt64) i = bget h i := fun i a => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 32 n.toUInt64) := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree h (bset h 32 n.toUInt64) := fun i a _ => e i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [e 0 (by decide)]; exact r0,
    by rw [e 3 (by decide)]; exact tokAt_frame et hn r3, by rw [e 11 (by decide)]; exact r11,
    binds_frame rB (e 4 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    defs_frame rD (e 12 (by decide)) (e 27 (by decide)) (e 26 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
    fun s' hs' => by rw [e 25 (by decide)]; exact (r25 s' hs').frame es,
    fun x hx => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [e 30 (by decide)]; exact r30, by rw [bget_bset_eq _ _ _ _ rfl (by rw [u]; omega)], out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (e 5 (by decide)) (fun i _ _ => e i (by omega)) et hn es (fun i a _ => e i (by omega)) har⟩

/-- dropping all bindings: h[4] := 0 -/
theorem rep_binds_clear {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs)  :
    Rep (bset h 4 0) ts { st with binds := [] } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have u : (4 : UInt64).toNat = 4 := rfl
  have e : ∀ i : UInt64, i.toNat ≠ 4 → bget (bset h 4 0) i = bget h i := fun i a => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 4 0) := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree h (bset h 4 0) := fun i a _ => e i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [e 0 (by decide)]; exact r0,
    by rw [e 3 (by decide)]; exact tokAt_frame et hn r3, by rw [e 11 (by decide)]; exact r11,
    ⟨by rw [bget_bset_eq _ _ _ _ rfl (by rw [u]; omega)]; rfl, by simp, fun i hi => absurd hi (by simp)⟩,
    defs_frame rD (e 12 (by decide)) (e 27 (by decide)) (e 26 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
    fun s' hs' => by rw [e 25 (by decide)]; exact (r25 s' hs').frame es,
    fun x hx => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [e 30 (by decide)]; exact r30, by rw [e 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (e 5 (by decide)) (fun i _ _ => e i (by omega)) et hn es (fun i a _ => e i (by omega)) har⟩

/-! ## task 77: `zeroDone` (v139), in stages -/
/-- stage 4: `,` then task 76 (step arm, state index 1) with the state-slot counter 1 -/
def zd4 (h : Buf) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == k40 then v1 (bset (bset h 3 (bget h 3 + 1)) 32 1) 76 1 1 else bset h 0 0
/-- stage 3: the numeral 1, arm flag -/
def zd3 (h : Buf) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 5 then
    (if bget (v87 h (bget h 3)) 31 == 1 then zd4 (bset (bset (v87 h (bget h 3)) 3 (bget (v87 h (bget h 3)) 3 + 9)) 30 1)
     else bset (v87 h (bget h 3)) 0 0)
  else bset h 0 0
/-- stage 2: `+` -/
def zd2 (h : Buf) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 10 then zd3 (bset h 3 (bget h 3 + 1)) else bset h 0 0
/-- stage 1: the fuel binder: bindings reset to this one (slot 0, Nat) -/
def zd1 (h : Buf) : Buf :=
  if (bget h (d11 + (bget h 3) + 0)) == 14 then
    zd2 (v6 (bset (v86 16777216 h (bget h 3 + 1)) 4 0) (bget h 3) 0 4)
  else bset h 0 0

theorem v139_eq (g : Buf) (a b : UInt64) : v139 g a b =
    if bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3) then
      (if bget g (d11 + bget g 3) = 18 then zd1 (bset g 3 (bget g 3 + 1)) else bset g 0 0)
    else bset g 0 0 := by
  unfold v139 zd1 zd2 zd3 zd4
  simp [k43]

theorem zd4_ok {h ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (hs : bget (zd4 h) 0 ≠ 0) :
    ∃ r, st.toks = .k 15 :: r ∧ Rep (zd4 h) ts { st with toks := r, sslot := 1 } (.armBind true 1 :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  unfold zd4 at hs ⊢
  simp only [UInt64.add_zero, k40, beq_iff_eq] at hs ⊢
  by_cases c : bget h (d11 + bget h 3) = 15
  · rw [if_pos c] at hs ⊢
    obtain ⟨r, et, tr⟩ := tok_kw R.2.2.2.1 R.1 R.2.1 c (by decide) (by decide) (by decide)
    have R2 := rep_sslot (rep_cursor R (bget h 3 + 1) tr) 1
    exact ⟨r, et, rep_push (.armBind true 1) 1 1 R2 rfl ⟨rfl, rfl⟩ hs⟩
  · rw [if_neg c] at hs; exact absurd (stat0 _ (by omega)) hs

theorem zd4_zero (h : Buf) (hl : 12352 ≤ h.length) (h0 : bget h 0 = 0) : bget (zd4 h) 0 = 0 := by
  unfold zd4
  split
  · exact v1_zero _ _ _ _ (by rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)]; exact h0)
  · exact stat0 _ (by omega)

theorem zd3_zero (h : Buf) (hl : 12352 ≤ h.length) (h0 : bget h 0 = 0) : bget (zd3 h) 0 = 0 := by
  unfold zd3
  split
  · split
    · refine zd4_zero _ (by simp only [length_bset]; unfold v87; simp only [length_bset]; exact hl) ?_
      rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)]
      unfold v87; rw [bget_bset' _ _ _ _ (by decide)]; exact h0
    · exact stat0 _ (by unfold v87; simp only [length_bset]; omega)
  · exact stat0 _ (by omega)

theorem zd2_zero (h : Buf) (hl : 12352 ≤ h.length) (h0 : bget h 0 = 0) : bget (zd2 h) 0 = 0 := by
  unfold zd2
  split
  · exact zd3_zero _ (by simp only [length_bset]; exact hl) (by rw [bget_bset' _ _ _ _ (by decide)]; exact h0)
  · exact stat0 _ (by omega)

theorem zd3_ok {h ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (hs : bget (zd3 h) 0 ≠ 0) :
    ∃ r, st.toks = .num 1 :: .k 15 :: r ∧ Rep (zd3 h) ts { st with toks := r, arm := true, sslot := 1 } (.armBind true 1 :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  unfold zd3 at hs ⊢
  simp only [UInt64.add_zero, beq_iff_eq] at hs ⊢
  by_cases c : bget h (d11 + bget h 3) = 5
  · rw [if_pos c] at hs ⊢
    obtain ⟨v, t4, et⟩ := tok_num R.2.2.2.1 R.1 c
    have r3 := R.2.2.2.1; rw [et] at r3
    obtain ⟨e87, hv, tr, _⟩ := v87_tok r3 hn
    rw [e87] at hs ⊢
    have c31 : ∀ j : UInt64, j.toNat ≠ 31 → bget (bset h 31 v.toUInt64) j = bget h j := fun j a => bget_bset' _ _ _ _ (by simp; omega)
    rw [bb31 h (by omega), c31 3 (by decide)] at hs ⊢
    by_cases c1 : v.toUInt64 = 1
    · rw [if_pos c1] at hs ⊢
      have hv1 : v = 1 := u_one hv (c := 1) (by decide) c1
      subst hv1
      have R2 : Rep (bset h 31 (1 : Nat).toUInt64) ts st fs := rep_scratch R (fun j _ a => c31 j a) (drop_bset _ _ _ (by decide))
      have tr' : TokAt (bset h 31 (1 : Nat).toUInt64) (bget h 3 + 9) t4 :=
        tokAt_frame ⟨c31 7 (by decide), fun j hj => c31 j (by omega)⟩ hn tr
      have R3 := rep_arm (rep_cursor R2 (bget h 3 + 9) tr') true
      obtain ⟨r, et4, R4⟩ := zd4_ok R3 hs
      exact ⟨r, by rw [et]; simp only at et4; rw [et4], R4⟩
    · rw [if_neg c1] at hs; exact absurd (stat0 _ (by simp only [length_bset]; omega)) hs
  · rw [if_neg c] at hs; exact absurd (stat0 _ (by omega)) hs

theorem zd2_ok {h ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (hs : bget (zd2 h) 0 ≠ 0) :
    ∃ r, st.toks = .k 10 :: .num 1 :: .k 15 :: r ∧
      Rep (zd2 h) ts { st with toks := r, arm := true, sslot := 1 } (.armBind true 1 :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  unfold zd2 at hs ⊢
  simp only [UInt64.add_zero, beq_iff_eq] at hs ⊢
  by_cases c : bget h (d11 + bget h 3) = 10
  · rw [if_pos c] at hs ⊢
    obtain ⟨t3, et, tr⟩ := tok_kw R.2.2.2.1 R.1 R.2.1 c (by decide) (by decide) (by decide)
    obtain ⟨r, et3, R3⟩ := zd3_ok (rep_cursor R (bget h 3 + 1) tr) hs
    exact ⟨r, by rw [et]; simp only at et3; rw [et3]; rfl, R3⟩
  · rw [if_neg c] at hs; exact absurd (stat0 _ (by omega)) hs

theorem zd1_ok {h ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (hs : bget (zd1 h) 0 ≠ 0) :
    ∃ nb r, st.toks = .id nb :: .k 10 :: .num 1 :: .k 15 :: r ∧
      Rep (zd1 h) ts { st with toks := r, binds := [⟨nb, 0, some .nt, false⟩], arm := true, sslot := 1 } (.armBind true 1 :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  have rT := R.1
  have h7 : (bget h 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; have := R.2.1; omega
  have p3 := R.2.2.2.1.le
  unfold zd1 at hs ⊢
  simp only [UInt64.add_zero, beq_iff_eq] at hs ⊢
  by_cases c : bget h (d11 + bget h 3) = 14
  · rw [if_pos c] at hs ⊢
    obtain ⟨nm, t2, et, hNm, tr⟩ := tok_id R.2.2.2.1 rT c
    have hskip := v86_skip nm 16777216 h (bget h 3 + 1) hNm.2.1
      (by rw [tn_add _ _ (by simp; omega)]; have := hNm.2.2; simp; omega) (by have := hNm.2.2; omega)
    rw [hskip] at hs ⊢
    have epos : bget h 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget h 3 + 2 + 2 * nm.length.toUInt64 := by
      rw [show (2 : UInt64) = 1 + 1 from rfl]; ac_rfl
    have R2 := rep_binds_clear (rep_cursor R (bget h 3 + 1 + 2 * nm.length.toUInt64 + 1) (by rw [epos]; exact tr))
    generalize hg : bset (bset h 3 (bget h 3 + 1 + 2 * nm.length.toUInt64 + 1)) 4 0 = g at hs R2 ⊢
    have etg : TokAgree h g := by
      rw [← hg]
      exact ⟨by rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)],
        fun j hj => by rw [bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by simp; omega)]⟩
    have hx : NameAt g (bget h 3) (nm.map UInt64.toNat) := nameAt_frame etg (by omega) ⟨nm, hNm, rfl⟩
    have lg : 12352 ≤ g.length := by rw [← hg]; simp only [length_bset]; omega
    have hs6 : bget (v6 g (bget h 3) 0 4) 0 ≠ 0 := fun z => hs (zd2_zero _ (by
      by_cases q : bget g 4 < d14
      · unfold v6; simp only [q, if_true, length_bset]; exact lg
      · unfold v6; simp only [q, if_false, length_bset]; exact lg) z)
    have R3 := rep_v6 R2 (bget h 3) 0 4 (nm.map UInt64.toNat) 0 (some .nt) hx rfl ShapeCode.nt hs6
    obtain ⟨r, et2, R4⟩ := zd2_ok R3 hs
    exact ⟨nm.map UInt64.toNat, r, by rw [et]; simp only at et2; rw [et2], R4⟩
  · rw [if_neg c] at hs; exact absurd (stat0 _ (by omega)) hs

theorem h_zeroDone {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.zeroDone :: fs)) (hD : inDefF fs = true)
    (hv : st.vals ≠ []) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .zeroDone st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have ev : step h = v139 g a b := by rw [E]; simp [v96]
  rw [ev, v139_eq] at hs ⊢
  by_cases c1 : bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3)
  · rw [if_pos c1] at hs ⊢
    have rA := R1.2.2.2.2.2.2.2.1
    have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
    have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← rD.1]; simp
    have hres : ShOpt g (bget g (d7 + 8 * bget g 12 + 3)) st.cur.res := by
      rw [h12]; have := rD.2.2.2.2.1; simp only [if_true] at this; exact this.1.2.2.2.1
    obtain ⟨z, rest, ev2⟩ : ∃ z rest, st.vals = z :: rest := by
      match hv' : st.vals with
      | z :: rest => exact ⟨z, rest, rfl⟩
      | [] => exact absurd hv' hv
    have l0 : 0 < st.vals.length := by rw [ev2]; simp
    have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
    simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
    obtain ⟨_, rs⟩ := val_rep rA 0 l0
    have fz : ShOpt g (bget g (d5 + 8 * opAt g (st.vals.length - 1 - 0) + 3)) (st.vals[0]'l0).sh := rs.fields.2.2.2.1
    rw [← o0, c1] at fz
    have hsh := ShOpt.same fz hres
    simp only [ev2, List.getElem_cons_zero] at hsh
    by_cases c18 : bget g (d11 + bget g 3) = 18
    · rw [if_pos c18] at hs ⊢
      obtain ⟨t1, et, tr⟩ := tok_kw R1.2.2.2.1 R1.1 R1.2.1 c18 (by decide) (by decide) (by decide)
      obtain ⟨nb, rr, et1, R2⟩ := zd1_ok (rep_cursor R1 (bget g 3 + 1) tr) hs
      simp only at et1
      exact ⟨[.armBind true 1], _, by simp [stepF, ev2, hsh, et, et1], R2⟩
    · rw [if_neg c18] at hs; exact absurd (stat0 _ (by omega)) hs
  · rw [if_neg c1] at hs; exact absurd (stat0 _ (by omega)) hs

/-! ### task 76 `armBind` (`v138`) -/

/-- tail of `v138`: the separator token decides between the next pattern variable and the arm body -/
def ab2 (h : Buf) (a b z : UInt64) : Buf :=
  if b + 1 < z then
    (if bget h (d11 + bget h 3) = 15 then v1 (bset h 3 (bget h 3 + 1)) 76 a (b + 1) else bset (bset h 3 (bget h 3 + 1)) 0 0)
  else if bget h (d11 + bget h 3) = 19 then
    (if a = 0 then v1 (v1 (bset h 3 (bget h 3 + 1)) 77 0 0) 1 0 0
     else v1 (v1 (v1 (bset h 3 (bget h 3 + 1)) 80 0 0) 79 0 0) 1 0 1)
  else bset (bset h 3 (bget h 3 + 1)) 0 0

def ab1 (h : Buf) (p s w n1 a b z : UInt64) : Buf :=
  if bget h 21 = 0 then
    ab2 (bset (v9 (bset (v6 h p s w) (d9 + 4 * (bget (v6 h p s w) 4 - 1) + 3) n1) w) 32
      (s + bget (v9 (bset (v6 h p s w) (d9 + 4 * (bget (v6 h p s w) 4 - 1) + 3) n1) w) 31
         - bget (v9 (bset (v6 h p s w) (d9 + 4 * (bget (v6 h p s w) 4 - 1) + 3) n1) w) 31 * n1)) a b z
  else bset h 0 0

theorem v138_eq (g a b) : v138 g a b =
    if bget g (d11 + bget g 3) = 14 then
      ab1 (v7 16777216 (v86 16777216 g (bget g 3 + 1)) (bget (v86 16777216 g (bget g 3 + 1)) 4) (bget g 3)) (bget g 3) (bget g 32)
        (bget g (d7 + 4096 + bget g (d7 + 8 * bget g 12 + 5) + b))
        (if (if bget g (d7 + 4096 + bget g (d7 + 8 * bget g 12 + 5) + b) = 3 then v203 16777216 g (bget g (d7 + 8 * bget g 12 + 5)) b else 1) = 0 then 1 else 0)
        a b (bget g (d7 + 8 * bget g 12 + 6))
    else bset g 0 0 := by
  unfold v138 ab1 ab2
  simp only [beq_iff_eq, k40, k44, k0, k1]

theorem ab2_ok {h ts : Buf} {st : St} {fs : List Frame} {a b z : UInt64} {stp : Bool} {b0 n : Nat} (R : Rep h ts st fs)
    (ha : a = b01 stp) (hb : b.toNat = b0) (hz : z.toNat = n) (hb4 : b0 < 4096) (hs : bget (ab2 h a b z) 0 ≠ 0) :
    ∃ t r fr, st.toks = t :: r ∧
      (if b0 + 1 < n then (if t = .k 15 then some [Frame.armBind stp (b0 + 1)] else none)
       else if t = .k 19 then (if stp then some [.expr 0 1, .mkLoop, .defEnd] else some [.expr 0 0, .zeroDone]) else none) = some fr ∧
      Rep (ab2 h a b z) ts { st with toks := r } (fr ++ fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  have b1 : (b + 1).toNat = b0 + 1 := by rw [UInt64.toNat_add]; simp; omega
  have lt : b + 1 < z ↔ b0 + 1 < n := by rw [UInt64.lt_iff_toNat_lt, b1, hz]
  have fl : ∀ {P : Prop}, bget (bset (bset h 3 (bget h 3 + 1)) 0 0) 0 ≠ 0 → P := fun x => absurd (stat0 _ (by simp [length_bset]; omega)) x
  unfold ab2 at hs ⊢
  by_cases c : b + 1 < z
  · rw [if_pos c] at hs ⊢
    by_cases c15 : bget h (d11 + bget h 3) = 15
    · rw [if_pos c15] at hs ⊢
      obtain ⟨r, et, tr⟩ := tok_kw R.2.2.2.1 R.1 R.2.1 c15 (by decide) (by decide) (by decide)
      have R2 := rep_cursor R (bget h 3 + 1) tr
      exact ⟨_, r, [.armBind stp (b0 + 1)], et, by rw [if_pos (lt.mp c)]; exact if_pos rfl, rep_push (.armBind stp (b0 + 1)) a (b + 1) R2 rfl ⟨ha, b1⟩ hs⟩
    · rw [if_neg c15] at hs; exact fl hs
  · rw [if_neg c] at hs ⊢
    by_cases c19 : bget h (d11 + bget h 3) = 19
    · rw [if_pos c19] at hs ⊢
      obtain ⟨r, et, tr⟩ := tok_kw R.2.2.2.1 R.1 R.2.1 c19 (by decide) (by decide) (by decide)
      have R2 := rep_cursor R (bget h 3 + 1) tr
      cases stp with
      | false =>
        have a0 : a = 0 := ha
        rw [if_pos a0] at hs ⊢
        have R3 := rep_push .zeroDone 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
        have R4 := rep_push (.expr 0 0) 0 0 R3 rfl ⟨rfl, rfl⟩ hs
        exact ⟨_, r, [.expr 0 0, .zeroDone], et, by rw [if_neg (fun x => c (lt.mpr x))]; exact if_pos rfl, R4⟩
      | true =>
        have a0 : a ≠ 0 := by rw [ha]; decide
        rw [if_neg a0] at hs ⊢
        have R3 := rep_push .defEnd 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ (v1_zero _ _ _ _ z)))
        have R4 := rep_push .mkLoop 0 0 R3 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
        have R5 := rep_push (.expr 0 1) 0 1 R4 rfl ⟨rfl, rfl⟩ hs
        exact ⟨_, r, [.expr 0 1, .mkLoop, .defEnd], et, by rw [if_neg (fun x => c (lt.mpr x))]; exact if_pos rfl, R5⟩
    · rw [if_neg c19] at hs; exact fl hs

/-- the input flag of the newest binding row may be rewritten -/
theorem rep_flag {g ts : Buf} {st : St} {fs : List Frame} (R : Rep g ts st fs) (bs : List Bd) (bd : Bd) (hb : st.binds = bs ++ [bd])
    (f : Bool) :
    Rep (bset g (d9 + 4 * (bget g 4 - 1) + 3) (b01 f)) ts { st with binds := bs ++ [{ bd with inp := f }] } fs := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  obtain ⟨b4, bl, brows⟩ := rB
  rw [hb] at b4 bl brows
  simp only [List.length_append, List.length_singleton] at b4 bl
  have e41 : bget g 4 - 1 = bs.length.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [b4]; simp))]; simp; omega
  rw [e41]
  have ci := rowCell bs.length (by omega) 3 (by decide)
  simp only [show (3 : UInt64).toNat = 3 from rfl] at ci
  generalize hG : bset g (d9 + 4 * bs.length.toUInt64 + 3) (b01 f) = G
  have e : ∀ i : UInt64, i.toNat ≠ 180288 + 4 * bs.length + 3 → bget G i = bget g i :=
    fun i a => by rw [← hG]; exact bget_bset' _ _ _ _ (by rw [ci]; omega)
  have et : TokAgree g G := ⟨e 7 (by simp; omega), fun i hi => e i (by omega)⟩
  have es : ShTabAgree g G := fun i a _ => e i (by omega)
  have cc : ∀ n : UInt64, n.toNat < 64 → bget G n = bget g n := fun n a => e n (by omega)
  refine ⟨tokensAt_frame rT et rts, rts, by rw [cc 0 (by decide)]; exact r0,
    by rw [cc 3 (by decide)]; exact tokAt_frame et hn7 r3, by rw [cc 11 (by decide)]; exact r11,
    ⟨by rw [cc 4 (by decide)]; simp; omega, by simp; omega, fun i hi => ?_⟩,
    defs_frame rD (cc 12 (by decide)) (cc 27 (by decide)) (cc 26 (by decide)) (fun i a b => e i (by omega)) et hn7 es,
    arena_frame rA (cc 8 (by decide)) (cc 9 (by decide)) (fun i a b => e i (by omega)) es,
    fun s' hs' => by rw [cc 25 (by decide)]; exact (r25 s' hs').frame es,
    fun y hy => by rw [cc 29 (by decide)]; exact nameAt_frame et (by omega) (r29 y hy),
    by rw [cc 30 (by decide)]; exact r30, by rw [cc 32 (by decide)]; exact r32,
    out_frame rO (by rw [← hG]; exact drop_bset _ _ _ (by rw [ci]; omega)),
    tasks_frame rK (cc 5 (by decide)) (fun i a b => e i (by have := rK.2.1; omega)) et hn7 es (fun i a b => e i (by omega)) har⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hin : i < bs.length
  · have c : ∀ k : UInt64, k.toNat < 4 → bget G (d9 + 4 * i.toUInt64 + k) = bget g (d9 + 4 * i.toUInt64 + k) :=
      fun k hk => e _ (by rw [rowCell i (by omega) k hk]; omega)
    have c0' := c 0 (by decide); simp only [UInt64.add_zero] at c0'
    obtain ⟨a0, a1, a2, a3⟩ := brows i (by simp; omega)
    simp only [List.getElem_append_left hin] at a0 a1 a2 a3 ⊢
    exact ⟨by rw [c0']; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1,
      by rw [c 2 (by decide)]; exact a2.frame es, by rw [c 3 (by decide)]; exact a3⟩
  · have : i = bs.length := by omega
    subst this
    have c : ∀ k : UInt64, k.toNat < 3 → bget G (d9 + 4 * bs.length.toUInt64 + k) = bget g (d9 + 4 * bs.length.toUInt64 + k) :=
      fun k hk => e _ (by rw [rowCell bs.length (by omega) k (by omega)]; omega)
    have c0' := c 0 (by decide); simp only [UInt64.add_zero] at c0'
    obtain ⟨a0, a1, a2, a3⟩ := brows bs.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at a0 a1 a2 a3 ⊢
    exact ⟨by rw [c0']; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1,
      by rw [c 2 (by decide)]; exact a2.frame es, by rw [← hG]; exact bget_bset_eq _ _ _ _ rfl (by rw [ci]; omega)⟩

theorem ab2_zero (h : Buf) (a b z : UInt64) (h0 : bget h 0 = 0) (hl : 12352 ≤ h.length) : bget (ab2 h a b z) 0 = 0 := by
  have e3 : bget (bset h 3 (bget h 3 + 1)) 0 = 0 := by rw [bget_bset' _ _ _ _ (by decide)]; exact h0
  have fl : bget (bset (bset h 3 (bget h 3 + 1)) 0 0) 0 = 0 := stat0 _ (by simp [length_bset]; omega)
  unfold ab2
  by_cases c : b + 1 < z
  · rw [if_pos c]
    by_cases c15 : bget h (d11 + bget h 3) = 15
    · rw [if_pos c15]; exact v1_zero _ _ _ _ e3
    · rw [if_neg c15]; exact fl
  · rw [if_neg c]
    by_cases c19 : bget h (d11 + bget h 3) = 19
    · rw [if_pos c19]
      by_cases a0 : a = 0
      · rw [if_pos a0]; exact v1_zero _ _ _ _ (v1_zero _ _ _ _ e3)
      · rw [if_neg a0]; exact v1_zero _ _ _ _ (v1_zero _ _ _ _ (v1_zero _ _ _ _ e3))
    · rw [if_neg c19]; exact fl

/-- `v6` followed by the flag write leaves the status and the shape table alone -/
theorem v6flag_sh {h ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (p s w n : UInt64) (q : bget h 4 < d14) :
    bget (v6 h p s w) 0 = bget h 0 ∧ ShTabAgree h (bset (v6 h p s w) (d9 + 4 * (bget (v6 h p s w) 4 - 1) + 3) n) := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  have b4 := R.2.2.2.2.2.1.1
  have hlt : st.binds.length < 1024 := by rw [← b4]; exact UInt64.lt_iff_toNat_lt.mp q
  have hn : bget h 4 = st.binds.length.toUInt64 := by rw [← b4]; simp
  obtain ⟨L, e4, c0, c1, c2, c3, U, D⟩ := v6_eff h p s w st.binds.length hn hlt hl
  have e41 : bget (v6 h p s w) 4 - 1 = st.binds.length.toUInt64 := by
    rw [e4]; apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have ci := rowCell st.binds.length hlt 3 (by decide)
  simp only [show (3 : UInt64).toNat = 3 from rfl] at ci
  rw [e41]
  exact ⟨U 0 (by decide) (Or.inl (by simp; omega)),
    fun i a b => by rw [bget_bset' _ _ _ _ (by rw [ci]; omega)]; exact U i (by omega) (Or.inl (by omega))⟩

theorem ab1_ok {h ts : Buf} {st : St} {fs : List Frame} {p s wc n1c a b z : UInt64} {stp : Bool} {b0 n : Nat} {name : List Nat}
    {w : Sh} {n1 : Bool} (R : Rep h ts st fs) (hx : NameAt h p name) (hsl : s = st.sslot.toUInt64) (hw : ShapeCode h wc w)
    (hn1 : n1c = b01 n1) (ha : a = b01 stp) (hb : b.toNat = b0) (hz : z.toNat = n) (hb4 : b0 < 4096) (h21 : bget h 21 = 0)
    (hs : bget (ab1 h p s wc n1c a b z) 0 ≠ 0) :
    ∃ t r fr, st.toks = t :: r ∧
      (if b0 + 1 < n then (if t = .k 15 then some [Frame.armBind stp (b0 + 1)] else none)
       else if t = .k 19 then (if stp then some [.expr 0 1, .mkLoop, .defEnd] else some [.expr 0 0, .zeroDone]) else none) = some fr ∧
      Rep (ab1 h p s wc n1c a b z) ts
        { st with toks := r, binds := st.binds ++ [⟨name, st.sslot, some w, n1⟩],
                  sslot := if n1 then st.sslot else st.sslot + w.width } (fr ++ fs) := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  subst hn1
  unfold ab1 at hs ⊢
  rw [if_pos h21] at hs ⊢
  unfold v9 at hs ⊢
  simp only [] at hs ⊢
  by_cases q : bget h 4 < d14
  · obtain ⟨z0, es5⟩ := v6flag_sh R p s wc (b01 n1) q
    have hs6 : bget (v6 h p s wc) 0 ≠ 0 := by rw [z0, R.2.2.1]; split <;> decide
    have R4 := rep_v6 R p s wc name st.sslot (some w) hx hsl hw hs6
    have R5 := rep_flag R4 st.binds ⟨name, st.sslot, some w, false⟩ rfl n1
    have hw5 : ShOpt _ wc (some w) := ShapeCode.frame hw es5
    generalize bset (v6 h p s wc) (d9 + 4 * (bget (v6 h p s wc) 4 - 1) + 3) (b01 n1) = G5 at hs R5 hw5 ⊢
    obtain ⟨_, hl5, _⟩ := rep_bounds R5
    rw [v9_cw hw5] at hs ⊢
    have q31 : bget (bset G5 31 (cw (some w)).toUInt64) 31 = (cw (some w)).toUInt64 := bget_bset_eq _ _ _ _ rfl (by simp; omega)
    rw [q31] at hs ⊢
    have h32 : s + (cw (some w)).toUInt64 - (cw (some w)).toUInt64 * b01 n1 = (if n1 then st.sslot else st.sslot + w.width).toUInt64 := by
      rw [hsl]; cases n1 <;> simp [b01, cw]
    have R7 := rep_nxss (h' := bset (bset G5 31 (cw (some w)).toUInt64) 32 (s + (cw (some w)).toUInt64 - (cw (some w)).toUInt64 * b01 n1))
      R5 st.nx (if n1 then st.sslot else st.sslot + w.width)
      (fun i _ _ i31 i32 => by rw [bget_bset' _ _ _ _ (fun x => i32 x.symm), bget_bset' _ _ _ _ (fun x => i31 x.symm)])
      (by rw [drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide)])
      (by rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)]; exact R5.2.2.2.2.1)
      (by rw [bget_bset_eq _ _ _ _ rfl (by simp [length_bset]; omega)]; exact h32)
    obtain ⟨t, r, fr, et, hfr, R8⟩ := ab2_ok R7 ha hb hz hb4 hs
    exact ⟨t, r, fr, et, hfr, R8⟩
  · exfalso; apply hs
    obtain ⟨b41, b42, _⟩ := R.2.2.2.2.2.1
    have e4 : bget h 4 = 1024 := by
      apply UInt64.toNat_inj.mp
      have q' : ¬ (bget h 4).toNat < 1024 := fun x => q (UInt64.lt_iff_toNat_lt.mpr x)
      show (bget h 4).toNat = 1024
      omega
    have v6e : v6 h p s wc = bset h 0 0 := by unfold v6; rw [if_neg q]
    rw [v6e, show bget (bset h 0 0) 4 = 1024 from by rw [bget_bset' _ _ _ _ (by decide)]; exact e4]
    apply ab2_zero _ _ _ _ _ (by simp [length_bset]; omega)
    rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)]
    exact stat0 _ (by omega)

/-- **task 76** (`v138`, one pattern variable of a loop arm) -/
theorem h_armBind {h ts : Buf} {st : St} {stp : Bool} {b0 : Nat} {fs : List Frame} (r : Rep h ts st (.armBind stp b0 :: fs))
    (hD : inDefF fs = true) (hb : b0 < st.cur.params.length) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.armBind stp b0) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r rfl
  simp only [Frame.code, FrameArgs] at E ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E ea
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1
  have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; have := R1.2.1; omega
  have p3 := R1.2.2.2.1.le
  have ev : step h = v138 g a b := by rw [E]; simp [v96]
  rw [ev, v138_eq] at hs ⊢
  by_cases c14 : bget g (d11 + bget g 3) = 14
  · rw [if_pos c14] at hs ⊢
    -- the current def row
    have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
    have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← rD.1]; simp
    have row := rD.2.2.2.2.1; simp only [if_true] at row
    obtain ⟨⟨_, _, _, _, _, r6, r5, rc⟩, _⟩ := row
    rw [← h12] at r6 r5 rc
    have eb : b = b0.toUInt64 := by rw [← ea.2]; simp
    have hw := rc b0 hb
    rw [← eb] at hw
    have hv := v203_eq g (bget g (d7 + 8 * bget g 12 + 5)) st.cur.params r5 rc b0 16777216 (by omega) (by omega)
    rw [← eb] at hv
    have hn1 : (if (if bget g (d7 + 4096 + bget g (d7 + 8 * bget g 12 + 5) + b) = 3 then
        v203 16777216 g (bget g (d7 + 8 * bget g 12 + 5)) b else 1) = 0 then (1 : UInt64) else 0) =
        b01 (st.cur.params[b0] == .ls && !(hasLs ((st.cur.params.take b0).map some))) := by
      rw [hv]
      by_cases cl : st.cur.params[b0] = .ls
      · rw [if_pos (hw.ls_iff.mpr cl)]; cases hasLs ((st.cur.params.take b0).map some) <;> simp [cl, b01]
      · rw [if_neg (fun x => cl (hw.ls_iff.mp x))]; simp [cl, b01]
    rw [hn1] at hs ⊢
    generalize bget g (d7 + 4096 + bget g (d7 + 8 * bget g 12 + 5) + b) = wc at hs hw ⊢
    -- the name
    obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id R1.2.2.2.1 rT c14
    have hskip := v86_skip nm 16777216 g (bget g 3 + 1) hNm.2.1
      (by rw [tn_add _ _ (by simp; omega)]; have := hNm.2.2; simp; omega) (by have := hNm.2.2; omega)
    rw [hskip] at hs ⊢
    have epos : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
      rw [show (2 : UInt64) = 1 + 1 from rfl]; ac_rfl
    have R2 := rep_cursor R1 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1) (by rw [epos]; exact tr)
    have et2 : TokAgree g (bset g 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1)) :=
      ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by simp; omega)⟩
    have es2 : ShTabAgree g (bset g 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1)) := fun i a _ => bget_bset' _ _ _ _ (by simp; omega)
    have hNm2 := nameOK_frame et2 (by omega) hNm
    have hw2 := hw.frame es2
    have s32 : bget g 32 = st.sslot.toUInt64 := R1.2.2.2.2.2.2.2.2.2.2.2.1
    generalize bset g 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1) = g2 at hs R2 hNm2 hw2 ⊢
    obtain ⟨hn2, hl2, _⟩ := rep_bounds R2
    have h72 : (bget g2 7).toNat < 2 ^ 24 := by rw [R2.1.2.2.2]; simp; have := R2.2.1; omega
    obtain ⟨hS, hf⟩ := v7_findB R2.2.2.2.2.2.1 h72 (by omega) hNm2
    have hdrop := v7_drop 16777216 g2 (bget g2 4) (bget g 3)
    have R3 := rep_same R2 hS (Or.inl rfl) hdrop
    have et3 : TokAgree g2 (v7 16777216 g2 (bget g2 4) (bget g 3)) := ⟨hS.2 7 (by decide) (by decide), fun i hi => hS.2 i (by omega) (by omega)⟩
    have es3 : ShTabAgree g2 (v7 16777216 g2 (bget g2 4) (bget g 3)) := fun i a _ => hS.2 i (by omega) (by omega)
    have hx3 : NameAt (v7 16777216 g2 (bget g2 4) (bget g 3)) (bget g 3) (nm.map UInt64.toNat) := ⟨nm, nameOK_frame et3 (by omega) hNm2, rfl⟩
    have hw3 := hw2.frame es3
    generalize v7 16777216 g2 (bget g2 4) (bget g 3) = g3 at hs R3 hf hx3 hw3 ⊢
    obtain ⟨_, hl3, _⟩ := rep_bounds R3
    rcases hf with ⟨h21, hnone⟩ | ⟨i, h21, hi, _⟩
    · obtain ⟨t, rr, fr, et4, hfr, R4⟩ := ab1_ok R3 hx3 s32 hw3 rfl ea.1 ea.2 r6 (by omega) h21 hs
      simp only at et4
      refine ⟨fr, _, ?_, R4⟩
      simp only [stepF, List.getElem?_eq_getElem hb, et, et4, hnone]
      revert hfr
      split <;> (try split) <;> (try split) <;> simp
    · exfalso; apply hs
      have ne : bget g3 21 ≠ 0 := by
        rw [h21]; intro x
        have t1 := congrArg UInt64.toNat x
        have hle : st.binds.length ≤ 1024 := R3.2.2.2.2.2.1.2.1
        have hi' : i < st.binds.length := hi
        simp at t1; omega
      unfold ab1; rw [if_neg ne]; exact stat0 _ (by omega)
  · rw [if_neg c14] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv

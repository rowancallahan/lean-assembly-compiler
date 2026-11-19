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
    fun x hx hne => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
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
    fun x hx hne => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
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
    fun x hx hne => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
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

end ParInv

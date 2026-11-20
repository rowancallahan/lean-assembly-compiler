/- Nano/V2Self/Proof/Parser/ParInvArg: Layer-3 handlers for task 47 `argCheck c k` (v122) and task 48 `mkCall c n` (v123, on C's `rep_v5`), box G.
`rep_scratch`: `Rep` does not read the scratch cells 21 / 31.  `v122_eq`: the handler as one expression. -/
import Nano.V2Self.Proof.Parser.ParInvCall
import Nano.V2Self.Proof.Parser.ParInvPrim
import Nano.V2Self.Proof.Parser.ParInvBuild
namespace ParInv
open C BufL ParSpec ParRun

/-- `Rep` ignores the scratch cells 21 and 31 -/
theorem rep_scratch {h h' ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs)
    (e : ∀ i : UInt64, i.toNat ≠ 21 → i.toNat ≠ 31 → bget h' i = bget h i)
    (ed : h'.drop LAY_HASH = h.drop LAY_HASH) : Rep h' ts st fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide), fun i hi => e i (by omega) (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega)
  have c : ∀ n : UInt64, n.toNat ≠ 21 → n.toNat ≠ 31 → bget h' n = bget h n := e
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide)]; exact tokAt_frame et hn r3, by rw [c 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) et hn es,
    defs_frame rD (c 12 (by decide) (by decide)) (c 27 (by decide) (by decide)) (c 26 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) et hn es,
    arena_frame rA (c 8 (by decide) (by decide)) (c 9 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) es,
    fun s hs => by rw [c 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide)]; exact r32, out_frame rO ed,
    tasks_frame rK (c 5 (by decide) (by decide)) (fun i _ _ => e i (by omega) (by omega)) et hn es
      (fun i a _ => e i (by omega) (by omega)) rA.2.1⟩

theorem bb31 (g : Buf) (hl : 31 < g.length) (v : UInt64) : bget (bset g 31 v) 31 = v := bget_bset_same _ _ _ hl
theorem bb31' (g : Buf) (hl : 31 < g.length) (u v : UInt64) : bget (bset (bset g 31 u) 31 v) 31 = v :=
  bget_bset_same _ _ _ (by rw [length_bset]; exact hl)

/-- the callee's arity word (v15) -/
def arAr (g : Buf) (a : UInt64) : UInt64 := if a < 512 then bget g (d7 + 8 * a + 6) else v91 (a - 512)
/-- the parameter code of the operand `b` below the top (v14 after v15) -/
def arW (g : Buf) (a b : UInt64) : UInt64 :=
  if a < 512 then bget (bset g 31 (arAr g a)) ((d7 + 4096) + (bget (bset g 31 (arAr g a)) (d7 + 8 * a + 5)) + (arAr g a - b))
  else v90 (a - 512) (arAr g a - b)
/-- the heap after the two scratch writes -/
def arG (g : Buf) (a b : UInt64) : Buf := bset (bset g 31 (arAr g a)) 31 (arW g a b)

/-- task 47 as one expression: the operand's shape code is read before the scratch writes, its tag / `a` field after them -/
theorem v122_eq (g : Buf) (a b : UInt64) (hb : b ≠ 0) (hl : 31 < g.length) :
    v122 g a b =
      if bget g ((d5 + 8 * (bget g (d3 + (bget g 8) - b))) + 3) == arW g a b then v1 (arG g a b) 47 a (b - 1)
      else if arW g a b == 4 then
        (if bget (arG g a b) ((d5 + 8 * (bget (arG g a b) (d3 + (bget (arG g a b) 8) - b))) + 0) == 1 then v1 (arG g a b) 47 a (b - 1)
         else if bget (arG g a b) ((d5 + 8 * (bget (arG g a b) (d3 + (bget (arG g a b) 8) - b))) + 0) == 9 then
           (if bget (arG g a b) ((d5 + 8 * (bget (arG g a b) (d3 + (bget (arG g a b) 8) - b))) + 1) == 1 then v1 (arG g a b) 47 a (b - 1)
            else bset (arG g a b) 0 0)
         else bset (arG g a b) 0 0)
      else bset (arG g a b) 0 0 := by
  unfold v122 v15 v14 arG arW arAr
  simp only [beq_iff_eq, hb, if_false, bb31 g hl, bb31' g hl]

theorem arG_get (g : Buf) (a b i : UInt64) (hi : i.toNat ≠ 31) : bget (arG g a b) i = bget g i := by
  unfold arG; rw [bget_bset' _ _ _ _ (by simpa using Ne.symm hi), bget_bset' _ _ _ _ (by simpa using Ne.symm hi)]

theorem arG_len (g : Buf) (a b : UInt64) : (arG g a b).length = g.length := by simp [arG, length_bset]

theorem arG_drop (g : Buf) (a b : UInt64) : (arG g a b).drop LAY_HASH = g.drop LAY_HASH := by
  unfold arG; rw [drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide)]

theorem ShapeCode.ne0 {h : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) : c ≠ 0 := by
  cases r <;> first | decide | (intro z; subst z; simp at *)

/-- the row of a callee: a finished def or the current one -/
theorem row_rep {g : Buf} {st : St} {j : Nat} {d : DefR} (rD : DefsRep g st true) (hj : (rows st)[j]? = some d) :
    j < 512 ∧ RowRep g j d := by
  obtain ⟨_, hlen, _, hrows, hcur, _⟩ := rD
  simp only [rows] at hj
  by_cases hlt : j < st.defs.length
  · rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt] at hj
    cases hj; exact ⟨by omega, (hrows j hlt).1⟩
  · rw [List.getElem?_append_right (by omega)] at hj
    have hq : j - st.defs.length = 0 := by
      cases hq : j - st.defs.length with
      | zero => rfl
      | succ q => rw [hq] at hj; simp at hj
    have : j = st.defs.length := by omega
    subst this
    simp at hj; subst hj
    exact ⟨(if_pos rfl ▸ hcur).2, (if_pos rfl ▸ hcur).1.1⟩

theorem u_sub {x b : UInt64} {n m : Nat} (hx : x.toNat = n) (hb : b.toNat = m) (hm : m ≤ n) : x - b = (n - m).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hx, hb]
  have := x.toNat_lt
  simp; omega

/-- the callee word is a row of the table / a small prim id (from Layer 2's `WF`) -/
def calleeOK (st : St) : Callee → Prop
  | .df j => j < (rows st).length
  | .pr p => p < 2 ^ 32

/-- the parameter code the check reads is the code of Layer 2's `parCode` -/
theorem arW_code {g ts : Buf} {st : St} {fs : List Frame} {c : Callee} {k : Nat} {a b : UInt64} (R : Rep g ts st fs)
    (hD : inDefF fs = true) (ea : a = calleeW c) (eb : b.toNat = k + 1) (hka : k + 1 ≤ arity st c)
    (hc : calleeOK st c) :
    ∃ wS, parCode st c (arity st c - (k + 1)) = some wS ∧ ShapeCode g (arW g a b) wS := by
  have rD : DefsRep g st true := hD ▸ R.2.2.2.2.2.2.1
  cases c with
  | df j =>
    have hjl : j < (rows st).length := hc
    obtain ⟨d, hd⟩ : ∃ d, (rows st)[j]? = some d := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨hj512, _, _, _, _, _, rcnt, rbnd, rpar⟩ := row_rep rD hd
    have har : arity st (.df j) = d.params.length := by simp [arity, hd]
    rw [har] at hka ⊢
    subst ea
    have a512 : j.toUInt64 < 512 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have c5 := defCell j hj512 5 (by decide)
    have ei := u_sub rcnt eb hka
    have hi : d.params.length - (k + 1) < d.params.length := by omega
    have cp := parCell (bget g (d7 + 8 * j.toUInt64 + 5)) (d.params.length - (k + 1)) (by omega)
    refine ⟨d.params[d.params.length - (k + 1)], by simp [parCode, hd], ?_⟩
    unfold arW arAr
    simp only [calleeW, a512, if_true]
    rw [ei, bget_bset' _ _ (d7 + 8 * j.toUInt64 + 5) _ (by rw [c5]; simp; omega), bget_bset' _ _ _ _ (by rw [cp]; simp; omega)]
    exact rpar _ hi
  | pr p =>
    have hp : p < 2 ^ 32 := hc
    subst ea
    have a512 : ¬ (512 + p).toUInt64 < 512 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have ep : (512 + p).toUInt64 - 512 = p.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp; omega
    have har : arity st (.pr p) = primAr p := rfl
    rw [har] at hka ⊢
    have hA : primAr p ≤ 3 := by unfold primAr; split <;> (try split) <;> (try split) <;> omega
    have ei : v91 p.toUInt64 - b = (primAr p - (k + 1)).toUInt64 :=
      u_sub (by rw [v91_eq (by omega)]; simp; omega) eb hka
    refine ⟨primPar p (primAr p - (k + 1)), rfl, ?_⟩
    unfold arW arAr
    simp only [calleeW, a512, if_false, ep, ei]
    exact v90_code g (by omega) (by omega)

/-- the record of operand `k` (0 = top), addressed as the machine does (`h[8] − (k+1)`) -/
theorem operand_fld {g : Buf} {arena vals : List RN} (rA : ArenaRep g arena vals) {k : Nat} (hk : k < vals.length) {b : UInt64}
    (eb : b.toNat = k + 1) :
    ∃ t A B sh p ks, vals[k]? = some (RN.mk t A B sh p ks) ∧ fld g (bget g (d3 + bget g 8 - b)) 0 = t.toUInt64 ∧
      fld g (bget g (d3 + bget g 8 - b)) 1 = A.toUInt64 ∧ ShOpt g (fld g (bget g (d3 + bget g 8 - b)) 3) sh ∧ t < 2 ^ 64 ∧ (t ≠ 2 → t ≠ 5 → A < 2 ^ 64) ∧
      (bget g (d3 + bget g 8 - b)).toNat < 16384 ∧ (d3 + bget g 8 - b).toNat = LAY_D3 + (vals.length - 1 - k) := by
  obtain ⟨h9, hal, h8, hvl, I, hI, hR, _, _⟩ := rA
  obtain ⟨hr, earr, _⟩ := hR k hk
  have ecell : d3 + bget g 8 - b = d3 + (vals.length - 1 - k).toUInt64 := by
    apply UInt64.toNat_inj.mp
    have e1 : (d3 + bget g 8).toNat = LAY_D3 + vals.length := by rw [tn_add _ _ (by simp [d3v]; omega)]; simp [d3v]; omega
    rw [d3k _ (by omega), UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), e1, eb]; omega
  have eop : bget g (d3 + bget g 8 - b) = opAt g (vals.length - 1 - k) := by rw [ecell]; rfl
  rw [eop, ecell]
  have rn := (hI _ hr).1
  have ex : (opAt g (vals.length - 1 - k)).toNat.toUInt64 = opAt g (vals.length - 1 - k) := by simp
  rw [earr, ex] at rn
  rw [List.getElem?_eq_getElem hk]
  cases hv : vals[k] with
  | mk t A B sh p ks =>
    rw [hv] at rn
    generalize I (opAt g (vals.length - 1 - k)).toNat = ids at rn
    cases rn with
    | mk f0 f1 _ fsh _ _ ht hAB _ =>
      exact ⟨t, A, B, sh, p, ks, rfl, f0, f1, fsh, ht, fun x y => (hAB x y).1, by omega, d3k _ (by omega)⟩

theorem u_one {t : Nat} (ht : t < 2 ^ 64) {c : Nat} (hc : c < 2 ^ 64) (e : t.toUInt64 = c.toUInt64) : t = c := by
  have := congrArg UInt64.toNat e
  simpa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hc] using this

/-! ## task 47: `argCheck c k` (v122) -/
theorem h_argCheck {h ts : Buf} {st : St} {c : Callee} {k : Nat} {fs : List Frame} (r : Rep h ts st (.argCheck c k :: fs))
    (hD : inDefF fs = true) (hk : k ≤ st.vals.length) (hka : k ≤ arity st c)
    (hc : calleeOK st c) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.argCheck c k) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  match k with
  | 0 =>
    have b0 : b = 0 := UInt64.toNat_inj.mp eb
    subst b0
    have ev : step h = g := by rw [E]; simp [v96, v122]
    rw [ev]
    exact ⟨[], st, argCheck_zero c st, R1⟩
  | k + 1 =>
    have bne : b ≠ 0 := fun z => by subst z; simp at eb
    obtain ⟨hn, hl, har⟩ := rep_bounds R1
    have eb1 : (b - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨t, A, B, sh, p, ks, hv, f0, f1, fsh, ht, hA, hu, hcell⟩ := operand_fld R1.2.2.2.2.2.2.2.1 (k := k) (by omega) eb
    obtain ⟨wS, hpc, hw⟩ := arW_code R1 hD ea eb hka hc
    have e8 : bget (arG g a b) 8 = bget g 8 := arG_get g a b 8 (by decide)
    have eu : bget (arG g a b) (d3 + bget g 8 - b) = bget g (d3 + bget g 8 - b) := arG_get g a b _ (by rw [hcell]; omega)
    have e0 : bget (arG g a b) (d5 + 8 * bget g (d3 + bget g 8 - b) + 0) = t.toUInt64 := by
      rw [arG_get g a b _ (by rw [recK _ _ hu (by decide)]; omega)]; exact f0
    have e1 : bget (arG g a b) (d5 + 8 * bget g (d3 + bget g 8 - b) + 1) = A.toUInt64 := by
      rw [arG_get g a b _ (by rw [recK _ _ hu (by decide)]; omega)]; exact f1
    have ev : step h = v122 g a b := by rw [E]; simp [v96]
    rw [ev, v122_eq g a b bne (by omega)] at hs ⊢
    simp only [e8, eu, e0, e1, beq_iff_eq] at hs ⊢
    have fin : (sh = some wS ∨ (wS = .nt ∧ (t = 1 ∨ (t = 9 ∧ A = 1)))) →
        bget (v1 (arG g a b) 47 a (b - 1)) 0 ≠ 0 →
        ∃ fr st', stepF (.argCheck c (k + 1)) st = some (fr, st') ∧ Rep (v1 (arG g a b) 47 a (b - 1)) ts st' (fr ++ fs) := by
      intro hcond hs'
      have R2 : Rep (arG g a b) ts st fs := rep_scratch R1 (fun i _ h31 => arG_get g a b i h31) (arG_drop g a b)
      have R3 := rep_push (.argCheck c k) a (b - 1) R2 rfl ⟨ea, eb1⟩ hs'
      refine ⟨[.argCheck c k], st, ?_, R3⟩
      simp only [stepF, hv, hpc, RN.sh, RN.tag, RN.a]
      exact if_pos hcond
    have dead : bget (bset (arG g a b) 0 0) 0 ≠ 0 → False := fun x => x (stat0 _ (by rw [arG_len]; omega))
    by_cases c1 : bget g (d5 + 8 * bget g (d3 + bget g 8 - b) + 3) = arW g a b
    · rw [if_pos c1] at hs ⊢
      refine fin (Or.inl ?_) hs
      have fsh' : ShOpt g (arW g a b) sh := by rw [← c1]; exact fsh
      cases sh with
      | none => exact absurd fsh' hw.ne0
      | some s => exact congrArg some (ShapeCode.det fsh' hw)
    · rw [if_neg c1] at hs ⊢
      by_cases c2 : arW g a b = 4
      · rw [if_pos c2] at hs ⊢
        have wnt : wS = .nt := ShapeCode.det (c2 ▸ hw) .nt
        by_cases c3 : t.toUInt64 = 1
        · rw [if_pos c3] at hs ⊢; exact fin (Or.inr ⟨wnt, Or.inl (u_one ht (c := 1) (by decide) c3)⟩) hs
        · rw [if_neg c3] at hs ⊢
          by_cases c4 : t.toUInt64 = 9
          · rw [if_pos c4] at hs ⊢
            by_cases c5 : A.toUInt64 = 1
            · rw [if_pos c5] at hs ⊢
              have t9 := u_one ht (c := 9) (by decide) c4
              exact fin (Or.inr ⟨wnt, Or.inr ⟨t9, u_one (hA (by omega) (by omega)) (c := 1) (by decide) c5⟩⟩) hs
            · rw [if_neg c5] at hs; exact (dead hs).elim
          · rw [if_neg c4] at hs; exact (dead hs).elim
      · rw [if_neg c2] at hs; exact (dead hs).elim

/-! ## task 48: `mkCall c n` (v123) -/
theorem h_mkCall {h ts : Buf} {st : St} {c : Callee} {n : Nat} {fs : List Frame} (r : Rep h ts st (.mkCall c n :: fs))
    (hD : inDefF fs = true) (hnf : fs.all (fun f => !f.isFlat)) (hn : n ≤ 4096) (hc : calleeOK st c)
    (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.mkCall c n) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  have ebn : b = n.toUInt64 := by rw [← eb]; simp
  have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
  subst ea ebn
  cases c with
  | df j =>
    have hjl : j < (rows st).length := hc
    obtain ⟨d, hd⟩ : ∃ d, (rows st)[j]? = some d := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨hj512, _, _, _, rres, _⟩ := row_rep rD hd
    have a512 : j.toUInt64 < 512 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have ev : step h = v5 g (8 : Nat).toUInt64 j.toUInt64 n.toUInt64 (bget g (d7 + 8 * j.toUInt64 + 3)) (b01 false) n.toUInt64 := by
      rw [E]; simp [v96, v123, calleeW, a512, b01]
    rw [ev] at hs ⊢
    obtain ⟨st', hm, R2⟩ := rep_v5 R1 hnf n 8 j n d.res false _ rres (by decide) (by omega) (by omega) hn hs
    exact ⟨[], st', by simp [stepF, hd, hm], R2⟩
  | pr p =>
    have hp : p < 2 ^ 32 := hc
    have a512 : ¬ (512 + p).toUInt64 < 512 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have ep : (512 + p).toUInt64 - 512 = p.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      simp; omega
    have ev : step h = v5 g (9 : Nat).toUInt64 p.toUInt64 (0 : Nat).toUInt64 (v92 p.toUInt64) (b01 false) n.toUInt64 := by
      have e0 : (512 + p).toUInt64 = 512 + UInt64.ofNat p := by simp
      have a512' : ¬ (512 + UInt64.ofNat p < 512) := e0 ▸ a512
      have ep' : 512 + UInt64.ofNat p - 512 = UInt64.ofNat p := by rw [← e0]; exact ep
      rw [E]; simp [v96, v123, calleeW, a512', ep', b01]
    rw [ev] at hs ⊢
    obtain ⟨st', hm, R2⟩ := rep_v5 R1 hnf n 9 p 0 (some (primRes p)) false _ (v92_code g (by omega)) (by decide) (by omega)
      (by decide) hn hs
    exact ⟨[], st', by simp [stepF, hm], R2⟩

end ParInv

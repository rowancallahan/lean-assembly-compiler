/- Nano/V2Self/Proof/ParInvLetEnd: Layer-3 handler `letEnd s d` (task 12, v118), box C: the LET node over (value, body),
binding depth restored to `d`. Side conditions from B's WF: `d ≤ |binds|`, no flatten frame pending. -/
import Nano.V2Self.Proof.ParInvLet
import Nano.V2Self.Proof.ParInvAtom
import Nano.V2Self.Proof.ParInvName
namespace ParInv
open C BufL ParSpec ParRun

/-- restoring the binding depth h[4] to `d ≤ |binds|` represents `binds.take d` -/
theorem rep_take {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (d : Nat) (hd : d ≤ st.binds.length) :
    Rep (bset h 4 d.toUInt64) ts { st with binds := st.binds.take d } fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have u : (4 : UInt64).toNat = 4 := rfl
  have c : ∀ i : UInt64, i.toNat ≠ 4 → bget (bset h 4 d.toUInt64) i = bget h i := fun i hi => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 4 d.toUInt64) := ⟨c 7 (by decide), fun i hi => c i (by omega)⟩
  have es : ShTabAgree h (bset h 4 d.toUInt64) := fun i a _ => c i (by omega)
  have ea : ArenaAgree h (bset h 4 d.toUInt64) := fun i a _ => c i (by omega)
  obtain ⟨b4, bl, bk⟩ := rB
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide)]; exact r0, by rw [c 3 (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide)]; exact r11, ⟨?_, by simp; omega, fun i hi => ?_⟩,
    defs_frame rD (c 12 (by decide)) (c 27 (by decide)) (fun i a _ => c i (by omega)) et hn es,
    arena_frame rA (c 8 (by decide)) (c 9 (by decide)) (fun i a _ => c i (by omega)) es,
    fun s hs => by rw [c 25 (by decide)]; exact (r25 s hs).frame es,
    fun y hy hne => by rw [c 29 (by decide)]; exact nameAt_frame et (by omega) (r29 y hy hne),
    by rw [c 30 (by decide)]; exact r30, by rw [c 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (c 5 (by decide)) (fun i a _ => c i (by omega)) et hn es ea rA.2.1⟩
  · rw [bget_bset_eq _ _ _ _ rfl (by rw [u, rO.1]; omega)]; simp; omega
  · simp only [List.length_take] at hi
    have hi' : i < st.binds.length := by omega
    have := bk i hi'
    simp only [List.getElem_take]
    have cr : ∀ k : UInt64, k.toNat < 4 → bget (bset h 4 d.toUInt64) (d9 + 4 * i.toUInt64 + k) = bget h (d9 + 4 * i.toUInt64 + k) :=
      fun k hk => c _ (by rw [rowCell i (by omega) k hk]; omega)
    have c0 := cr 0 (by decide); simp only [UInt64.add_zero] at c0
    obtain ⟨a0, a1, a2, a3⟩ := this
    exact ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [cr 1 (by decide)]; exact a1, by rw [cr 2 (by decide)]; exact a2.frame es,
      by rw [cr 3 (by decide)]; exact a3⟩

/-- the scratch word h[31] is not part of the representation -/
theorem rep_31 {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (v : UInt64) : Rep (bset h 31 v) ts st fs :=
  rep_same r (same_bset 21 h 31 v (Or.inr rfl)) (Or.inl rfl) (drop_bset _ _ _ (by decide))

/-! ## task 12: `letEnd s d` (v118) -/
theorem h_letEnd {h ts : Buf} {st : St} {s d : Nat} {fs : List Frame} (r : Rep h ts st (.letEnd s d :: fs))
    (hd : d ≤ st.binds.length) (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letEnd s d) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  subst ea
  have eb' : b = d.toUInt64 := by rw [← eb]; simp
  subst eb'
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have rA := R1.2.2.2.2.2.2.2.1
  have h8le : (bget h1 8).toNat ≤ 4096 := by rw [rA.2.2.1]; exact rA.2.2.2.1
  -- the words v118 reads, named
  generalize ew : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) = wB
  generalize et : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 4) = tB
  generalize ez : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) = zV
  have ev : step h = v5 (bset (bset h1 31 (if zV < 5 then 1 else bget h1 (d7 + 8192 + 3 * (zV - 5) + 2))) 4 d.toUInt64)
      5 s.toUInt64 (if zV < 5 then 1 else bget h1 (d7 + 8192 + 3 * (zV - 5) + 2)) wB tB 2 := by
    rw [E]; simp only [Frame.code, v96, v118, v9, ew, et, ez]
    simp
    rw [bget_bset_eq _ _ _ _ rfl (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)]
  rw [ev] at hs ⊢
  -- two operands: the v5 guard
  obtain ⟨_, g2, _⟩ := v5_guards _ _ _ _ _ _ _ (by simp [length_bset]; omega) hs
  have g2' := UInt64.lt_iff_toNat_lt.mp g2
  rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)] at g2'
  rw [tn_add _ _ (by simp; omega)] at g2'
  simp only [show (2 : UInt64).toNat = 2 from rfl, show (1 : UInt64).toNat = 1 from rfl, rA.2.2.1] at g2'
  obtain ⟨body, v, rest, evs⟩ : ∃ body v rest, st.vals = body :: v :: rest := by
    match hv : st.vals with
    | body :: v :: rest => exact ⟨body, v, rest, rfl⟩
    | [] => simp [hv] at g2'
    | [_] => simp [hv] at g2'
  have l0 : 0 < st.vals.length := by rw [evs]; simp
  have l1 : 1 < st.vals.length := by rw [evs]; simp
  have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
  have o1 := opCell rA.2.2.1 rA.2.2.2.1 1 l1
  simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl, show ((1 : Nat) + 1).toUInt64 = 2 from rfl] at o0 o1
  obtain ⟨_, rb⟩ := val_rep rA 0 l0
  obtain ⟨_, rv⟩ := val_rep rA 1 l1
  have fb := rb.fields; have fv := rv.fields
  simp only [fld] at fb fv
  rw [← o0] at fb; rw [← o1] at fv
  rw [ew] at fb; rw [et] at fb; rw [ez] at fv
  simp only [evs, List.getElem_cons_zero, List.getElem_cons_succ] at fb fv
  have W := v9_cw fv.2.2.2.1
  simp only [show d7 + 8192 + 3 * (zV - 5) + 2 = (d7 + 8192) + 3 * (zV - 5) + 2 from rfl] at W
  rw [W] at hs ⊢
  have R2 := rep_take (rep_31 R1 (cw v.sh).toUInt64) d hd
  have hw : ShOpt (bset (bset h1 31 (cw v.sh).toUInt64) 4 d.toUInt64) wB body.sh := by
    have := fb.2.2.2.1
    exact ShOpt.frame this (fun i a b => by rw [bget_bset' _ _ _ _ (by rw [show (4 : UInt64).toNat = 4 from rfl]; omega),
      bget_bset' _ _ _ _ (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)])
  rw [fb.2.2.2.2] at hs ⊢
  obtain ⟨st', em, R3⟩ := rep_v5g R2 hnf 2 5 s (cw v.sh) body.sh body.pend wB hw (by decide) (fun _ h5 => absurd rfl h5)
    (by decide) (by simpa using hs)
  refine ⟨[], st', ?_, by simpa using R3⟩
  simp only [stepF, evs]
  simp only [evs] at em
  rw [em]; rfl

end ParInv

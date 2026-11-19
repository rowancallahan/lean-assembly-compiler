/- Nano/V2Self/Proof/ParInvLetSemi: Layer-3 handler `letSemi x tl` (task 11, v116), box C: `;` after the value, the binder
at slot h[11], the body in the inherited tail mode, the LET end frame with the saved slot and depth. -/
import Nano.V2Self.Proof.ParInvIte
import Nano.V2Self.Proof.ParInvGroup
namespace ParInv
open C BufL ParSpec ParRun

/-- the slot counter h[11] (mod 2^64) -/
theorem rep_set11 {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (nx : Nat) :
    Rep (bset h 11 nx.toUInt64) ts { st with nx := nx } fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have u : (11 : UInt64).toNat = 11 := rfl
  have c : ∀ i : UInt64, i.toNat ≠ 11 → bget (bset h 11 nx.toUInt64) i = bget h i := fun i hi => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 11 nx.toUInt64) := ⟨c 7 (by decide), fun i hi => c i (by omega)⟩
  have es : ShTabAgree h (bset h 11 nx.toUInt64) := fun i a _ => c i (by omega)
  have ea : ArenaAgree h (bset h 11 nx.toUInt64) := fun i a _ => c i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide)]; exact r0, by rw [c 3 (by decide)]; exact tokAt_frame et hn r3,
    bget_bset_eq _ _ _ _ rfl (by rw [u, rO.1]; omega), binds_frame rB (c 4 (by decide)) (fun i a _ => c i (by omega)) et hn es,
    defs_frame rD (c 12 (by decide)) (c 27 (by decide)) (c 26 (by decide)) (fun i a _ => c i (by omega)) et hn es,
    arena_frame rA (c 8 (by decide)) (c 9 (by decide)) (fun i a _ => c i (by omega)) es,
    fun s hs => by rw [c 25 (by decide)]; exact (r25 s hs).frame es,
    fun y hy => by rw [c 29 (by decide)]; exact nameAt_frame et (by omega) (r29 y hy),
    by rw [c 30 (by decide)]; exact r30, by rw [c 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (c 5 (by decide)) (fun i a _ => c i (by omega)) et hn es ea rA.2.1⟩

theorem h_letSemi {h ts : Buf} {st : St} {x : List Nat} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.letSemi x tl :: fs))
    (hv : st.vals ≠ []) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letSemi x tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  have ea1 : NameAt (bset h 5 fs.length.toUInt64) a x := nameAt_ts r.1 R1.1 r.2.1 ea
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1 ea1
  have ev : step h = v116 h1 a (b01 tl) := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v116, v9, UInt64.add_zero] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c13 : bget h1 (d11 + bget h1 3) = 13
  · simp only [c13, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 13 c13 (by decide) (by decide) (by decide)
    generalize hH2 : bset h1 3 (bget h1 3 + 1) = H2 at hs R2 ⊢
    have rA := R2.2.2.2.2.2.2.2.1
    obtain ⟨top, vs, evs⟩ : ∃ top vs, st.vals = top :: vs := by
      match hq : st.vals with
      | [] => exact absurd hq hv
      | top :: vs => exact ⟨top, vs, rfl⟩
    have l0 : 0 < st.vals.length := by rw [evs]; simp
    have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
    simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
    obtain ⟨_, rt⟩ := val_rep rA 0 l0
    have ft : ShOpt H2 (bget H2 (d5 + 8 * bget H2 (d3 + bget H2 8 - 1) + 3)) top.sh := by
      have := rt.fields.2.2.2.1; simp only [fld] at this; rw [o0]; simpa [evs] using this
    generalize ew : bget H2 (d5 + 8 * bget H2 (d3 + bget H2 8 - 1) + 3) = w at hs ft ⊢
    by_cases w4 : w = 4
    · simp only [w4, beq_self_eq_true, if_true] at hs; exact absurd (stat0 _ (by rw [← hH2]; simp [length_bset]; omega)) hs
    · have nw : (w == 4) = false := by simpa using w4
      simp only [nw, Bool.false_eq_true, if_false] at hs ⊢
      have nnt : top.sh ≠ some .nt := by
        intro e; rw [e] at ft; exact w4 (ShapeCode.nt_code ft)
      have s11 : bget H2 11 = st.nx.toUInt64 := R2.2.2.2.2.1
      have j4 : (bget H2 4).toNat = st.binds.length := R2.2.2.2.2.2.1.1
      rw [s11] at hs ⊢
      have hl2 := (rep_bounds R2).2.1
      -- status survives backwards through the tail writes
      have z6 : ∀ g : Buf, bget g 0 = 0 → bget (v6 g a st.nx.toUInt64 w) 0 = 0 := by
        intro g hg; unfold v6; split
        · rename_i hc
          have hcN := UInt64.lt_iff_toNat_lt.mp hc; simp only [show d14.toNat = 1024 from rfl] at hcN
          have rc := fun k (hk : k.toNat < 4) => rowCell (bget g 4).toNat hcN k hk
          rw [bget_bset' _ _ _ _ (by decide)]
          rw [bget_bset' _ _ _ _ (by have := rc 3 (by decide); simp at this ⊢; omega),
            bget_bset' _ _ _ _ (by have := rc 2 (by decide); simp at this ⊢; omega),
            bget_bset' _ _ _ _ (by have := rc 1 (by decide); simp at this ⊢; omega),
            bget_bset' _ _ _ _ (by have := rc 0 (by decide); simp at this ⊢; omega)]; exact hg
        · rw [bget_bset]; split <;> simp_all
      have zb : ∀ (g : Buf) (k v : UInt64), k.toNat ≠ 0 → bget g 0 = 0 → bget (bset g k v) 0 = 0 :=
        fun g k v hk hg => by rw [bget_bset' _ _ _ _ (by simpa using hk)]; exact hg
      have st4 : bget (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) 0 ≠ 0 :=
        fun z => hs (z6 _ (zb _ 11 _ (by decide) (zb _ 31 _ (by decide) z)))
      have R3 := rep_push (.letEnd st.nx st.binds.length) st.nx.toUInt64 (bget H2 4) R2 (by simp [inDefF, Frame.isDefs])
        ⟨rfl, j4⟩ (pushOK st4)
      have R4 := rep_push (.expr 0 (bm tl)) 0 (b01 tl) R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, b01_toNat tl⟩ st4
      have o1 := v1_ok _ _ _ _ (pushOK st4)
      have o2 := v1_ok _ _ _ _ st4
      obtain ⟨_, a1, _⟩ := v1_agree H2 12 st.nx.toUInt64 (bget H2 4) o1 (by omega)
      obtain ⟨_, a2, _⟩ := v1_agree (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl) o2
        (by obtain ⟨L, _⟩ := v1_eff H2 12 st.nx.toUInt64 (bget H2 4) o1 (by omega); rw [L]; omega)
      have sh24 : ShTabAgree H2 (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) :=
        fun i x y => by rw [a2 i x y, a1 i x y]
      have R4' : Rep (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) ts { st with toks := rest }
          (.expr 0 (bm tl) :: .letEnd st.nx st.binds.length :: fs) := R4
      clear R4
      generalize hH4 : v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl) = H4 at hs R4' st4 sh24
      have R4 := R4'
      have l4 := (rep_bounds R4).2.1
      have ft4 : ShOpt H4 w top.sh := ft.frame sh24
      have eW := v9_cw ft4
      rw [eW] at hs ⊢
      rw [bget_bset_eq _ _ _ _ rfl (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)] at hs ⊢
      have R5 := rep_31 R4 (cw top.sh).toUInt64
      have en : st.nx.toUInt64 + (cw top.sh).toUInt64 = (st.nx + cw top.sh).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      rw [en] at hs ⊢
      have R6 := rep_set11 R5 (st.nx + cw top.sh)
      have sh6 : ShTabAgree H4 (bset (bset H4 31 (cw top.sh).toUInt64) 11 (st.nx + cw top.sh).toUInt64) :=
        fun i x y => by rw [bget_bset' _ _ _ _ (by rw [show (11 : UInt64).toNat = 11 from rfl]; omega),
          bget_bset' _ _ _ _ (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)]
      have R7 := rep_v6 R6 a st.nx.toUInt64 w x st.nx top.sh (nameAt_ts R1.1 R6.1 R1.2.1 ea1) rfl (ft4.frame sh6) hs
      refine ⟨[.expr 0 (bm tl), .letEnd st.nx st.binds.length], _, ?_, R7⟩
      simp [stepF, et, evs, nnt]
  · have n : (bget h1 (d11 + bget h1 3) == 13) = false := by simpa using c13
    simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv

/- Nano/V2Self/Proof/Parser/ParInvFinish: task 80 (FINISH a def, `v141`) on box C's Rep (parser lead).  The step is "two task pushes ++ the
6 header words"; B's `defEnd` emits the same words; Rep holds for the pushed heap (the output append is `rep_append`). -/
import Nano.V2Self.Proof.Parser.ParInvDefs
import Nano.V2Self.Proof.Parser.ParInvFlatM
import Nano.V2Self.Proof.Parser.ParInvIte
import Nano.V2Self.Proof.Parser.ParInvAppend
import Nano.V2Self.Proof.Parser.ParInvValRep
namespace ParInv
open C BufL ParSpec ParRun

theorem RNRep.shOpt {h : Buf} {u : UInt64} {n : RN} {ids : List UInt64} (r : RNRep h u n ids) : ShOpt h (fld h u 3) n.sh := by
  cases r with
  | mk _ _ _ a3 => exact a3

theorem cwC_eq {h : Buf} {w : UInt64} {o : Option Sh} (r : ShOpt h w o) : cwC h w = (cw o).toUInt64 := v9_cw r

/-- **task 80 core** -/
theorem h_defEnd_core {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.defEnd :: fs)) (hW : IsInpW)
    (hfs : inDefF fs = true) (hn20 : st.nx < 2 ^ 20) (hres20 : cw st.cur.res < 2 ^ 20) (hs : bget (step h) 0 ≠ 0) :
    ∃ H zn ws, step h = H ++ ws ∧
      stepF .defEnd st = some ([.flat zn, .defClose], { st with out := st.out ++ ws }) ∧
      Rep H ts st ([.flat zn, .defClose] ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  have ev : step h = v141 g a b := by rw [E]; rfl
  obtain ⟨hn, hlen, har⟩ := rep_bounds R1
  rw [ev, v141_eq g a b (by omega)] at hs ⊢
  simp only [] at hs ⊢
  generalize hz : bget g (d3 + bget g 8 - 1) = z at hs ⊢
  by_cases hc : bget g 8 = 1 ∧ bget g ((d5 + 8 * z) + 3) = bget g ((d7 + 8 * bget g 12) + 3) ∧ inpC g z ≠ 1
  · rw [if_pos hc] at hs ⊢
    obtain ⟨h8, hsh, hinp⟩ := hc
    have rD := R1.2.2.2.2.2.2.1
    rw [hfs] at rD
    obtain ⟨d12, _, _, _, dcur, _, _⟩ := rD
    simp only [if_true] at dcur
    obtain ⟨⟨⟨_, rnpw, _, rres, rloop, _, _, _⟩, _⟩, dlt⟩ := dcur
    have rA := R1.2.2.2.2.2.2.2.1
    obtain ⟨a9, ale, a8, vle, I, hI, hops, _, _⟩ := rA
    have hv1 : st.vals.length = 1 := by rw [← a8, h8]; rfl
    obtain ⟨zn, hvz⟩ : ∃ zn, st.vals = [zn] := by
      match hv : st.vals, hv1 with
      | [zn], _ => exact ⟨zn, rfl⟩
    obtain ⟨hzA, hzn, _⟩ := hops 0 (by omega)
    generalize hz0 : opAt g (st.vals.length - 1 - 0) = z0 at hzA hzn
    have hzz : z = z0 := by
      rw [← hz0, ← hz, hv1, h8]; unfold opAt; rfl
    subst hzz
    simp only [hvz, List.getElem_cons_zero] at hzn
    obtain ⟨rz, _, _⟩ := hI z.toNat hzA
    rw [hzn] at rz
    have zz : z.toNat.toUInt64 = z := by apply UInt64.toNat_inj.mp; simp [Nat.toUInt64]
    rw [zz] at rz
    have hj : bget g 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp [Nat.toUInt64]; omega
    rw [hj] at hsh hs ⊢
    -- shapes and the input test
    have rzsh : ShOpt g (fld g z 3) zn.sh := rz.shOpt
    have rzsh' : ShOpt g (bget g (d7 + 8 * st.defs.length.toUInt64 + 3)) zn.sh := by rw [← hsh]; exact rzsh
    have hshape : zn.sh = st.cur.res := ShOpt.det' rzsh' rres
    have hni : zn.isInp = false := by
      have := inpC_isInp hW rz
      cases hi : zn.isInp
      · rfl
      · rw [hi] at this; exact absurd this hinp
    have r11 : bget g 11 = st.nx.toUInt64 := R1.2.2.2.2.1
    rw [rnpw, r11, rloop, cwC_eq rres] at hs ⊢
    have hH0 : bget (v1 (v1 (bset g 31 (cw st.cur.res).toUInt64) 83 0 0) 81 z 0) 0 ≠ 0 := by
      rw [bget_append_lt _ _ _ (by simp [v1_length, length_bset]; omega)] at hs; exact hs
    refine ⟨v1 (v1 (bset g 31 (cw st.cur.res).toUInt64) 83 0 0) 81 z 0, zn, _, rfl, ?_, ?_⟩
    · simp [stepF, hvz, hshape, hni, b01, hn20, hres20]
    · have R2 := rep_scratch (h' := bset g 31 (cw st.cur.res).toUInt64) R1
        (fun i _ a31 => bget_bset' g 31 i _ (fun e => a31 (by rw [← e]; rfl))) (drop_bset _ _ _ (by decide))
      have R3 := rep_push .defClose 0 0 R2 (by simp [inDefF, Frame.isDefs]) trivial (fun e => hH0 (v1_zero _ _ _ _ e))
      have hf : FrameArgs (v1 (bset g 31 (cw st.cur.res).toUInt64) 83 0 0) st.arena (.flat zn) z 0 := by
        obtain ⟨_, _, _, _, I3, hI3, _⟩ := R3.2.2.2.2.2.2.2.1
        obtain ⟨rz3, _, hb3⟩ := hI3 z.toNat hzA
        rw [hzn, zz] at rz3
        exact ⟨I3 z.toNat, rz3, hb3⟩
      have R4 := rep_push (.flat zn) z 0 R3 (by simp [inDefF, Frame.isDefs]) hf hH0
      exact R4
  · rw [if_neg hc] at hs; exact absurd (status_bset0 g) hs


/-- **task 80** (FINISH a def) on C's Rep, including the output append -/
theorem h_defEnd {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.defEnd :: fs)) (hfs : inDefF fs = true)
    (hn20 : st.nx < 2 ^ 20) (hres20 : cw st.cur.res < 2 ^ 20)
    (hs : bget (step h) 0 ≠ 0) : ∃ k st', stepF .defEnd st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨H, zn, ws, e, e2, R⟩ := h_defEnd_core r isInpW hfs hn20 hres20 hs
  exact ⟨_, _, e2, by rw [e]; exact rep_append R ws⟩

end ParInv

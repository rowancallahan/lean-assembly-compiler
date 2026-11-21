/- Nano/Parser/ParInvIte: Layer-3 handler `mkIte c` (task 9, v111), box C: the IF node over (lhs, rhs, then, else);
side condition from B's WF: no flatten frame pending. -/
import Nano.Parser.ParInvLetEnd
namespace ParInv
open C BufL ParSpec ParRun

/-- a shape code decodes to one optional shape -/
theorem ShOpt.det' {h : Buf} {c : UInt64} {o o' : Option Sh} (r : ShOpt h c o) (r' : ShOpt h c o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some s' => simp only [ShOpt] at r r'; subst r; cases r' with | pr h5 => simp at h5
  | some s =>
    cases o' with
    | none => simp only [ShOpt] at r r'; subst r'; cases r with | pr h5 => simp at h5
    | some s' => exact congrArg some (ShapeCode.det r r')

theorem b01_or (p q : Bool) : b01 p ||| b01 q = b01 (p || q) := by cases p <;> cases q <;> rfl

theorem h_mkIte {h ts : Buf} {st : St} {c : Nat} {fs : List Frame} (r : Rep h ts st (.mkIte c :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.mkIte c) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  have ea' : a = c.toUInt64 := by rw [← ea]; simp
  have hc : c < 2 ^ 64 := by rw [← ea]; exact a.toNat_lt
  subst ea'
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have rA := R1.2.2.2.2.2.2.2.1
  have h8le : (bget h1 8).toNat ≤ 4096 := by rw [rA.2.2.1]; exact rA.2.2.2.1
  generalize e4 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 4) + 3) = cA
  generalize e3 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 3) + 3) = cB
  generalize e2 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) = cT
  generalize e1 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) = cE
  generalize p2 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 4) = pT
  generalize p1 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 4) = pE
  have ev : step h = (if cA == 1 then if cB == 1 then if cT == cE then v5 h1 4 c.toUInt64 0 cE (pT ||| pE) 4
      else bset h1 0 0 else bset h1 0 0 else bset h1 0 0) := by
    rw [E]; simp only [Frame.code, v96, v111, e4, e3, e2, e1, p2, p1]; simp
  rw [ev] at hs ⊢
  have dead : ∀ g : Buf, g = bset h1 0 0 → bget g 0 ≠ 0 → False := fun g e hg => hg (by rw [e]; exact stat0 _ (by omega))
  by_cases ca : cA = 1
  · by_cases cb : cB = 1
    · by_cases ct : cT = cE
      · simp only [ca, cb, ct, beq_self_eq_true, if_true] at hs ⊢
        obtain ⟨_, g2, _⟩ := v5_guards _ _ _ _ _ _ _ (by omega) hs
        have g2' := UInt64.lt_iff_toNat_lt.mp g2
        rw [tn_add _ _ (by simp; omega)] at g2'
        simp only [show (4 : UInt64).toNat = 4 from rfl, show (1 : UInt64).toNat = 1 from rfl, rA.2.2.1] at g2'
        obtain ⟨ve, vt, vb, va, rest, evs⟩ : ∃ ve vt vb va rest, st.vals = ve :: vt :: vb :: va :: rest := by
          match hv : st.vals with
          | ve :: vt :: vb :: va :: rest => exact ⟨ve, vt, vb, va, rest, rfl⟩
          | [] => simp [hv] at g2'
          | [_] => simp [hv] at g2'
          | [_, _] => simp [hv] at g2'
          | [_, _, _] => simp [hv] at g2'
        have lk : ∀ k, k < 4 → k < st.vals.length := fun k hk => by rw [evs]; simp; omega
        have oc : ∀ k (hk : k < 4), bget h1 (d3 + bget h1 8 - (k + 1).toUInt64) = opAt h1 (st.vals.length - 1 - k) :=
          fun k hk => opCell rA.2.2.1 rA.2.2.2.1 k (lk k hk)
        have fk : ∀ k (hk : k < 4), ∃ ids, RNRep h1 (bget h1 (d3 + bget h1 8 - (k + 1).toUInt64)) (st.vals[k]'(lk k hk)) ids := by
          intro k hk; rw [oc k hk]; exact val_rep rA k (lk k hk)
        obtain ⟨_, rE⟩ := fk 0 (by decide); obtain ⟨_, rT⟩ := fk 1 (by decide)
        obtain ⟨_, rB⟩ := fk 2 (by decide); obtain ⟨_, rA'⟩ := fk 3 (by decide)
        have fE := rE.fields; have fT := rT.fields; have fB := rB.fields; have fA := rA'.fields
        simp only [fld, show ((0 : Nat) + 1).toUInt64 = 1 from rfl, show ((1 : Nat) + 1).toUInt64 = 2 from rfl,
          show ((2 : Nat) + 1).toUInt64 = 3 from rfl, show ((3 : Nat) + 1).toUInt64 = 4 from rfl] at fE fT fB fA
        rw [e1, p1] at fE; rw [e2, p2] at fT; rw [e3] at fB; rw [e4] at fA
        simp only [evs, List.getElem_cons_zero, List.getElem_cons_succ] at fE fT fB fA
        rw [ca] at fA; rw [cb] at fB; rw [ct] at fT
        have sa := shOpt_one fA.2.2.2.1; have sb := shOpt_one fB.2.2.2.1
        have stE := ShOpt.det' fT.2.2.2.1 fE.2.2.2.1
        rw [fT.2.2.2.2, fE.2.2.2.2, b01_or] at hs ⊢
        obtain ⟨st', em, R2⟩ := rep_v5g R1 hnf 4 4 c 0 ve.sh (vt.pend || ve.pend) cE fE.2.2.2.1 (by decide)
          (fun _ _ => ⟨hc, by decide⟩) (by decide) (by simpa using hs)
        refine ⟨[], st', ?_, by simpa using R2⟩
        simp only [stepF, evs, sa, sb, stE, and_self, if_true]
        rw [em]; rfl
      · have n : (cT == cE) = false := by simpa using ct
        simp only [ca, cb, n, beq_self_eq_true, if_true, if_false] at hs; exact (dead _ rfl hs).elim
    · have n : (cB == 1) = false := by simpa using cb
      simp only [ca, n, beq_self_eq_true, if_true, if_false] at hs; exact (dead _ rfl hs).elim
  · have n : (cA == 1) = false := by simpa using ca
    simp only [n, if_false] at hs; exact (dead _ rfl hs).elim

end ParInv

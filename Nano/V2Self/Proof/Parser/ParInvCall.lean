/- Nano/V2Self/Proof/Parser/ParInvCall: Layer-3 handler preservation, ARGUMENTS / CALLS (box G): tasks 44 `args` (v119), 45 `mkCallN` (v121).
Shape as ParInvExpr: `Rep h ts st (f :: fs) → bget (step h) 0 ≠ 0 → ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs)`,
with the side fact the top glue has from `WF`: `d ≤ |vals|` (task 45).
Generic: `rep_pop` (the popped heap still represents `fs`), `rep_push` (one `v1` push that did not fail). -/
import Nano.V2Self.Proof.Parser.ParInvExpr
import Nano.V2Self.Proof.Parser.ParRunCall
namespace ParInv
open C BufL ParSpec ParRun

/-- **pop**: the handler of `f` runs on the popped heap, which represents the rest of the stack -/
theorem rep_pop {h ts : Buf} {st : St} {f : Frame} {fs : List Frame} (r : Rep h ts st (f :: fs))
    (hD : inDefF fs = inDefF (f :: fs)) :
    let t := taskAt h fs.length
    step h = v96 (bset h 5 fs.length.toUInt64) f.code.toUInt64 t.a t.b ∧ FrameArgs h st.arena f t.a t.b ∧
      Rep (bset h 5 fs.length.toUInt64) ts st fs := by
  intro t
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  obtain ⟨E, A, T1⟩ := step_top (ts := ts) r.2.2.2.2.2.2.2.2.2.2.2.2.2 (by omega) hn har
  refine ⟨E, A, rep_tasks r (by simp [length_bset]) (fun i h5 _ => bget_bset' _ _ _ _ (by simp; omega)) (drop_bset _ _ _ (by simp)) T1 hD⟩

/-- **push**: a `v1` that leaves the status nonzero extends the represented stack by its frame -/
theorem rep_push {h ts : Buf} {st : St} {fs : List Frame} (f : Frame) (a b : UInt64) (r : Rep h ts st fs)
    (hD : inDefF (f :: fs) = inDefF fs) (hf : FrameArgs h st.arena f a b) (hs : bget (v1 h f.code.toUInt64 a b) 0 ≠ 0) :
    Rep (v1 h f.code.toUInt64 a b) ts st (f :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  have hg := v1_ok _ _ _ _ hs
  have rT := r.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨L, _, _, U⟩ := v1_eff h f.code.toUInt64 a b hg (by omega)
  have T := tasks_push f a b rT (by rw [← rT.1]; exact hg) (by omega) hn har hf
  exact rep_tasks r L (fun i h5 hi => U i h5 (by omega)) (drop_v1 _ _ _ _ hl) T hD

/-! ## task 44: `args c k` (v119) -/
theorem h_args {h ts : Buf} {st : St} {c : Callee} {k : Nat} {fs : List Frame} (r : Rep h ts st (.args c k :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.args c k) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  match k with
  | 0 =>
    have b0 : b = 0 := UInt64.toNat_inj.mp eb
    subst b0
    have ev : step h = bset h 5 fs.length.toUInt64 := by rw [E]; simp [v96, v119]
    rw [ev]
    exact ⟨[], st, args_zero c st, R1⟩
  | k + 1 =>
    have bne : b ≠ 0 := fun z => by subst z; simp at eb
    have ev : step h = v1 (v1 (bset h 5 fs.length.toUInt64) 44 a (b - 1)) 43 0 0 := by rw [E]; simp [v96, v119, bne]
    rw [ev] at hs ⊢
    have eb1 : (b - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have R2 := rep_push (.args c k) a (b - 1) R1 (by simp [inDefF, Frame.isDefs]) ⟨ea, eb1⟩ (fun z => hs (v1_zero _ _ _ _ z))
    have R3 := rep_push .argAtom 0 0 R2 rfl trivial hs
    exact ⟨[.argAtom, .args c k], st, args_succ c k st, R3⟩

/-! ## task 45: `mkCallN c d` (v121) -/
theorem h_mkCallN {h ts : Buf} {st : St} {c : Callee} {d : Nat} {fs : List Frame} (r : Rep h ts st (.mkCallN c d :: fs))
    (hd : d ≤ st.vals.length) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.mkCallN c d) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  have e8 : (bget h 8).toNat = st.vals.length := r.2.2.2.2.2.2.2.1.2.2.1
  have e8' : bget (bset h 5 fs.length.toUInt64) 8 = bget h 8 := bget_bset' _ _ _ _ (by decide)
  have en : (bget h 8 - b).toNat = st.vals.length - d := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega
  have ev : step h = v1 (v1 (bset h 5 fs.length.toUInt64) 48 a (bget h 8 - b)) 47 a (bget h 8 - b) := by
    rw [E]; simp [v96, v121, e8']
  rw [ev] at hs ⊢
  have R2 := rep_push (.mkCall c (st.vals.length - d)) a (bget h 8 - b) R1 (by simp [inDefF, Frame.isDefs]) ⟨ea, en⟩ (fun z => hs (v1_zero _ _ _ _ z))
  have R3 := rep_push (.argCheck c (st.vals.length - d)) a (bget h 8 - b) R2 rfl ⟨ea, en⟩ hs
  exact ⟨_, st, mkCallN_eq c d st, R3⟩

end ParInv

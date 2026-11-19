/- Nano/V2Self/Proof/ParInvTop: the TOP GLUE of the parser proof (parser lead).  Given
* a representation relation `Rep h fs st` between machine heaps and Layer-2 configurations with the properties `RepAPI`
  (initial state, one-step simulation "the machine did not fail ⇒ `stepF` steps and `Rep` holds again", task count, status,
  heap length / output words, main-def cells) — Layer 3, boxes C / D / parser lead;
* Layer-2 soundness `Accepts toks o → ∃ p, ParsesProgram ts p ∧ o = serialize p` — box B;
this file derives `ParserSound ts`.  `RepAPI` is the exact contract Layer 3 has to meet. -/
import Nano.V2Self.Proof.ParInvFin
import Nano.V2Self.Proof.ParTreeOK
namespace ParInv
open C BufL ParSpec ParRun

/-- what Layer 3 provides: `Rep` relates running (status 1) and accepted (status 2) heaps to Layer-2 configurations -/
structure RepAPI (ts : Buf) (toks : List Tok) (Rep : Buf → List Frame → St → Prop) : Prop where
  /-- the loaded heap with the initial task 60 -/
  init : Rep (v1 (entryHeap ts) 60 0 0) [.defs] (ParRun.init toks)
  /-- status: running, or accepted with the task stack empty -/
  status : ∀ {h fs st}, Rep h fs st → bget h 0 = 1 ∨ (bget h 0 = 2 ∧ fs = [] ∧ st.acc = true)
  /-- the task count cell -/
  ntasks : ∀ {h fs st}, Rep h fs st → bget h 0 = 1 → (bget h 5 = 0 ↔ fs = [])
  /-- one machine step that does not fail is one `stepF` step -/
  step : ∀ {h f fs st}, Rep h (f :: fs) st → bget h 0 = 1 → bget (step h) 0 ≠ 0 →
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) (k ++ fs) st'
  /-- heap = 184384 layout cells, the tokens, the sentinel 0, then the output words (which start with the IRV word 2) -/
  len : ∀ {h fs st}, Rep h fs st → h.length = 184385 + ts.length + st.out.length
  out : ∀ {h fs st}, Rep h fs st → h.drop (184385 + ts.length) = st.out
  /-- the cells `fin` checks are `mainOK` -/
  main : ∀ {h fs st}, Rep h fs st → bget h 0 = 2 → 0 < bget h 12 → MainCells h → mainOK st = true

theorem status_bset0 (h : Buf) : bget (bset h 0 0) 0 = 0 := by
  rw [bget_bset]; by_cases hl : 0 < h.length <;> simp [hl, bget, List.getD]

/-- a failed or exhausted run never shows status 2 -/
theorem v97_dead (N : Nat) (h : Buf) (h0 : bget h 0 = 0) : bget (v97 N h) 0 = 0 := by
  cases N with
  | zero => exact status_bset0 h
  | succ n => rw [v97_stopped n h (by rw [h0]; decide)]; exact h0

/-- **the run**: if the task machine ends with status 2, the Layer-2 configuration runs to the empty stack and is accepted -/
theorem run_sim {ts : Buf} {toks : List Tok} {Rep : Buf → List Frame → St → Prop} (api : RepAPI ts toks Rep) :
    ∀ (N : Nat) (h : Buf) (fs : List Frame) (st : St), Rep h fs st → bget (v97 N h) 0 = 2 →
      ∃ m st', m ≤ N ∧ StarN m (fs, st) ([], st') ∧ Rep (v97 N h) [] st' ∧ st'.acc = true
  | 0, h, fs, st, _, h2 => by
    rw [show v97 0 h = bset h 0 0 from rfl, status_bset0] at h2; exact absurd h2 (by decide)
  | N + 1, h, fs, st, hr, h2 => by
    rcases api.status hr with h1 | ⟨hs, rfl, ha⟩
    · by_cases hg : bget h 5 = 0
      · exfalso
        have : v97 (N + 1) h = bset h 0 0 := by simp [v97, h1, hg]
        rw [this, status_bset0] at h2; exact absurd h2 (by decide)
      · rw [v97_running N h h1 hg] at h2 ⊢
        by_cases hd : bget (step h) 0 = 0
        · rw [v97_dead N _ hd] at h2; exact absurd h2 (by decide)
        · match fs, hr with
          | [], hr => exact absurd ((api.ntasks hr h1).mpr rfl) hg
          | f :: fs', hr =>
            obtain ⟨k, st1, hk, hr1⟩ := api.step hr h1 hd
            obtain ⟨m, st', hm, hs, hr', ha⟩ := run_sim api N (step h) (k ++ fs') st1 hr1 h2
            exact ⟨m + 1, st', by omega, .step (stepS_some.mpr ⟨k, st1, hk, rfl⟩) hs, hr', ha⟩
    · have hst : v97 (N + 1) h = h := v97_stopped N h (by rw [hs]; decide)
      rw [hst]
      exact ⟨0, st, by omega, .refl _, hr, ha⟩

/-- **ParserSound from the two layers** -/
theorem parserSound_of {ts : Buf} {toks : List Tok} {Rep : Buf → List Frame → St → Prop} (api : RepAPI ts toks Rep)
    (hx : ts.length ≤ 16777216)
    (sound : ∀ o, Accepts toks o → ∃ p, ParsesProgram ts p ∧ o = serialize p) : ParserSound ts := by
  intro hne
  have e : y16 ts = fin ts 1 (v97 16777216 (v1 (entryHeap ts) 60 0 0)) := v99_eq ts 1 hx
  rw [e] at hne ⊢
  generalize hH : v97 16777216 (v1 (entryHeap ts) 60 0 0) = H at hne ⊢
  -- status 2 is forced by a non-empty result
  have h2 : bget H 0 = 2 := by
    by_cases h2 : bget H 0 = 2
    · exact h2
    · exfalso; apply hne; simp [fin, h2, bnew]
  obtain ⟨m, st', hm, hs, hr, ha⟩ := run_sim api 16777216 _ _ _ api.init (by rw [hH]; exact h2)
  rw [hH] at hr
  have hlen := api.len hr
  have hout := api.out hr
  have hob : st'.out.length ≤ 1 + 6 * m := by
    have := hs.out_le
    simpa [ParRun.init] using this
  have hj : (d11 + bsize ts + 1).toNat = 184385 + ts.length := by
    have e1 : (bsize ts).toNat = ts.length := by simp [bsize, Nat.toUInt64]; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, d11v, e1]; simp; omega
  obtain ⟨_, h12, hmc, hfin⟩ := fin_ne ts H (by rw [hlen]; omega) (by rw [hj, hlen]; omega) hne
  rw [hfin, hj, hout]
  exact sound _ ⟨st', hs.toStar, ha, api.main hr h2 h12 hmc, rfl⟩

end ParInv

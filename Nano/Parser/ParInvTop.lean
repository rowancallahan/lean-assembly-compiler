/- Nano/Parser/ParInvTop: the TOP GLUE of the parser proof (parser lead).  Given
* a representation relation `Rep h fs st` between machine heaps and Layer-2 configurations with the properties `RepAPI`
  (initial state, one-step simulation "the machine did not fail ⇒ `stepF` steps and `Rep` holds again", task count, status,
  heap length / output words, main-def cells) — Layer 3, boxes C / D / parser lead;
* Layer-2 soundness `Accepts toks o → ∃ p, ParsesProgram ts p ∧ o = serialize p` — box B;
this file derives `ParserSound ts`.  `RepAPI` is the exact contract Layer 3 has to meet. -/
import Nano.Parser.ParInvFin
import Nano.Parser.ParTreeOK
namespace ParInv
open C BufL ParSpec ParRun

/-- what Layer 3 provides: `Rep` relates RUNNING heaps (status 1) to Layer-2 configurations; the accepting step is a separate field,
so no relation is needed at the accepting heap -/
structure RepAPI (ts : Buf) (toks : List Tok) (Rep : Buf → List Frame → St → Prop) : Prop where
  /-- the loaded heap with the initial task 60 -/
  init : Rep (v1 (entryHeap ts) 60 0 0) [.defs] (ParRun.init toks)
  /-- represented heaps are running -/
  running : ∀ {h fs st}, Rep h fs st → bget h 0 = 1
  /-- the task count cell -/
  ntasks : ∀ {h fs st}, Rep h fs st → (bget h 5 = 0 ↔ fs = [])
  /-- one machine step that keeps running is one `stepF` step -/
  step : ∀ {h f fs st}, Rep h (f :: fs) st → bget (step h) 0 = 1 →
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) (k ++ fs) st'
  /-- the accepting step (status 2): `stepF` accepts with nothing left, and the final heap is
  185408 layout cells, the tokens, the sentinel 0, then the output words; its main-def cells are `mainOK` -/
  accept : ∀ {h f fs st}, Rep h (f :: fs) st → bget (ParInv.step h) 0 = 2 →
    ∃ st', stepF f st = some ([], st') ∧ fs = [] ∧ st'.acc = true ∧
      (ParInv.step h).length = 185409 + ts.length + st'.out.length ∧
      ((ParInv.step h).length < 2 ^ 64 → (ParInv.step h).drop (185409 + ts.length) = st'.out) ∧
      (0 < bget (ParInv.step h) 12 → MainCells (ParInv.step h) → mainOK st' = true)

theorem status_bset0 (h : Buf) : bget (bset h 0 0) 0 = 0 := by
  rw [bget_bset]; by_cases hl : 0 < h.length <;> simp [hl, bget, List.getD]

/-- **the run**: if the task machine ends with status 2, the Layer-2 configuration runs to the empty stack, is accepted, and the
final heap carries the output and main facts -/
theorem run_sim {ts : Buf} {toks : List Tok} {Rep : Buf → List Frame → St → Prop} (api : RepAPI ts toks Rep) :
    ∀ (N : Nat) (h : Buf) (fs : List Frame) (st : St), Rep h fs st → bget (v97 N h) 0 = 2 →
      ∃ m st', m ≤ N ∧ StarN m (fs, st) ([], st') ∧ st'.acc = true ∧
        (v97 N h).length = 185409 + ts.length + st'.out.length ∧
        ((v97 N h).length < 2 ^ 64 → (v97 N h).drop (185409 + ts.length) = st'.out) ∧
        (0 < bget (v97 N h) 12 → MainCells (v97 N h) → mainOK st' = true)
  | 0, h, fs, st, _, h2 => by
    rw [show v97 0 h = bset h 0 0 from rfl, status_bset0] at h2; exact absurd h2 (by decide)
  | N + 1, h, fs, st, hr, h2 => by
    have h1 := api.running hr
    by_cases hg : bget h 5 = 0
    · exfalso
      have : v97 (N + 1) h = bset h 0 0 := by simp [v97, h1, hg]
      rw [this, status_bset0] at h2; exact absurd h2 (by decide)
    · rw [v97_running N h h1 hg] at h2 ⊢
      match fs, hr with
      | [], hr => exact absurd ((api.ntasks hr).mpr rfl) hg
      | f :: fs', hr =>
        by_cases s1 : bget (step h) 0 = 1
        · obtain ⟨k, st1, hk, hr1⟩ := api.step hr s1
          obtain ⟨m, st', hm, hs, ha, hl, ho, hmn⟩ := run_sim api N (step h) (k ++ fs') st1 hr1 h2
          exact ⟨m + 1, st', by omega, .step (stepS_some.mpr ⟨k, st1, hk, rfl⟩) hs, ha, hl, ho, hmn⟩
        · cases N with
          | zero =>
            rw [show v97 0 (step h) = bset (step h) 0 0 from rfl, status_bset0] at h2; exact absurd h2 (by decide)
          | succ N =>
            have hst : v97 (N + 1) (step h) = step h := v97_stopped N (step h) s1
            rw [hst] at h2 ⊢
            obtain ⟨st', hk, rfl, ha, hl, ho, hmn⟩ := api.accept hr h2
            exact ⟨1, st', by omega, .step (stepS_some.mpr ⟨[], st', hk, rfl⟩) (.refl _), ha, hl, ho, hmn⟩

/-- **ParserSound from the two layers** -/
theorem parserSound_of {ts : Buf} {toks : List Tok} {Rep : Buf → List Frame → St → Prop} (api : RepAPI ts toks Rep)
    (hx : ts.length ≤ 16777216)
    (sound : ∀ o, Accepts toks o → ∃ p, ParsesProgram ts p ∧ o = serialize p) : ParserSound ts := by
  intro hne
  have e : y16 ts = fin ts 1 (v97 16777216 (v1 (entryHeap ts) 60 0 0)) := v99_eq ts 1 hx
  rw [e] at hne ⊢
  generalize hH : v97 16777216 (v1 (entryHeap ts) 60 0 0) = H at hne ⊢
  have h2 : bget H 0 = 2 := by
    by_cases h2 : bget H 0 = 2
    · exact h2
    · exfalso; apply hne; simp [fin, h2, bnew]
  obtain ⟨m, st', hm, hs, ha, hlen, hout, hmain⟩ := run_sim api 16777216 _ _ _ api.init (by rw [hH]; exact h2)
  rw [hH] at hlen hout hmain
  have hob : st'.out.length ≤ 1 + 6 * m := by
    have := hs.out_le
    simpa [ParRun.init] using this
  have hj : (d11 + bsize ts + 1).toNat = 185409 + ts.length := by
    have e1 : (bsize ts).toNat = ts.length := by simp [bsize, Nat.toUInt64]; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, d11v, e1]; simp; omega
  have hHl : H.length < 2 ^ 64 := by rw [hlen]; omega
  obtain ⟨_, h12, hmc, hfin⟩ := fin_ne ts H hHl (by rw [hj, hlen]; omega) hne
  rw [hfin, hj, hout hHl]
  exact sound _ ⟨st', hs.toStar, ha, hmain h12 hmc, rfl⟩

end ParInv

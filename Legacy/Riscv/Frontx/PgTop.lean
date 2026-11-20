/- Paged arrays (NOTES section 35): `CompileRunsWeak` and `CompileCorrectWeak` (`Compiler/AllocSpec.lean`) for the paged
compiler `compile : PgProg → Option CompiledA`.

* `PgProg`: a paged program over the input bytes (`Pg [.ar .ba] R`, scalar or array result).  Its meaning
  `PgProg.run` is its Lean semantics `Pg.Den` (loops through `Runs`), with the result as bytes (`outEnc`: a scalar
  as 8 bytes little-endian, an array as `encArr`).
* `compile`: the stub `pgStub` (the `a0` flag, `PgMem.lean`) followed by the paged code (`pgCodeS` / `pgCodeA`);
  cells are pages of 8192 bytes; the events of an input are those of its run (`Pg.GoodE`, oldest first) reversed,
  after one page for the frame (`events = E.reverse ++ [.alloc 1]`), so `memoryNeeded = 8192 * (pk 0 E + 1)`.
* `Good`: the checks of `implements1_pgSQ` / `implements1_pgAQ` and that every input up to `maxIn` bytes has a run
  with events (`GoodE`: the side conditions of the source, e.g. indices in range, sizes below `P * P`); longer
  inputs have no meaning (`run = none`), so a program whose arrays grow is compiled for the inputs it can serve. -/
import Legacy.Riscv.Frontx.PgMem
import Legacy.Riscv.Frontx.WpMem

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Proven.WA
open Proven Proven.WP Proven.Top Proven.Top.Alloc Proven.Mach.Riscv
open Proven.Frontx (Res)

/-! ## Page events are allocations -/

def AllocsOnly (E : List MemEvent) : Prop := ∀ e ∈ E, ∃ n, e = .alloc n

theorem allocs_nil : AllocsOnly [] := fun _ h => nomatch h

theorem allocs_append {a b : List MemEvent} (ha : AllocsOnly a) (hb : AllocsOnly b) : AllocsOnly (a ++ b) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact ha e h
  · exact hb e h

theorem allocs_cons1 {E : List MemEvent} (h : AllocsOnly E) : AllocsOnly (.alloc 1 :: E) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | h'
  · exact ⟨1, rfl⟩
  · exact h e h'

theorem pushEvs_allocs (n : Nat) : AllocsOnly (pushEvs n) := PgEx.pushFrom_allocs 0 n

theorem F.evsP_allocs (L : List PLoc) {Γ : List Sl} {k : AK} (f : F Γ k) (v : Vals Γ) :
    AllocsOnly (F.evsP L f v) := by
  cases f with
  | rep n x => exact allocs_cons1 (pushEvs_allocs _)
  | const c => exact allocs_nil
  | empty => exact allocs_cons1 allocs_nil
  | extract m lo hi => exact allocs_cons1 (pushEvs_allocs _)
  | data m => simp only [F.evsP]; split
              · exact allocs_nil
              · exact allocs_cons1 (pushEvs_allocs _)
  | alias m => simp only [F.evsP]; split
               · exact allocs_nil
               · exact allocs_cons1 (pushEvs_allocs _)

theorem A.evs_allocs {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ), AllocsOnly (a.evs v)
  | .var _, _ => allocs_nil
  | .set a _ _, v => A.evs_allocs a v
  | .push a _, v => by
    simp only [A.evs]
    refine allocs_append (A.evs_allocs a v) ?_
    split
    · exact allocs_cons1 allocs_nil
    · exact allocs_nil
  | .ite c a b, v => by
    simp only [A.evs]
    split
    · exact A.evs_allocs a v
    · exact A.evs_allocs b v

theorem Args.evs_allocs {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (v : Vals Γ), AllocsOnly (as.evs v)
  | _, .nil, _ => allocs_nil
  | _, @Args.cons _ (.sc _) _ _ as, v => by simp only [Args.evs]; exact Args.evs_allocs as v
  | _, @Args.cons _ (.ar _) _ a as, v => by
    simp only [Args.evs]; exact allocs_append (A.evs_allocs a v) (Args.evs_allocs as v)

theorem T.evs_allocs : ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (v : Vals Γ), AllocsOnly (b.evs v)
  | _, _, _, .ret _, _ => allocs_nil
  | _, _, _, .call as, v => by simp only [T.evs]; exact Args.evs_allocs as v
  | _, _, _, .ite c a b, v => by
    simp only [T.evs]
    split
    · exact T.evs_allocs a v
    · exact T.evs_allocs b v
  | _, _, _, .let_ e k, v => by simp only [T.evs]; exact T.evs_allocs k _

theorem RunsE.allocs {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    {E : List MemEvent} (h : RunsE b c s r E) : AllocsOnly E := by
  induction h with
  | ret _ => exact allocs_nil
  | call _ _ ih => exact allocs_append (T.evs_allocs _ _) ih

theorem Inis.evsP_allocs (L : List PLoc) {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (v : Vals Γ),
    AllocsOnly (xs.evsP L v)
  | _, .nil, _ => allocs_nil
  | _, .cons (s := .sc _) x xs, v => by
    simp only [Inis.evsP, Ini.evsP, List.nil_append]; exact Inis.evsP_allocs L xs v
  | _, .cons (s := .ar _) x xs, v => by
    simp only [Inis.evsP, Ini.evsP]; exact allocs_append (F.evsP_allocs L x v) (Inis.evsP_allocs L xs v)

theorem Pg.goodE_allocs {Γ : List Sl} {R : Sl} (p : Pg Γ R) : ∀ (L : List PLoc) (d : Nat) (v : Vals Γ) (y : R.T)
    (E : List MemEvent), p.GoodE L d v y E → AllocsOnly E := by
  induction p with
  | ret r =>
    intro L d v y E h
    rename_i R
    cases R
    · rw [h.2.2]; exact allocs_nil
    · rw [h.2]; exact allocs_nil
  | let_ x k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, E2, h2, rfl⟩ := h <;>
      exact allocs_append (by cases s <;> simp only [Ini.evsP] <;> first | exact allocs_nil | exact F.evsP_allocs L _ v)
        (ih _ _ _ _ _ h2)
  | loop Δ b init k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, r, P, Eb, Ek, -, -, -, hr, hk, rfl⟩ := h <;>
      exact allocs_append (Inis.evsP_allocs L init v) (allocs_append hr.allocs (ih _ _ _ _ _ hk))

/-! ## The meaning: `GoodE` runs agree with `Pg.Den`, which is deterministic -/

theorem Runs.det' {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r r' : R.T}
    (h : Runs b c s r) (h' : Runs b c s r') : r = r' := by
  obtain ⟨E, hE⟩ := runsE_of h
  obtain ⟨E', hE'⟩ := runsE_of h'
  exact (hE.det hE').1

theorem Pg.goodE_den {Γ : List Sl} {R : Sl} (p : Pg Γ R) : ∀ (L : List PLoc) (d : Nat) (v : Vals Γ) (y : R.T)
    (E : List MemEvent), p.GoodE L d v y E → p.Den v y := by
  induction p with
  | ret r =>
    intro L d v y E h
    rename_i R
    cases R
    · exact h.1
    · exact h.1
  | let_ x k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, E2, h2, -⟩ := h <;> exact ih _ _ _ _ _ h2
  | loop Δ b init k ih =>
    intro L d v y E h
    rename_i R s
    cases R <;> simp only [Pg.GoodE] at h <;> obtain ⟨-, r, P, Eb, Ek, -, -, -, hr, hk, -⟩ := h <;>
      exact ⟨r, hr.runs, ih _ _ _ _ _ hk⟩

theorem Pg.den_det {Γ : List Sl} {R : Sl} (p : Pg Γ R) : ∀ (v : Vals Γ) (y y' : R.T), p.Den v y → p.Den v y' → y = y' := by
  induction p with
  | ret r => intro v y y' h h'; exact h.trans h'.symm
  | let_ x k ih => intro v y y' h h'; exact ih _ _ _ h h'
  | loop Δ b init k ih =>
    intro v y y' h h'
    obtain ⟨r, hr, hk⟩ := h
    obtain ⟨r', hr', hk'⟩ := h'
    obtain rfl := Runs.det' hr hr'
    exact ih _ _ _ hk hk'

/-! ## The compiler -/

/-- a paged program over the input bytes -/
structure PgProg where
  R : Sl
  p : Pg [.ar .ba] R
  /-- the inputs it accepts: up to `maxIn` bytes (a program whose arrays grow needs room below `P * P`) -/
  maxIn : Nat := 2 ^ 20
  /-- a register choice for the checked words `compBFC` (programs with `mop`); `none`: `compBFO` -/
  ch : Option (List (Nat × Nat) × List Nat) := none

/-- the bytes of a result: a scalar as 8 bytes little-endian, an array as its elements' bytes -/
def outEnc : (R : Sl) → R.T → List UInt8
  | .sc t, y => Res.enc (t.rep y)
  | .ar k, y => encArr k y

/-- the input bytes as a `ByteArray` -/
def inArr (input : List UInt8) : ByteArray := ⟨input.toArray⟩

theorem inArr_data (xs : ByteArray) : inArr xs.data.toList = xs := by simp [inArr]

/-- an array result reports its byte count in `a1` -/
def retOf : Sl → Bool
  | .sc _ => false
  | .ar _ => true

namespace PgProg
variable (q : PgProg)

/-- **the meaning**: the bytes of the Lean result (`Pg.Den`) -/
noncomputable def run (input : List UInt8) : Option (List UInt8) :=
  open Classical in
  if h : input.length ≤ q.maxIn ∧ ∃ y, q.p.Den (inArr input, ()) y then some (outEnc q.R (Classical.choose h.2))
  else none

/-- every input up to `maxIn` bytes has a run with page events -/
def Total : Prop := ∀ xs : ByteArray, xs.size ≤ q.maxIn → ∃ y E, q.p.GoodE [inLocP] 9 (xs, ()) y E

/-- the result and the page events of the run on an input (oldest first) -/
noncomputable def res (input : List UInt8) : q.R.T :=
  open Classical in
  if h : ∃ y E, q.p.GoodE [inLocP] 9 (inArr input, ()) y E then Classical.choose h else
    Classical.choice (by
      cases q with
      | mk R p m c =>
        cases R with
        | sc t => cases t <;> exact ⟨default⟩
        | ar k => cases k with
          | ba => exact ⟨default⟩
          | arr t => cases t <;> exact ⟨default⟩)

noncomputable def evs (input : List UInt8) : List MemEvent :=
  open Classical in
  if h : ∃ y E, q.p.GoodE [inLocP] 9 (inArr input, ()) y E then Classical.choose (Classical.choose_spec h) else []

/-- **the memory events** (newest first): the frame page, then the run's pages -/
noncomputable def events (input : List UInt8) : List MemEvent := (q.evs input).reverse ++ [.alloc 1]

/-- the paged code after the stub -/
def body : PgProg → List (BitVec 32)
  | ⟨.sc _, p, _, none⟩ => pgCodeS p (Res.k (BitVec 64))
  | ⟨.sc _, p, _, some (t, spl)⟩ => pgCodeSC p (Res.k (BitVec 64)) (waTbl t) spl
  | ⟨.ar _, p, _, none⟩ => pgCodeA p
  | ⟨.ar _, p, _, some (t, spl)⟩ => pgCodeAC p (waTbl t) spl

def code : List (BitVec 32) := pgStub ++ q.body

/-- the conditions the compiler checks -/
def Good : PgProg → Prop
  | ⟨.sc t, p, m, none⟩ => pgNS p (Res.k (BitVec 64)) ≤ NS ∧ p.wfP [inLocP] 9 = true ∧
      rvF.wfB (pgNS p (Res.k (BitVec 64))) [0, 3] [2] (pgProgS p (Res.k (BitVec 64))) ∧ Total ⟨.sc t, p, m, none⟩
  | ⟨.sc t, p, m, some (tb, spl)⟩ => pgNS p (Res.k (BitVec 64)) ≤ NS ∧ p.wfP [inLocP] 9 = true ∧
      (rvwF.optB scB (tblG (waTbl tb)) (fun j => spl.contains j) (pgNS p (Res.k (BitVec 64))) [0, 3] [2]
        (pgProgS p (Res.k (BitVec 64)))).isSome = true ∧ Total ⟨.sc t, p, m, some (tb, spl)⟩
  | ⟨.ar k, p, m, none⟩ => pgNA p ≤ NS ∧ ((p.compP [inLocP] 9).2.v < outBaseP p ∧ (p.compP [inLocP] 9).2.pt < outBaseP p) ∧
      p.wfP [inLocP] 9 = true ∧ rvF.wfB (pgNA p) [0, 3] [2] (pgProgA p) ∧ Total ⟨.ar k, p, m, none⟩
  | ⟨.ar k, p, m, some (tb, spl)⟩ => pgNA p ≤ NS ∧
      ((p.compP [inLocP] 9).2.v < outBaseP p ∧ (p.compP [inLocP] 9).2.pt < outBaseP p) ∧ p.wfP [inLocP] 9 = true ∧
      (rvwF.optB scB (tblG (waTbl tb)) (fun j => spl.contains j) (pgNA p) [0, 3] [2] (pgProgA p)).isSome = true ∧
      Total ⟨.ar k, p, m, some (tb, spl)⟩

theorem good_total {q : PgProg} (h : q.Good) : q.Total := by
  obtain ⟨R, p, m, c⟩ := q
  cases R <;> cases c <;> first | exact h.2.2.2 | exact h.2.2.2.2

theorem goodE_cast {R : Sl} {p : Pg [.ar .ba] R} {v v' : Vals [.ar .ba]} {y : R.T} {E : List MemEvent}
    (e : v = v') (h : p.GoodE [inLocP] 9 v y E) : p.GoodE [inLocP] 9 v' y E := e ▸ h

theorem res_spec {q : PgProg} (ht : q.Total) (xs : ByteArray) (hs : xs.size ≤ q.maxIn) :
    q.p.GoodE [inLocP] 9 (xs, ()) (q.res xs.data.toList) (q.evs xs.data.toList) := by
  have h : ∃ y E, q.p.GoodE [inLocP] 9 (inArr xs.data.toList, ()) y E := by rw [inArr_data]; exact ht xs hs
  unfold res evs
  rw [dif_pos h, dif_pos h]
  exact goodE_cast (by rw [inArr_data]) (Classical.choose_spec (Classical.choose_spec h))

theorem evs_allocs (input : List UInt8) : AllocsOnly (q.evs input) := by
  unfold evs
  split
  · next h => exact Pg.goodE_allocs _ _ _ _ _ _ (Classical.choose_spec (Classical.choose_spec h))
  · exact allocs_nil

end PgProg

noncomputable instance : Program PgProg := ⟨PgProg.run⟩

/-- **the compiler**: the stub, then the paged code; cells are pages of 8192 bytes -/
noncomputable def compile (q : PgProg) : Option CompiledA :=
  open Classical in if q.Good then some ⟨wordBytes q.code, 8192, q.events⟩ else none

theorem compile_inv {q : PgProg} {c : CompiledA} (h : compile q = some c) :
    q.Good ∧ c = ⟨wordBytes q.code, 8192, q.events⟩ := by
  unfold compile at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact nomatch h

/-- the run fits: `memoryNeeded` (of the input's bytes) at most the work length -/
def PgProg.fitsM (q : PgProg) (xs : ByteArray) (L : Nat) : Prop := 8192 * peak (q.events xs.data.toList) ≤ L

theorem PgProg.fitsM_iff (q : PgProg) (xs : ByteArray) (L : Nat) :
    q.fitsM xs L ↔ pk 0 (q.evs xs.data.toList) + 1 ≤ L / 8192 := by
  unfold PgProg.fitsM PgProg.events
  rw [peak_pages _ (q.evs_allocs _)]; omega

theorem _root_.Proven.Mach.Riscv.Implements1PgQ.congr {α β β' : Type} {encA : α → List UInt8} {encB : β → List UInt8}
    {encB' : β' → List UInt8} {code : List (BitVec 32)} {f : α → β} {f' : α → β'} {Lmin : Nat}
    {fits : α → Nat → Prop} {Q : α → Nat → BitVec 64 → Prop} {maxLen : Nat} {retLen : Bool}
    (h : Implements1PgQ encA encB code f Lmin fits Q maxLen retLen) (he : ∀ a, encB (f a) = encB' (f' a)) :
    Implements1PgQ encA encB' code f' Lmin fits Q maxLen retLen := by
  intro a
  have := h a
  rw [he a] at this
  exact this

/-- **the paged code after the stub** -/
theorem body_ok {q : PgProg} (hg : q.Good) :
    Implements1PgQ (fun xs : ByteArray => xs.data.toList) (outEnc q.R) q.body (fun xs => q.res xs.data.toList) 8192
      q.fitsM (okQ q.fitsM) q.maxIn (retOf q.R) := by
  have ht := PgProg.good_total hg
  obtain ⟨R, p, m, c⟩ := q
  cases R with
  | sc t =>
    cases c with
    | none =>
      obtain ⟨hN, hwf, hmwf, -⟩ := hg
      have := implements1_pgSQ (β := BitVec 64) (fun xs => t.rep (PgProg.res ⟨.sc t, p, m, none⟩ xs.data.toList)) p
        t.rep (fun _ => rfl) hN hwf hmwf (PgProg.fitsM ⟨.sc t, p, m, none⟩) m (fun xs hs =>
          ⟨_, _, PgProg.res_spec ht xs hs, rfl, fun L _ => PgProg.fitsM_iff _ xs L⟩)
      exact this.congr fun _ => rfl
    | some ch =>
      obtain ⟨tb, spl⟩ := ch
      obtain ⟨hN, hwf, hc, -⟩ := hg
      have := implements1_pgSQC (β := BitVec 64) (fun xs => t.rep (PgProg.res ⟨.sc t, p, m, some (tb, spl)⟩ xs.data.toList))
        p t.rep (fun _ => rfl) hN hwf (waTbl tb) spl hc (PgProg.fitsM ⟨.sc t, p, m, some (tb, spl)⟩) m (fun xs hs =>
          ⟨_, _, PgProg.res_spec ht xs hs, rfl, fun L _ => PgProg.fitsM_iff _ xs L⟩)
      exact this.congr fun _ => rfl
  | ar k =>
    cases c with
    | none =>
      obtain ⟨hN, hob, hwf, hmwf, -⟩ := hg
      exact implements1_pgAQ (fun xs => PgProg.res ⟨.ar k, p, m, none⟩ xs.data.toList) p hN hob hwf hmwf
        (PgProg.fitsM ⟨.ar k, p, m, none⟩) m (fun xs hs => ⟨_, PgProg.res_spec ht xs hs, fun L _ => PgProg.fitsM_iff _ xs L⟩)
    | some ch =>
      obtain ⟨tb, spl⟩ := ch
      obtain ⟨hN, hob, hwf, hc, -⟩ := hg
      exact implements1_pgAQC (fun xs => PgProg.res ⟨.ar k, p, m, some (tb, spl)⟩ xs.data.toList) p hN hob hwf
        (waTbl tb) spl hc (PgProg.fitsM ⟨.ar k, p, m, some (tb, spl)⟩) m
        (fun xs hs => ⟨_, PgProg.res_spec ht xs hs, fun L _ => PgProg.fitsM_iff _ xs L⟩)

theorem run_eq {q : PgProg} (hg : q.Good) {input out : List UInt8} (hrun : q.run input = some out) :
    input.length ≤ q.maxIn ∧ out = outEnc q.R (q.res (inArr input).data.toList) := by
  have ht := PgProg.good_total hg
  unfold PgProg.run at hrun
  split at hrun
  · next h =>
    have hsz : (inArr input).size ≤ q.maxIn := by simpa [inArr, ByteArray.size] using h.1
    have hden := Pg.goodE_den _ _ _ _ _ _ (PgProg.res_spec ht (inArr input) hsz)
    refine ⟨h.1, ?_⟩
    rw [← Option.some.inj hrun, Pg.den_det _ _ _ _ (Classical.choose_spec h.2) hden]
  · exact nomatch hrun

theorem inArr_toList (input : List UInt8) : (inArr input).data.toList = input := by simp [inArr]

/-- the machine run of a compiled program -/
theorem machine_run {q : PgProg} {compiled : CompiledA} {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State} {call : Call}
    (compiles : compile q = some compiled) (computes : Computes q f encodeInput encodeOutput)
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength) :
    ∃ finishState, Proven.Top.Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      (memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
        (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
        readMemory (riscv.observe finishState) call.outputAddress (encodeOutput (f argument)).length
          = some (encodeOutput (f argument))) ∧
      (¬ memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
        (riscv.observe finishState).register riscv.mapping.status = oomFlag) := by
  obtain ⟨hg, rfl⟩ := compile_inv compiles
  obtain ⟨hs, hout⟩ := run_eq hg (computes argument)
  have hsr : StartCorrect riscv startState call (wordBytes (pgStub ++ q.body))
      ((fun xs : ByteArray => xs.data.toList) (inArr (encodeInput argument))) := by
    show StartCorrect riscv startState call (wordBytes q.code) (inArr (encodeInput argument)).data.toList
    rw [inArr_toList]; exact startsRight
  have hof : (outEnc q.R (q.res (inArr (encodeInput argument)).data.toList)).length ≤ call.outputLength := by
    rw [← hout]; exact outputFits
  obtain ⟨fin, hruns, hpc, hframe, hfit, hnofit⟩ := stub_top (body_ok hg)
    (fun a L hL h => by rw [PgProg.fitsM_iff] at h; omega) (by rw [inArr_toList]; exact hs) hsr hof
  have hmn : memoryNeeded ⟨wordBytes q.code, 8192, q.events⟩ (encodeInput argument) =
      8192 * peak (q.events (inArr (encodeInput argument)).data.toList) := by
    rw [inArr_toList]; rfl
  refine ⟨fin, hruns, hpc, hframe, fun hle => ?_, fun hlt => ?_⟩
  · obtain ⟨h1, h2⟩ := hfit (by unfold PgProg.fitsM; rw [← hmn]; exact hle)
    rw [hout]; exact ⟨h1, h2⟩
  · exact hnofit (by unfold PgProg.fitsM; rw [← hmn]; exact hlt)

/-- **What happens** (`CompileRunsWeak`, `Compiler/AllocSpec.lean`) for the paged compiler: the code returns to the
caller, changes nothing outside the output and work blocks, and the status register (`a0`) holds `oomFlag` exactly
when the run's pages and the frame page (`memoryNeeded`) exceed the work block. -/
theorem compile_runs : CompileRunsWeak riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨fin, hruns, hpc, hframe, hfit, hnofit⟩ := machine_run compiles computes startsRight outputFits
  refine ⟨fin, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  by_cases h : memoryNeeded compiled (encodeInput argument) ≤ call.workLength
  · exact ⟨fun e => absurd e (hfit h).1, fun e => absurd h (Nat.not_le.2 e)⟩
  · exact ⟨fun _ => Nat.not_le.1 h, fun _ => hnofit h⟩

/-- **What comes out** (`CompileCorrectWeak`, `Compiler/AllocSpec.lean`) for the paged compiler: with
`memoryNeeded ≤ workLength` the code returns with the right output and no flag. -/
theorem compile_correct : CompileCorrectWeak riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨fin, hruns, hpc, -, hfit, -⟩ := machine_run compiles computes startsRight outputFits
  exact ⟨fin, hruns, hpc, (hfit enoughMemory).1, (hfit enoughMemory).2⟩

end Proven.WA

namespace Proven.WA
open Proven Proven.WP Proven.Top Proven.Top.Alloc Proven.Mach.Riscv

/-- **A Lean function with `GoodE` runs is what its paged program computes** (on the inputs it accepts) -/
theorem computes_of (q : PgProg) (f : ByteArray → q.R.T)
    (h : ∀ xs : ByteArray, xs.size ≤ q.maxIn → ∃ E, q.p.GoodE [inLocP] 9 (xs, ()) (f xs) E) :
    Computes q (fun a : {xs : ByteArray // xs.size ≤ q.maxIn} => f a.1) (fun a => a.1.data.toList)
      (outEnc q.R) := by
  intro a
  have hl : a.1.data.toList.length ≤ q.maxIn := by rw [Array.length_toList]; exact a.2
  obtain ⟨E, hE⟩ := h a.1 a.2
  have hden : q.p.Den (inArr a.1.data.toList, ()) (f a.1) := by
    rw [inArr_data]; exact Pg.goodE_den _ _ _ _ _ _ hE
  show PgProg.run q a.1.data.toList = _
  unfold PgProg.run
  rw [dif_pos ⟨hl, _, hden⟩, Pg.den_det _ _ _ _ (Classical.choose_spec (⟨_, hden⟩ : ∃ y, q.p.Den _ y)) hden]

theorem total_of (q : PgProg) (f : ByteArray → q.R.T)
    (h : ∀ xs : ByteArray, xs.size ≤ q.maxIn → ∃ E, q.p.GoodE [inLocP] 9 (xs, ()) (f xs) E) : q.Total :=
  fun xs hx => let ⟨E, hE⟩ := h xs hx; ⟨_, E, hE⟩

theorem compile_some {q : PgProg} (hg : q.Good) : compile q = some ⟨wordBytes q.code, 8192, q.events⟩ := by
  unfold compile; rw [if_pos hg]

end Proven.WA

/- Paged dynamic arrays (NOTES section 30), part 8: fresh arrays, programs.

A fresh array of a `let` or a loop start (`F`) is a new array of its own pages: `ByteArray.empty` is one page
(`newArr`), `Array.replicate n x` and `xs.extract lo hi` and a copy of a work array are a new array filled by
pushes (`fillLoopP`); a view of the input (`xs.data`, an alias of the input) is no array at all (`inp`).

A program's stages are guarded by `vOk`: once a push found no page, the rest is skipped.  At the end of a loop
with a scalar result the state's work array is freed (every page back to the pool). -/
import Riscv.Frontx.WpFill
import Riscv.Frontx.WaPg

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB rN_sub')

/-! ## A new array, filled -/

/-- `newArr`, `i := 0`, the fill loop -/
def newFill (ptv sv x i n t tA : Nat) (Sv : MS) : MS :=
  .seq (newArr ptv sv tA) (.seq (.assign i (.const 0)) (fillLoopP ptv sv x i n t Sv))

set_option maxHeartbeats 8000000 in
theorem newFill_ok (ptv sv x i n t tA : Nat) (Sv : MS) (C : Nat) (X : List (Nat × W64)) (f : Nat → BitVec 64)
    (N : Nat) (hN : N ≤ P * P)
    (hv : 8 ≤ ptv ∧ 8 ≤ sv ∧ 8 ≤ x ∧ 8 ≤ i ∧ 8 ≤ n ∧ ptv < t ∧ sv < t ∧ x < t ∧ i < t ∧ n < t ∧ sv ≠ ptv ∧ sv ≠ x ∧
      i ≠ ptv ∧ i ≠ sv ∧ i ≠ x ∧ n ≠ ptv ∧ n ≠ sv ∧ n ≠ x ∧ n ≠ i ∧ ptv ≠ x)
    (hA : 8 ≤ tA ∧ ptv ≠ tA ∧ ptv ≠ tA + 1 ∧ tA + 1 < t ∧ i ≠ tA ∧ i ≠ tA + 1 ∧ n ≠ tA ∧ n ≠ tA + 1 ∧ x ≠ tA ∧
      x ≠ tA + 1 ∧ sv ≠ tA ∧ sv ≠ tA + 1)
    (σ : MSt)
    (hSv : ∀ (pt : Nat) (σ1 : MSt) (W : W64) (xs : W64) (j : Nat), σ1.wheap = [W] → Store C σ1.env W ((pt, xs) :: X) →
      σ1.env i = rN j → j < N →
      (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ ptv → q ≠ tA → q ≠ tA + 1 → NP q → σ1.env q = σ.env q) →
      σ1.heap = σ.heap → ∃ σ', Mach.BExec Sv σ1 σ' ∧ σ'.env x = f j ∧
        (∀ q, q < t → q ≠ x → σ'.env q = σ1.env q) ∧ σ'.heap = σ1.heap ∧ σ'.wheap = σ1.wheap)
    (W : W64) (hW : σ.wheap = [W]) (hS : Store C σ.env W X) (hn : σ.env n = rN N) (hok : σ.env vOk = 1) :
    ∃ σ' W', Mach.BExec (newFill ptv sv x i n t tA Sv) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      (∀ q, q < t → q ≠ x → q ≠ sv → q ≠ i → q ≠ ptv → q ≠ tA → q ≠ tA + 1 → NP q → σ'.env q = σ.env q) ∧
      ((σ'.env vOk = 1 ∧ ∃ pt, σ'.env ptv = rN pt ∧ σ'.env sv = rN N ∧
          Store C σ'.env W' ((pt, (List.range N).map f) :: X) ∧
          finE (pageCount X) (.alloc 1 :: pushEvs N) = pageCount ((pt, (List.range N).map f) :: X) ∧
          pk (pageCount X) (.alloc 1 :: pushEvs N) ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount X) (.alloc 1 :: pushEvs N))) := by
  obtain ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩ := hv
  obtain ⟨hA8, hpa, hpa1, hat, hia, hia1, hna, hna1, hxa, hxa1, hsa, hsa1⟩ := hA
  obtain ⟨env0, H0, Ws⟩ := σ
  simp only at hW hS hn hok ⊢; subst hW
  have hW32 := hS.1.wlen.2
  obtain ⟨env1, e1, k1, r1⟩ := newArr_ok H0 hS ptv sv tA ⟨hp8, hA8, hs8⟩ ⟨hpa, hpa1⟩ hsp
  have hk1 : ∀ q, ¬ AllocVars ptv tA q → q ≠ sv → env1 q = env0 q := k1
  rcases r1 with ⟨hlt, ok1, sz1, p, hp1, S1⟩ | ⟨heq, ok1⟩
  · let env2 := env1.set i 0
    have e2 : Mach.BExec (.assign i (.const 0)) ⟨env1, H0, [W]⟩ ⟨env2, H0, [W]⟩ := .assign
    have hn2 : env2 n = rN N := by
      simp only [env2, set_ne hni]
      rw [hk1 n (by simp only [AllocVars, vFh, vBump, vOk]; omega) hns]; exact hn
    have S2 : Store C env2 W ((p, (List.range 0).map f) :: X) := by
      simpa using S1.env (env' := env2) fun q hq => by simp only [env2]; rw [set_ne (by have := pool_vars hq; omega)]
    obtain ⟨σ3, W3, e3, h3, w3, k3, r3⟩ := fillLoopP_ok ptv sv x i n t Sv C p X f N hN ⟨env2, H0, [W]⟩
      ⟨hp8, hs8, hx8, hi8, hn8, hpt, hst, hxt, hit, hnt, hsp, hsx, hip, his, hix, hnp, hns, hnx, hni, hpx⟩
      (fun σ1 W1 xs j a b c' d' fr hh => hSv p σ1 W1 xs j a b c' d' (fun q q1 q2 q3 q4 q5 q6 q7 q8 => by
        rw [fr q q1 q2 q3 q4 q8]; simp only [env2, set_ne q4]
        exact hk1 q (by obtain ⟨n1, n2, n3⟩ := q8; simp only [AllocVars]; omega) q3) hh)
      N 0 ⟨env2, H0, [W]⟩ W (by omega) (Nat.zero_le _) rfl (fun _ _ _ _ _ _ => rfl) rfl S2
      (by simp only [env2, set_ne (Ne.symm hip)]; exact hp1)
      (by simp only [env2, set_ne (Ne.symm his)]; exact sz1) (by simp only [env2, set_eq]; rfl) hn2
      (by simp only [env2, set_ne (show vOk ≠ i by simp only [vOk]; omega)]; rw [ok1]; exact hok)
    have hu : pageCount ((p, (List.range 0).map f) :: X) = pageCount X + 1 := by
      simp [pageCount_cons, npages, P]; omega
    refine ⟨σ3, W3, .seq e1 (.seq e2 e3), h3, w3, fun q a b c' d' e' g h' hq => ?_, ?_⟩
    · obtain ⟨n1, n2, n3⟩ := hq
      rw [k3 q a b c' d' n1 n2 n3]
      simp only [env2, set_ne d']
      exact hk1 q (by simp only [AllocVars]; omega) c'
    · rcases r3 with ⟨o3, sz3, S3, p3⟩ | ⟨o3, p3⟩
      · refine .inl ⟨o3, p, ?_, sz3, S3, ?_, ?_⟩
        · rw [k3 ptv hpt hpx (Ne.symm hsp) (Ne.symm hip) (pool_ne hp8).2.2.1 (pool_ne hp8).2.1
            (pool_ne hp8).2.2.2]
          simp only [env2, set_ne (Ne.symm hip)]; exact hp1
        · simp only [finE, stepE, pushEvs]; rw [finE_pushFrom]
          simp [pageCount_cons, npages, P]; omega
        · simp only [pk, stepE, pushEvs]; rw [← hu]
          exact Nat.max_le.2 ⟨Nat.le_trans (by omega) (Store.count_le S2), p3⟩
      · exact .inr ⟨o3, by simp only [pk, stepE, pushEvs]; rw [← hu]; exact Nat.lt_of_lt_of_le p3 (Nat.le_max_right _ _)⟩
  · have hc : (Mach.BExp.bin .and (.bin .ult (.var i) (.var n)) (.var vOk)).denote (env1.set i 0) = 0 := by
      simp only [Mach.BExp.denote, Op.eval, set_ne (show vOk ≠ i by simp only [vOk]; omega), ok1]; simp
    refine ⟨⟨env1.set i 0, H0, [W]⟩, W, .seq e1 (.seq .assign (.loopF hc)), rfl, rfl,
      fun q a b c' d' e' g h' hq => ?_, .inr ⟨by simp only [set_ne (show vOk ≠ i by simp only [vOk]; omega)]; exact ok1, ?_⟩⟩
    · obtain ⟨n1, n2, n3⟩ := hq
      simp only [set_ne d', Mach.BExp.denote]; exact hk1 q (by simp only [AllocVars]; omega) c'
    simp only [pk, stepE]
    rw [heq]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans (le_pk _ _) (Nat.le_max_right _ _))

/-! ## Fresh arrays -/

/-- the location of a fresh array in slot variables `d` (size) and `d + 1` (page table) -/
def F.locP (L : List PLoc) {Γ : List Sl} : {k : AK} → F Γ k → Nat → PLoc
  | _, .data m, d | _, .alias m, d => if (m.locP L).inp then ⟨d, true, 0⟩ else ⟨d, false, d + 1⟩
  | _, _, d => ⟨d, false, d + 1⟩

/-- copy the array at `l` into a new array (size into `d + 3`, fill from `d + 4`) -/
def copyCode (l : PLoc) (d : Nat) : MS :=
  .seq (.assign (d + 3) (.var l.v)) (newFill (d + 1) d (d + 7) (d + 6) (d + 3) (d + 8) (d + 4)
    (.seq (.assign (d + 7) (.var (d + 6))) (ldP l (d + 7))))

def F.compP (L : List PLoc) {Γ : List Sl} : {k : AK} → F Γ k → Nat → MS
  | _, .empty, d => newArr (d + 1) d (d + 2)
  | _, .rep n x, d =>
    .seq (E.compP L n (d + 2)) (.seq (E.compP L x (d + 3))
      (newFill (d + 1) d (d + 7) (d + 6) (d + 2) (d + 8) (d + 4) (.assign (d + 7) (.var (d + 3)))))
  | _, .extract m lo hi, d =>
    .seq (E.compP L lo (d + 2)) (.seq (E.compP L hi (d + 3))
      (.seq (.assign (d + 3) (.ite (.bin .ult (.var (d + 3)) (.var (m.locP L).v)) (.var (d + 3)) (.var (m.locP L).v)))
      (.seq (.assign (d + 3) (.ite (.bin .ult (.var (d + 2)) (.var (d + 3))) (.bin .sub (.var (d + 3)) (.var (d + 2)))
          (.const 0)))
        (newFill (d + 1) d (d + 7) (d + 6) (d + 3) (d + 8) (d + 4)
          (.seq (.assign (d + 7) (.bin .add (.var (d + 2)) (.var (d + 6)))) (ldP (m.locP L) (d + 7)))))))
  | _, .data m, d | _, .alias m, d =>
    if (m.locP L).inp then .assign d (.var (m.locP L).v) else copyCode (m.locP L) d
  | _, .const _, d => skipAt d

def F.wfP (L : List PLoc) {Γ : List Sl} : {k : AK} → F Γ k → Bool
  | _, .empty => true
  | _, .rep n x => E.wfP L n && E.wfP L x
  | _, .extract _ lo hi => E.wfP L lo && E.wfP L hi
  | _, .data _ | _, .alias _ => true
  | _, .const _ => false

def F.okP {Γ : List Sl} : {k : AK} → F Γ k → Vals Γ → Prop
  | _, .empty, _ => True
  | _, .rep n x, v => E.ok n v ∧ E.ok x v ∧ n.den v ≤ P * P
  | _, .extract m lo hi, v => E.ok lo v ∧ E.ok hi v ∧ lo.den v < 2 ^ 64 ∧ hi.den v < 2 ^ 64 ∧
      min (hi.den v) (m.get v).size - lo.den v ≤ P * P
  | _, .data _, _ | _, .alias _, _ => True
  | _, .const _, _ => True

/-- the page events of a fresh array -/
def F.evsP (L : List PLoc) {Γ : List Sl} : {k : AK} → F Γ k → Vals Γ → List MemEvent
  | _, .empty, _ => [.alloc 1]
  | _, .rep n _, v => .alloc 1 :: pushEvs (n.den v)
  | _, .extract m lo hi, v => .alloc 1 :: pushEvs (min (hi.den v) (m.get v).size - lo.den v)
  | _, .data m, v => if (m.locP L).inp then [] else .alloc 1 :: pushEvs (AK.size .ba (m.get v))
  | _, @F.alias _ k m, v => if (m.locP L).inp then [] else .alloc 1 :: pushEvs (AK.size k (m.get v))
  | _, .const _, _ => []

/-! ## Words of fresh arrays -/

theorem words_rep (t : Ty) (n : Nat) (x : t.T) :
    words (.arr t) (Array.replicate n x) = (List.range n).map fun _ => t.rep x := by
  apply List.ext_getElem?; intro j
  by_cases h : j < n
  · rw [words_get _ _ (by rw [AK.size_arr]; simpa using h)]
    simp only [List.getElem?_map, List.getElem?_range h, Option.map_some, AK.w, AK.el, AK.get_arr]
    rw [getElem!_pos (Array.replicate n x) j (by simpa using h)]; simp
  · rw [List.getElem?_eq_none (by rw [words_length, AK.size_arr]; simp; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem words_extract (xs : ByteArray) (lo hi : Nat) :
    words .ba (xs.extract lo hi) = (List.range (min hi xs.size - lo)).map fun j => AK.w .ba xs (lo + j) := by
  apply List.ext_getElem?; intro j
  have hs : AK.size .ba (xs.extract lo hi) = min hi xs.size - lo := ByteArray.size_extract
  by_cases h : j < min hi xs.size - lo
  · rw [words_get _ _ (by rw [hs]; exact h)]
    simp only [List.getElem?_map, List.getElem?_range h, Option.map_some, AK.w, AK.el, AK.get]
    have hj : j < (xs.extract lo hi).size := by rw [ByteArray.size_extract]; exact h
    have hj2 : lo + j < xs.size := by omega
    rw [getElem!_pos (xs.extract lo hi) j hj, getElem!_pos xs (lo + j) hj2, ByteArray.getElem_extract]
  · rw [List.getElem?_eq_none (by rw [words_length, hs]; omega), List.getElem?_eq_none (by simp; omega)]

theorem words_data (xs : ByteArray) : words (.arr .u8) xs.data = words .ba xs := by
  simp only [words, AK.size]
  congr 1; funext j; simp only [AK.w, AK.el, AK.get, ba_data_get]

theorem words_self (k : AK) (a : k.T) : words k a = (List.range (AK.size k a)).map (AK.w k a) := rfl

/-- the outcome of a fresh array -/
def FOut (C : Nat) (k : AK) (l : PLoc) (a : k.T) (X : List (Nat × W64)) (u : Nat) (E : List MemEvent) (σ' : MSt)
    (W' : W64) : Prop :=
  (σ'.env vOk = 1 ∧ SRP σ' (.ar k) l a ∧ Store C σ'.env W' (arrsP [.ar k] [l] (a, ()) σ'.env ++ X) ∧
      finE u E = pageCount (arrsP [.ar k] [l] (a, ()) σ'.env ++ X) ∧ pk u E ≤ C) ∨
    (σ'.env vOk = 0 ∧ C < pk u E)

/-- a work array filled by `newFill` is the fresh array -/
theorem fout_work {C : Nat} {k : AK} {a : k.T} {X : List (Nat × W64)} {E : List MemEvent} {σ' : MSt} {W' : W64}
    {d pt N : Nat} {f : Nat → BitVec 64} (hw : words k a = (List.range N).map f) (hN : AK.size k a = N)
    (hNP : N ≤ P * P) (ok : σ'.env vOk = 1) (h1 : σ'.env (d + 1) = rN pt) (h2 : σ'.env d = rN N)
    (hS : Store C σ'.env W' ((pt, (List.range N).map f) :: X))
    (hf : finE (pageCount X) E = pageCount ((pt, (List.range N).map f) :: X)) (hp : pk (pageCount X) E ≤ C) :
    FOut C k ⟨d, false, d + 1⟩ a X (pageCount X) E σ' W' := by
  have hpt : pt < 2 ^ 32 := by
    have := (hS.2 _ (List.mem_cons_self ..)).pt_in; have := hS.1.wlen.2; simp only at *; omega
  have harr : arrsP [.ar k] [⟨d, false, d + 1⟩] (a, ()) σ'.env = [(pt, (List.range N).map f)] := by
    simp only [arrsP, List.headD_cons, Bool.false_eq_true, if_false, h1]; rw [rN_toNat (by omega), hw]
  refine .inl ⟨ok, ⟨by rw [hN]; exact h2, by rw [P] at hNP; omega, fun h => absurd h Bool.false_ne_true, fun _ => by omega⟩, ?_, ?_, hp⟩
  · rw [harr]; exact hS
  · rw [harr]; exact hf

theorem pageCount_nil_cons (p : Nat) (X : List (Nat × W64)) : pageCount ((p, []) :: X) = pageCount X + 1 := by
  simp [pageCount_cons, npages, P]; omega

theorem newArr_fout {C : Nat} {k : AK} {a : k.T} {X : List (Nat × W64)} {env : Mach.BEnv} {H : Heap} {W : W64}
    {d : Nat} (hd : 8 ≤ d) (ha : words k a = []) (hs : AK.size k a = 0) (hS : Store C env W X) (hok : env vOk = 1) :
    ∃ σ' W', Mach.BExec (newArr (d + 1) d (d + 2)) ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧
      (∀ j, j < d → NP j → σ'.env j = env j) ∧ FOut C k ⟨d, false, d + 1⟩ a X (pageCount X) [.alloc 1] σ' W' := by
  obtain ⟨env1, e1, k1, r1⟩ := newArr_ok H hS (d + 1) d (d + 2) ⟨by omega, by omega, hd⟩ ⟨by omega, by omega⟩
    (by omega)
  have hk : ∀ j, j < d → NP j → env1 j = env j := fun j hj hn => k1 j (by
    obtain ⟨n1, n2, n3⟩ := hn; simp only [AllocVars]; omega) (by omega)
  refine ⟨⟨env1, H, [W]⟩, W, e1, rfl, rfl, hk, ?_⟩
  rcases r1 with ⟨hlt, ok1, sz1, p, hp1, S1⟩ | ⟨heq, ok1⟩
  · have hu := pageCount_nil_cons p X
    refine fout_work (N := 0) (f := fun _ => 0) (by rw [ha]; rfl) hs (by decide) (by show env1 vOk = 1; rw [ok1]; exact hok)
      hp1 (by show env1 d = _; rw [sz1]; rfl) (by simpa using S1) (by simp only [finE, stepE]; simp [hu]) ?_
    simp only [pk, stepE]; omega
  · exact .inr ⟨ok1, by simp only [pk, stepE]; omega⟩

set_option maxHeartbeats 4000000 in
/-- `newFill` into slot variables `d`, `d + 1` (count in `nv`, value in `d + 7`, index `d + 6`, scratch from
`d + 8`) gives the fresh array -/
theorem newFill_fout {C : Nat} {k : AK} {a : k.T} {X : List (Nat × W64)} (σ : MSt) {W : W64} {d nv : Nat}
    (Sv : MS) (f : Nat → BitVec 64) (N : Nat) (hd : 8 ≤ d) (hnv : nv = d + 2 ∨ nv = d + 3)
    (hw : words k a = (List.range N).map f) (hs : AK.size k a = N) (hNP : N ≤ P * P)
    (hW : σ.wheap = [W]) (hS : Store C σ.env W X) (hn : σ.env nv = rN N) (hok : σ.env vOk = 1)
    (hSv : ∀ (pt : Nat) (σ1 : MSt) (W1 : W64) (xs : W64) (j : Nat), σ1.wheap = [W1] →
      Store C σ1.env W1 ((pt, xs) :: X) → σ1.env (d + 6) = rN j → j < N →
      (∀ q, q < d + 8 → q ≠ d + 7 → q ≠ d → q ≠ d + 6 → q ≠ d + 1 → q ≠ d + 4 → q ≠ d + 5 → NP q →
        σ1.env q = σ.env q) →
      σ1.heap = σ.heap → ∃ σ', Mach.BExec Sv σ1 σ' ∧ σ'.env (d + 7) = f j ∧
        (∀ q, q < d + 8 → q ≠ d + 7 → σ'.env q = σ1.env q) ∧ σ'.heap = σ1.heap ∧ σ'.wheap = σ1.wheap) :
    ∃ σ' W', Mach.BExec (newFill (d + 1) d (d + 7) (d + 6) nv (d + 8) (d + 4) Sv) σ σ' ∧ σ'.heap = σ.heap ∧
      σ'.wheap = [W'] ∧ (∀ j, j < d → NP j → σ'.env j = σ.env j) ∧
      FOut C k ⟨d, false, d + 1⟩ a X (pageCount X) (.alloc 1 :: pushEvs N) σ' W' := by
  obtain ⟨σ', W', e, h, w, k', r⟩ := newFill_ok (d + 1) d (d + 7) (d + 6) nv (d + 8) (d + 4) Sv C X f N hNP
    (by omega) (by omega) σ hSv W hW hS hn hok
  refine ⟨σ', W', e, h, w, fun j hj hn' => k' j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hn', ?_⟩
  rcases r with ⟨o, pt, h1, h2, S, fe, pe⟩ | ⟨o, pe⟩
  · exact fout_work hw hs hNP o h1 h2 S fe pe
  · exact .inr ⟨o, pe⟩

/-- the value code of a copy or `extract`: `x := a[lo + i]` (`lo` in `lv`, or `0`) is a load of the source -/
theorem srcLoad_ok {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {k : AK} (m : Mem Γ (.ar k)) {C : Nat}
    {X : List (Nat × W64)} {env : Mach.BEnv} {H : Heap} {W : W64} {d : Nat} (hd : 8 ≤ d)
    (hE : EnvOK Γ L v ⟨env, H, [W]⟩) (hb : BelowP L d) (hLnp : ∀ l ∈ L, NP l.v ∧ NP l.pt)
    (σ0 : MSt) (h0 : ∀ j, j < d → NP j → σ0.env j = env j) (hh0 : σ0.heap = H)
    (pt : Nat) (σ1 : MSt) (W1 : W64) (xs : W64) (j lo : Nat) (hW1 : σ1.wheap = [W1])
    (hS1 : Store C σ1.env W1 ((pt, xs) :: X ++ arrsP Γ L v env))
    (fr : ∀ q, q < d + 8 → q ≠ d + 7 → q ≠ d → q ≠ d + 6 → q ≠ d + 1 → q ≠ d + 4 → q ≠ d + 5 → NP q →
      σ1.env q = σ0.env q) (hh : σ1.heap = σ0.heap)
    (lx : MB) (hlx : lx.denote σ1.env = rN (lo + j)) (hlj : lo + j < AK.size k (m.get v)) :
    ∃ σ', Mach.BExec (.seq (.assign (d + 7) lx) (ldP (m.locP L) (d + 7))) σ1 σ' ∧ σ'.env (d + 7) = AK.w k (m.get v) (lo + j) ∧
      (∀ q, q < d + 8 → q ≠ d + 7 → σ'.env q = σ1.env q) ∧ σ'.heap = σ1.heap ∧ σ'.wheap = σ1.wheap := by
  let σa : MSt := ⟨σ1.env.set (d + 7) (lx.denote σ1.env), σ1.heap, σ1.wheap⟩
  have hfr : ∀ q, q < d → NP q → σa.env q = env q := fun q hq hn => by
    simp only [σa, set_ne (show q ≠ d + 7 by omega)]
    rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hn, h0 _ hq hn]
  have hslot : ∀ l ∈ L, σa.env l.v = env l.v ∧ σa.env l.pt = env l.pt := fun l hl =>
    ⟨hfr _ (hb l hl).1 (hLnp l hl).1, hfr _ (hb l hl).2 (hLnp l hl).2⟩
  have hEa : EnvOK Γ L v σa := by
    refine ⟨hE.rel.frame (fun l hl => (hslot l hl).1) (by simp [σa, hh, hh0]) hE.len, hE.len, W1,
      by simp [σa, hW1], hS1.1.wlen.2, ?_⟩
    unfold AllAt; rw [arrsP_congr (fun l hl => (hslot l hl).2) hE.len]
    intro a ha; exact hS1.2 a (by simp [ha])
  obtain ⟨σb, eb, vb, kb, hb', wb⟩ := ldP_ok hEa m (d + 7) (hb.mono (by omega)) (lo + j)
    (by simp only [σa, set_eq, hlx]) hlj
  refine ⟨σb, .seq .assign eb, vb, fun q hq hx => ?_, by rw [hb'], by rw [wb]⟩
  rw [kb q hx (by omega)]; simp only [σa, set_ne hx]

theorem lt_rN_ite {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if (if rN a < rN b then (1 : BitVec 64) else 0) = 0 then rN b else rN a) = rN (min a b) := by
  simp only [rN_lt ha hb]
  by_cases h : a < b
  · rw [if_pos h, if_neg (by decide), Nat.min_eq_left (by omega)]
  · rw [if_neg h, if_pos rfl, Nat.min_eq_right (by omega)]

theorem sub_rN_ite {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if (if rN a < rN b then (1 : BitVec 64) else 0) = 0 then 0 else rN b - rN a) = rN (b - a) := by
  simp only [rN_lt ha hb]
  by_cases h : a < b
  · rw [if_pos h, if_neg (by decide), rN_sub' hb ha, if_neg (by omega)]
  · rw [if_neg h, if_pos rfl, Nat.sub_eq_zero_of_le (by omega)]; rfl

set_option maxHeartbeats 4000000 in
/-- a view or copy of the array `m`, as an array `a` of kind `k` with the same elements -/
theorem copy_fout {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {k0 k : AK} (m : Mem Γ (.ar k0)) (a : k.T) {C : Nat}
    {X : List (Nat × W64)} {env : Mach.BEnv} {H : Heap} {W : W64} {d : Nat} (hd : 8 ≤ d)
    (hE : EnvOK Γ L v ⟨env, H, [W]⟩) (hb : BelowP L d) (hLnp : ∀ l ∈ L, NP l.v ∧ NP l.pt)
    (hS : Store C env W (X ++ arrsP Γ L v env)) (hok1 : env vOk = 1)
    (hs : AK.size k a = AK.size k0 (m.get v)) (hw : ∀ j, AK.w k a j = AK.w k0 (m.get v) j) :
    ∃ σ' W', Mach.BExec (if (m.locP L).inp then .assign d (.var (m.locP L).v) else copyCode (m.locP L) d)
        ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧ (∀ j, j < d → NP j → σ'.env j = env j) ∧
      FOut C k (if (m.locP L).inp then ⟨d, true, 0⟩ else ⟨d, false, d + 1⟩) a (X ++ arrsP Γ L v env)
        (pageCount (X ++ arrsP Γ L v env))
        (if (m.locP L).inp then [] else .alloc 1 :: pushEvs (AK.size k0 (m.get v))) σ' W' := by
  have hmL := Mem.locP_mem m L hE.len
  have hlv := (hb _ hmL).1
  obtain ⟨hmv, hm32, hinp, hwk⟩ := hE.rel.get m
  simp only at hmv hinp
  have hws : words k a = (List.range (AK.size k0 (m.get v))).map (AK.w k0 (m.get v)) := by
    rw [words_self, hs]; congr 1; funext j; exact hw j
  by_cases hi : (m.locP L).inp = true
  · simp only [hi, if_true]
    refine ⟨⟨env.set d (env (m.locP L).v), H, [W]⟩, W, .assign, rfl, rfl, fun j hj _ => set_ne (by omega), .inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [set_ne (show vOk ≠ d by simp only [vOk]; omega)]; exact hok1
    · refine ⟨by simp only [set_eq]; rw [hmv, hs], by rw [hs]; exact hm32, fun _ => ?_, fun h => by simp at h⟩
      obtain ⟨h1, h2⟩ := hinp hi
      exact ⟨by rw [hs]; exact h1, fun j hj => by rw [hw]; exact h2 j (by rw [← hs]; exact hj)⟩
    · simp only [arrsP, List.headD_cons, if_true, List.nil_append]
      exact hS.env fun j hj => set_ne (by have := pool_vars hj; omega)
    · simp [arrsP, finE]
    · exact hS.count_le
  · have hf : (m.locP L).inp = false := by simpa using hi
    simp only [hf, Bool.false_eq_true, if_false]
    have hN := hwk hf
    let σ2 : MSt := ⟨env.set (d + 3) (env (m.locP L).v), H, [W]⟩
    have hS2 : Store C σ2.env W (X ++ arrsP Γ L v env) := hS.env fun j hj => set_ne (by have := pool_vars hj; omega)
    obtain ⟨σ', W', e, h, w, k', r⟩ := newFill_fout (k := k) (a := a) σ2
      (.seq (.assign (d + 7) (.var (d + 6))) (ldP (m.locP L) (d + 7))) (AK.w k0 (m.get v)) (AK.size k0 (m.get v)) hd
      (.inr rfl) hws hs hN rfl hS2 (by simp only [σ2, set_eq]; exact hmv)
      (by simp only [σ2, set_ne (show vOk ≠ d + 3 by simp only [vOk]; omega)]; exact hok1)
      (fun pt σa Wa xs j a1 b c' d' fr hh => by
        have := srcLoad_ok m hd hE hb hLnp σ2 (fun j hj _ => set_ne (by omega)) rfl pt σa Wa xs j 0 a1 b fr hh
          (.var (d + 6)) (by simp only [Mach.BExp.denote, Nat.zero_add]; exact c') (by omega)
        simpa using this)
    exact ⟨σ', W', .seq .assign e, h, w, fun j hj hn => by rw [k' j hj hn]; exact set_ne (by omega), r⟩

set_option maxHeartbeats 8000000 in
/-- **Fresh arrays**: a new array of its own pages (or a view of the input), or a push found no page -/
theorem F.compP_ok (L : List PLoc) {Γ : List Sl} (C : Nat) : ∀ {k : AK} (f : F Γ k) (v : Vals Γ) (env : Mach.BEnv)
    (H : Heap) (W : W64) (d : Nat) (X : List (Nat × W64)), EnvOK Γ L v ⟨env, H, [W]⟩ → BelowP L d → 8 ≤ d →
    (∀ l ∈ L, NP l.v ∧ NP l.pt) → Store C env W (X ++ arrsP Γ L v env) → env vOk = 1 → f.wfP L = true →
    f.okP v →
    ∃ σ' W', Mach.BExec (F.compP L f d) ⟨env, H, [W]⟩ σ' ∧ σ'.heap = H ∧ σ'.wheap = [W'] ∧
      (∀ j, j < d → NP j → σ'.env j = env j) ∧
      FOut C k (F.locP L f d) (F.den f v) (X ++ arrsP Γ L v env) (pageCount (X ++ arrsP Γ L v env)) (F.evsP L f v) σ' W'
  | _, .empty, v, env, H, W, d, X, hE, hb, hd, hLnp, hS, hok1, hwf, hok => by
    simp only [F.compP, F.locP, F.evsP, F.den]
    exact newArr_fout hd rfl rfl hS hok1
  | _, @F.rep _ t n x, v, env, H, W, d, X, hE, hb, hd, hLnp, hS, hok1, hwf, hok => by
    simp only [F.wfP, Bool.and_eq_true] at hwf; simp only [F.okP] at hok
    obtain ⟨hon, hox, hnP⟩ := hok
    simp only [F.compP, F.locP, F.evsP]
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L n v ⟨env, H, [W]⟩ (d + 2) hE hE.len (hb.mono (by omega))
      hwf.1 hon).frameP hE (hb.mono (by omega)) hE.len
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.compP_ok L x v σ1 (d + 3) r1 hE.len (hb.mono (by omega)) hwf.2
      hox).frameP r1 (hb.mono (by omega)) hE.len
    have hk2 : ∀ j, j < d + 2 → σ2.env j = env j := fun j hj => by rw [k2 j (by omega), k1 j hj]
    have hS2 : Store C σ2.env W (X ++ arrsP Γ L v env) := hS.env fun j hj => hk2 j (by have := pool_vars hj; omega)
    have hW2 : σ2.wheap = [W] := by rw [w2, w1]
    have hn2 : σ2.env (d + 2) = rN (n.den v) := by rw [k2 _ (by omega)]; exact v1
    obtain ⟨σ', W', e3, h3, w3, k3, r3⟩ := newFill_fout (k := .arr t) (a := Array.replicate (n.den v) (x.den v))
      σ2 (.assign (d + 7) (.var (d + 3))) (fun _ => t.rep (x.den v)) (n.den v) hd (.inl rfl) (words_rep _ _ _)
      (by rw [AK.size_arr]; simp) hnP hW2 hS2 hn2 (by rw [hk2 _ (by simp only [vOk]; omega)]; exact hok1)
      (fun pt σa Wa xs j a b c' d' fr hh => ⟨_, .assign, by
        simp only [set_eq, Mach.BExp.denote]
        rw [fr (d + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by simp only [NP, vFh, vBump, vOk]; omega)]; exact v2, fun q hq hx => set_ne hx, rfl, rfl⟩)
    refine ⟨σ', W', .seq e1 (.seq e2 e3), by rw [h3, h2, h1], w3, fun j hj hn => by rw [k3 j hj hn, hk2 j (by omega)],
      ?_⟩
    rw [F.den_rep]; exact r3
  | _, .extract m lo hi, v, env, H, W, d, X, hE, hb, hd, hLnp, hS, hok1, hwf, hok => by
    simp only [F.wfP, Bool.and_eq_true] at hwf; simp only [F.okP] at hok
    obtain ⟨hol, hoh, hl64, hh64, hNP⟩ := hok
    simp only [F.compP, F.locP, F.evsP, F.den]
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L lo v ⟨env, H, [W]⟩ (d + 2) hE hE.len (hb.mono (by omega))
      hwf.1 hol).frameP hE (hb.mono (by omega)) hE.len
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.compP_ok L hi v σ1 (d + 3) r1 hE.len (hb.mono (by omega)) hwf.2
      hoh).frameP r1 (hb.mono (by omega)) hE.len
    have hk2 : ∀ j, j < d + 2 → σ2.env j = env j := fun j hj => by rw [k2 j (by omega), k1 j hj]
    have hS0 := hE.rel.get m
    obtain ⟨hmv, hm32, -, -⟩ := hS0
    have hmL := Mem.locP_mem m L hE.len
    have hmv2 : σ2.env (m.locP L).v = rN (m.get v).size := by rw [hk2 _ (by have := (hb _ hmL).1; omega)]; exact hmv
    have hlo2 : σ2.env (d + 2) = rN (lo.den v) := by rw [k2 _ (by omega)]; exact v1
    let σ3 : MSt := ⟨σ2.env.set (d + 3) (rN (min (hi.den v) (m.get v).size)), σ2.heap, σ2.wheap⟩
    have e3 : Mach.BExec (.assign (d + 3) (.ite (.bin .ult (.var (d + 3)) (.var (m.locP L).v)) (.var (d + 3))
        (.var (m.locP L).v))) σ2 σ3 := by
      have := Mach.BExec.assign (v := d + 3) (e := .ite (.bin .ult (.var (d + 3)) (.var (m.locP L).v)) (.var (d + 3))
        (.var (m.locP L).v)) (σ := σ2)
      simp only [Mach.BExp.denote, Op.eval, v2, hmv2, Ty.rep] at this
      rw [lt_rN_ite hh64 (show (m.get v).size < 2 ^ 64 from Nat.lt_trans (show AK.size .ba (m.get v) < 2 ^ 32 from hm32) (by decide))] at this; exact this
    let N := min (hi.den v) (m.get v).size - lo.den v
    let σ4 : MSt := ⟨σ3.env.set (d + 3) (rN N), σ3.heap, σ3.wheap⟩
    have e4 : Mach.BExec (.assign (d + 3) (.ite (.bin .ult (.var (d + 2)) (.var (d + 3)))
        (.bin .sub (.var (d + 3)) (.var (d + 2))) (.const 0))) σ3 σ4 := by
      have := Mach.BExec.assign (v := d + 3) (e := .ite (.bin .ult (.var (d + 2)) (.var (d + 3)))
        (.bin .sub (.var (d + 3)) (.var (d + 2))) (.const 0)) (σ := σ3)
      simp only [Mach.BExp.denote, Op.eval, σ3, set_eq, set_ne (show d + 2 ≠ d + 3 by omega), hlo2] at this
      rw [sub_rN_ite hl64 (Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hh64)] at this; exact this
    have hk4 : ∀ j, j < d + 2 → σ4.env j = env j := fun j hj => by
      simp only [σ4, σ3, set_ne (show j ≠ d + 3 by omega)]; exact hk2 j hj
    have hS4 : Store C σ4.env W (X ++ arrsP Γ L v env) := hS.env fun j hj => hk4 j (by have := pool_vars hj; omega)
    have hW4 : σ4.wheap = [W] := by simp only [σ4, σ3]; rw [w2, w1]
    obtain ⟨σ', W', e5, h5, w5, k5, r5⟩ := newFill_fout (k := .ba) (a := (m.get v).extract (lo.den v) (hi.den v))
      σ4 (.seq (.assign (d + 7) (.bin .add (.var (d + 2)) (.var (d + 6)))) (ldP (m.locP L) (d + 7)))
      (fun j => AK.w .ba (m.get v) (lo.den v + j)) N hd (.inr rfl) (words_extract _ _ _)
      (ByteArray.size_extract) hNP hW4 hS4 (by simp only [σ4, set_eq]) (by rw [hk4 _ (by simp only [vOk]; omega)]; exact hok1)
      (fun pt σa Wa xs j a b c' d' fr hh => by
        refine srcLoad_ok m hd hE hb hLnp σ4 (fun j hj _ => hk4 j (by omega)) (by simp [σ4, σ3, h2, h1]) pt σa Wa xs j
          (lo.den v) a b fr hh _ ?_ (by simp only [AK.size]; omega)
        simp only [Mach.BExp.denote, Op.eval, c']
        rw [fr (d + 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by simp only [NP, vFh, vBump, vOk]; omega), show σ4.env (d + 2) = rN (lo.den v) from by
            simp only [σ4, σ3, set_ne (show d + 2 ≠ d + 3 by omega)]; exact hlo2, rN_add])
    refine ⟨σ', W', .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))), by rw [h5]; simp [σ4, σ3, h2, h1], w5,
      fun j hj hn => by rw [k5 j hj hn, hk4 j (by omega)], r5⟩
  | _, .data m, v, env, H, W, d, X, hE, hb, hd, hLnp, hS, hok1, hwf, hok => by
    simp only [F.compP, F.locP, F.evsP, F.den]
    exact copy_fout m _ hd hE hb hLnp hS hok1 rfl (fun j => by simp only [AK.w, AK.el, AK.get, ba_data_get])
  | _, .alias m, v, env, H, W, d, X, hE, hb, hd, hLnp, hS, hok1, hwf, hok => by
    simp only [F.compP, F.locP, F.evsP, F.den]
    exact copy_fout m _ hd hE hb hLnp hS hok1 rfl (fun _ => rfl)
  | _, .const _, _, _, _, _, _, _, _, _, _, _, _, _, hwf, _ => by simp [F.wfP] at hwf

end Proven.WA
